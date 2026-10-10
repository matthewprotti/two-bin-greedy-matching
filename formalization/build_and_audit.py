#!/usr/bin/env python3
"""Compile and audit the full matching classification and all regime statements.
The receipt must be new and outside this repository. Run after `lake update` and
`lake exe cache get`. No external services or credentials are used by this script.
"""
from pathlib import Path
import argparse
import hashlib
import json
import platform
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
BANNED = r'\b(sorry|admit|axiom|native_decide|sorryAx|ofReduceBool)\b|decide\s*\+native|Lean\.trustCompiler|debug\.skipKernelTC'


def uncomment(text):
    """Strip Lean line comments and nested block comments, retaining newlines."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif not depth and text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise ValueError('Unclosed Lean comment')
    return ''.join(out)


def source_hashes():
    paths = list(ROOT.glob('*.lean')) + list((ROOT/'TwoBin').glob('*.lean')) + list((ROOT/'negative').glob('*.lean'))
    paths += [ROOT/'lean-toolchain', ROOT/'lakefile.toml', ROOT/'lake-manifest.json', ROOT/'MODEL_LOCK.json', Path(__file__)]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths) if p.is_file()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', required=True, type=Path)
    out = parser.parse_args().receipt.resolve()
    if out.exists() or out.is_relative_to(ROOT.parent):
        raise SystemExit('Receipt must be a new path outside the repository.')
    record = {'schema': 'two-bin-lean-build.v4', 'source_sha256': source_hashes(),
              'full_classification': 'NOT_YET_AUDITED',
              'paired_sufficiency': 'NOT_YET_AUDITED',
              'source_statement_independent_audit': 'NOT_RUN',
              'platform': platform.platform(), 'steps': []}

    def run(cmd, expect_failure=False):
        start = time.monotonic()
        result = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        record['steps'].append({'command': cmd, 'returncode': result.returncode,
                                'output': result.stdout, 'seconds': round(time.monotonic()-start, 3)})
        if (result.returncode == 0) == expect_failure:
            raise RuntimeError('Unexpected command result: ' + ' '.join(cmd))
        return result.stdout

    try:
        if not shutil.which('lake'):
            raise RuntimeError('lake is not installed or on PATH')
        if not (ROOT/'lake-manifest.json').is_file():
            raise RuntimeError('Missing pinned dependency manifest; run lake update first')
        for p in sorted((ROOT/'TwoBin').glob('*.lean')) + sorted(ROOT.glob('*.lean')):
            if re.search(BANNED, uncomment(p.read_text())):
                raise RuntimeError('Forbidden proof/trust construct in ' + p.name)
        lock = json.loads((ROOT/'MODEL_LOCK.json').read_text())
        if set(lock['files']) != {'TwoBin/Definitions.lean', 'TwoBin/SourceModel.lean'}:
            raise RuntimeError('Model lock must cover both original definition files')
        for name, expected in lock['files'].items():
            if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != expected:
                raise RuntimeError('Original model changed: '+name)
        record['model_lock'] = lock
        declarations = []
        for p in sorted((ROOT/'TwoBin').glob('*.lean')) + sorted(ROOT.glob('*.lean')):
            code = uncomment(p.read_text())
            names = re.findall(r'\b(?:theorem|lemma)\s+(\w+)', code)
            namespaces = re.findall(r'^namespace\s+(\w+)', code, re.M)
            if names and len(namespaces) != 1:
                raise RuntimeError('Expected one explicit namespace in theorem source '+p.name)
            if names:
                declarations.extend(namespaces[0]+'.'+name for name in names)
        audited = re.findall(r'#print axioms\s+(\S+)', (ROOT/'AxiomAudit.lean').read_text())
        if len(audited) != len(set(audited)) or set(declarations) != set(audited):
            raise RuntimeError('AxiomAudit must cover every named theorem exactly once')
        record['audited_theorems'] = audited
        run(['lake', 'env', 'lean', '--version'])
        run(['lake', 'build'])
        # Re-elaborate every project module with kernel trust level zero.
        for path in sorted((ROOT/'TwoBin').glob('*.lean')):
            run(['lake', 'env', 'lean', '--trust=0', str(path.relative_to(ROOT))])
        run(['lake', 'env', 'lean', '--trust=0', 'ChallengeStatement.lean'])
        run(['lake', 'env', 'lean', '--trust=0', 'AlgebraicChallenge.lean'])
        run(['lake', 'env', 'lean', '--trust=0', 'FullChallengeStatement.lean'])
        run(['lake', 'env', 'lean', '--trust=0', 'FullChallenge.lean'])
        output = run(['lake', 'env', 'lean', '--trust=0', 'AxiomAudit.lean'])
        dependencies = {}
        for name in audited:
            match = re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]", output, re.S)
            if match:
                names = {x.strip() for x in match.group(1).split(',') if x.strip()}
            elif re.search(r"'"+re.escape(name)+r"' does not depend on any axioms", output):
                names = set()
            else:
                raise RuntimeError('Missing actual axiom report for '+name)
            if not names <= ALLOWED:
                raise RuntimeError('Unapproved axiom dependencies for '+name+': '+repr(names-ALLOWED))
            dependencies[name] = sorted(names)
        record['axioms'] = dependencies
        # Positive counterparts establish the imports, notation and evaluation path.
        run(['lake', 'env', 'lean', '--trust=0', 'PositiveControls.lean'])
        controls = {}
        for name, expected in [('FalseNumeric', 'decide'), ('FalseQuadratic', 'unsolved goals'), ('FalseRankingNumerator', 'decide'), ('FalsePairedBound', 'unsolved goals'), ('FalseFixedDominance', 'unsolved goals'), ('FalseRandomDominance', 'unsolved goals'), ('FalseEquality', 'unsolved goals')]:
            output = run(['lake', 'env', 'lean', '--trust=0', f'negative/{name}.lean'], expect_failure=True)
            if f'negative/{name}.lean:3:' not in output or expected not in output:
                raise RuntimeError('Negative control did not fail at its intended false claim: '+name)
            if re.search(r'unknown module|unknown namespace|unknown identifier|failed to synthesize|object file .* does not exist|invalid import', output, re.I):
                raise RuntimeError('Negative control failed due to setup rather than its claim: '+name)
            controls[name] = 'REJECTED_AT_FALSE_CLAIM'
        record['negative_controls'] = controls
        if record['source_sha256'] != source_hashes():
            raise RuntimeError('Source or dependency manifest changed during audit')
        record['paired_sufficiency'] = 'PROVED_AND_AXIOMS_AUDITED'
        record['paired_classification'] = 'TwoBin.paired_classification'
        record['binomial_corollary'] = 'TwoBin.paired_binomial_shift'
        record['formula_comparison'] = 'TwoBin.survivalFormula_dominance'
        record['full_probabilistic_bridges'] = 'PROVED_FROM_ORIGINAL_SOURCE_COUNTS'
        record['full_classification'] = 'PROVED: TwoBin.full_classification'
        record['four_regimes'] = 'PROVED: TwoBin.four_regimes'
        record['fixed_witness_identity'] = 'TwoBin.fixedWitness_closed_formula'
        record['uniform_witness_identity'] = 'TwoBin.uniformWitness_closed_formula'
        record['literal_statement_challenge'] = 'PASS; independently authored audit still not performed'
        record['status'] = 'FULL_CLASSIFICATION_AND_REGIMES_COMPILED_AND_AXIOMS_AUDITED'
    except Exception as exc:
        record.update(status='FAILED', reason=str(exc))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(record, indent=2)+'\n')
    print(record['status'])
    if 'reason' in record:
        print(record['reason'])
    return 0 if record['status'] == 'FULL_CLASSIFICATION_AND_REGIMES_COMPILED_AND_AXIOMS_AUDITED' else 1


if __name__ == '__main__':
    raise SystemExit(main())
