#!/usr/bin/env python3
"""Compare actual Lean source counts to the separate historical Python oracle.
Finite execution evidence only: this is not a universal source-to-proof bridge.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.util
from itertools import permutations
import json
from pathlib import Path
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PIN = '97b6885c2f40a71101b58e2245d18f96335875306c3df8447754e52e5f0618d3'
DRIVER = '''import TwoBin

def decodeWord : Nat → Nat → List TwoBin.Degree
  | 0, _ => []
  | n+1, code => (match code % 3 with
      | 0 => .zero
      | 1 => .singleton
      | _ => .flexible) :: decodeWord n (code / 3)

def main : IO Unit := do
  for a in [1:4] do
    for b in [1:5] do
      for n in [0:5] do
        for code in [0:3^n] do
          let word := decodeWord n code
          let positive := (word.filter (fun d => decide (d ≠ .zero))).length
          let singles := (word.filter (fun d => decide (d = .singleton))).length
          let svrv := TwoBin.sourceSurvivalCount a b false false word
          let svrk := TwoBin.sourceSurvivalCount a b true false word + TwoBin.sourceSurvivalCount a b true true word
          let vformula := TwoBin.rvSurvivalFormula (a-1) (b-1) positive
          let rformula := TwoBin.rankingSurvivalFormula (a-1) (b-1) positive singles
          IO.println s!"S,{a},{b},{n},{code},{svrv},{svrk},{vformula.num},{vformula.den},{rformula.num},{rformula.den}"
          for k in [0:n+2] do
            let rv := TwoBin.rvCount a b word k
            let rk := TwoBin.rkCount a b word k
            let orders := TwoBin.arrivalOrders word
            let urv := (orders.map (fun w => TwoBin.rvCount a b w k)).sum
            let urk := (orders.map (fun w => TwoBin.rkCount a b w k)).sum
            let kv := TwoBin.tailKernel a b false false k word (0,0)
            let kr := (TwoBin.tailKernel a b true false k word (0,0) + TwoBin.tailKernel a b true true k word (0,0))/2
            IO.println s!"{a},{b},{n},{code},{k},{rv},{rk},{orders.length},{urv},{urk},{kv.num},{kv.den},{kr.num},{kr.den}"
  for a in [1:4] do
    for b in [a:6] do
      if 4 ≤ a+b && a+b ≤ 6 then
        let fw := TwoBin.fixedWitness (a-1) (b-1)
        let uw := TwoBin.uniformWitness (a-1) (b-1)
        let fg := TwoBin.matchingGap a b (a+b-1) fw
        let ug := TwoBin.randomMatchingGap a b (a+b-1) uw / (TwoBin.arrivalOrders uw).length
        IO.println s!"W,{a},{b},{fg.num},{fg.den},{ug.num},{ug.den}"
'''


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--receipt', type=Path, required=True)
    out = parser.parse_args().receipt.resolve()
    if out.exists() or out.is_relative_to(ROOT):
        raise SystemExit('Receipt must be new and outside the repository')
    archive = ROOT/'evidence/Two_Bin_Greedy_Matching_Classification_2026-10-08.zip'
    if hashlib.sha256(archive.read_bytes()).hexdigest() != PIN:
        raise SystemExit('Historical archive identity mismatch')
    with tempfile.TemporaryDirectory(prefix='two-bin-source-check-') as temp:
        temp = Path(temp)
        with zipfile.ZipFile(archive) as z:
            oracle_bytes = z.read('two_bin_classification/oracle.py')
            model_bytes = z.read('two_bin_classification/model.py')
        oracle_path = temp/'oracle.py'
        oracle_path.write_bytes(oracle_bytes)
        spec = importlib.util.spec_from_file_location('two_bin_literal_oracle', oracle_path)
        oracle = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(oracle)
        model_path = temp/'model.py'
        model_path.write_bytes(model_bytes)
        model_spec = importlib.util.spec_from_file_location('two_bin_historical_formula', model_path)
        model = importlib.util.module_from_spec(model_spec)
        model_spec.loader.exec_module(model)
        driver = temp/'SourceCheck.lean'
        driver.write_text(DRIVER)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(driver)], cwd=ROOT/'formalization', text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(result.stdout+result.stderr)
        cache, fixed, uniform, survival_checks, witness_checks = {}, 0, 0, 0, 0
        for row in result.stdout.splitlines():
            if row.startswith('W,'):
                a,b,fnum,fden,unum,uden = map(int,row.split(',')[1:])
                def gap(word):
                    def all_matched(algorithm):
                        return oracle.enumerate_distribution((a,b), word, algorithm)[0].get(a+b-1,Fraction(0))
                    return all_matched('rv')-all_matched('ranking')
                fw = (1,)*(a+b-4)+(2,2,1)
                uw = (2,2)+(1,)*(a+b-3)
                orders = list(permutations(uw))
                assert Fraction(fnum,fden)==model.fixed_witness_gap((a,b))==gap(fw), row
                expected = sum((gap(w) for w in orders),Fraction(0))/len(orders)
                assert Fraction(unum,uden)==model.random_witness_gap((a,b))==expected, row
                witness_checks += 2
                continue
            if row.startswith('S,'):
                a,b,n,code,svrv,svrk,vnum,vden,rnum,rden = map(int,row.split(',')[1:])
                digits, c = [], code
                for _ in range(n):
                    digits.append(c%3);c//=3
                positive = sum(d!=0 for d in digits)
                singles = digits.count(1)
                expected_rv = model.survival((a,b),positive,singles,'rv')
                expected_rk = model.survival((a,b),positive,singles,'ranking')
                assert Fraction(svrv,2**n)==expected_rv==Fraction(vnum,vden), row
                assert Fraction(svrk,2**(n+1))==expected_rk==Fraction(rnum,rden), row
                survival_checks += 2
                continue
            a,b,n,code,k,rv,rk,order_count,urv,urk,kvnum,kvden,krnum,krden = map(int,row.split(','))
            degrees=[]
            c=code
            for _ in range(n):
                degrees.append(c%3);c//=3
            degrees=tuple(degrees)
            def law(word, algorithm):
                key=(a,b,word,algorithm)
                if key not in cache:
                    cache[key] = oracle.enumerate_distribution((a,b), word, algorithm)[0]
                return cache[key]
            def tail(word, algorithm):
                return sum((p for size,p in law(word,algorithm).items() if size>=k),Fraction(0))
            assert Fraction(rv,2**n)==tail(degrees,'rv')==Fraction(kvnum,kvden), row
            assert Fraction(rk,2**(n+1))==tail(degrees,'ranking')==Fraction(krnum,krden), row
            fixed += 2
            orders=list(permutations(degrees))
            assert order_count==len(orders), row
            for algorithm,numerator,denominator in [('rv',urv,2**n),('ranking',urk,2**(n+1))]:
                expected=sum((tail(order,algorithm) for order in orders),Fraction(0))/len(orders)
                assert Fraction(numerator,denominator*order_count)==expected, row
                uniform+=1
        expected_rows=12*sum((3**n)*(n+2) for n in range(5))
        assert fixed==uniform==2*expected_rows
        assert survival_checks==2*12*sum(3**n for n in range(5))
        assert witness_checks==14
        receipt={'status':'PASS','scope':'finite execution, not universal formal bridge',
                 'capacities':'1 <= a <= 3; 1 <= b <= 4 (including label swaps)',
                 'degrees':[0,1,2],'word_lengths':'0..4','degree_words_per_capacity':121,
                 'fixed_tail_comparisons':fixed,'uniform_arrival_tail_comparisons':uniform,
                 'tail_kernel_comparisons_with_original_counts_and_oracle':fixed,
                 'survival_comparisons_actual_lean_vs_historical_formula_and_lean_formula':survival_checks,
                 'witness_gap_comparisons_actual_lean_vs_historical_formula_and_oracle':witness_checks,
                 'witness_capacities':'1 <= a <= b; 4 <= a+b <= 6',
                 'thresholds':'0..word_length+1','lean_driver_sha256':hashlib.sha256(DRIVER.encode()).hexdigest(),
                 'oracle_sha256':hashlib.sha256(oracle_bytes).hexdigest(),
                 'historical_formula_model_sha256':hashlib.sha256(model_bytes).hexdigest(),
                 'source_bridge_sha256':hashlib.sha256((ROOT/'formalization/TwoBin/SourceBridge.lean').read_bytes()).hexdigest(),
                 'window_formula_sha256':hashlib.sha256((ROOT/'formalization/TwoBin/Window.lean').read_bytes()).hexdigest(),
                 'source_model_sha256':hashlib.sha256((ROOT/'formalization/TwoBin/SourceModel.lean').read_bytes()).hexdigest(),
                 'raw_output_sha256':hashlib.sha256(result.stdout.encode()).hexdigest()}
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    main()
