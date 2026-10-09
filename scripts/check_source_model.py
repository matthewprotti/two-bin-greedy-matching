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
          for k in [0:n+2] do
            let rv := TwoBin.rvCount a b word k
            let rk := TwoBin.rkCount a b word k
            let orders := TwoBin.arrivalOrders word
            let urv := (orders.map (fun w => TwoBin.rvCount a b w k)).sum
            let urk := (orders.map (fun w => TwoBin.rkCount a b w k)).sum
            IO.println s!"{a},{b},{n},{code},{k},{rv},{rk},{orders.length},{urv},{urk}"
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
        oracle_path = temp/'oracle.py'
        oracle_path.write_bytes(oracle_bytes)
        spec = importlib.util.spec_from_file_location('two_bin_literal_oracle', oracle_path)
        oracle = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(oracle)
        driver = temp/'SourceCheck.lean'
        driver.write_text(DRIVER)
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(driver)], cwd=ROOT/'formalization', text=True, capture_output=True)
        if result.returncode:
            raise RuntimeError(result.stdout+result.stderr)
        cache, fixed, uniform = {}, 0, 0
        for row in result.stdout.splitlines():
            a,b,n,code,k,rv,rk,order_count,urv,urk = map(int,row.split(','))
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
            assert Fraction(rv,2**n)==tail(degrees,'rv'), row
            assert Fraction(rk,2**(n+1))==tail(degrees,'ranking'), row
            fixed += 2
            orders=list(permutations(degrees))
            assert order_count==len(orders), row
            for algorithm,numerator,denominator in [('rv',urv,2**n),('ranking',urk,2**(n+1))]:
                expected=sum((tail(order,algorithm) for order in orders),Fraction(0))/len(orders)
                assert Fraction(numerator,denominator*order_count)==expected, row
                uniform+=1
        expected_rows=12*sum((3**n)*(n+2) for n in range(5))
        assert fixed==uniform==2*expected_rows
        receipt={'status':'PASS','scope':'finite execution, not universal formal bridge',
                 'capacities':'1 <= a <= 3; 1 <= b <= 4 (including label swaps)',
                 'degrees':[0,1,2],'word_lengths':'0..4','degree_words_per_capacity':121,
                 'fixed_tail_comparisons':fixed,'uniform_arrival_tail_comparisons':uniform,
                 'thresholds':'0..word_length+1','lean_driver_sha256':hashlib.sha256(DRIVER.encode()).hexdigest(),
                 'oracle_sha256':hashlib.sha256(oracle_bytes).hexdigest(),
                 'source_model_sha256':hashlib.sha256((ROOT/'formalization/TwoBin/SourceModel.lean').read_bytes()).hexdigest(),
                 'raw_output_sha256':hashlib.sha256(result.stdout.encode()).hexdigest()}
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    main()
