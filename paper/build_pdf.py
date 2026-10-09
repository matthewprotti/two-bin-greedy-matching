#!/usr/bin/env python3
"""Build retained LaTeX in a new output directory, using pdfLaTeX or Tectonic."""
from pathlib import Path
import argparse,shutil,subprocess
p=argparse.ArgumentParser();p.add_argument('--out-dir',required=True,type=Path)
a=p.parse_args();src=Path(__file__).resolve().parent;out=a.out_dir.resolve()
if out.exists() or out.is_relative_to(src.parent):raise SystemExit('Choose a new output directory outside the sealed package.')
exe=shutil.which('pdflatex')
tectonic=shutil.which('tectonic')
if not exe and not tectonic:raise SystemExit('Install pdfLaTeX or Tectonic; no build performed.')
out.mkdir(parents=True)
for name in ['manuscript.tex','body.tex']:shutil.copy2(src/name,out/name)
commands=([[exe,'-halt-on-error','-interaction=nonstopmode','manuscript.tex']]*2 if exe else
          [[tectonic,'-X','compile','manuscript.tex','--keep-logs']])
for k,command in enumerate(commands,1):
 r=subprocess.run(command,cwd=out,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/f'build_pass_{k}.txt').write_text(r.stdout)
 if r.returncode:raise SystemExit(f'Build failed; inspect {out}')
print(out/'manuscript.pdf')
