#!/usr/bin/env python3
"""Check sealed membership and replay in a disposable copy; no network or writes to source.
A digest binds received bytes; it does not authenticate an issuer on its own.
"""
from pathlib import Path,PurePosixPath
import hashlib,json,os,shutil,stat,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
MODE='publication'
PARENT_HASH='97b6885c2f40a71101b58e2245d18f96335875306c3df8447754e52e5f0618d3'
GENERATED_DIRS={'.git','.lake','__pycache__'}
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def snapshot(root):
 out={}
 for f in sorted(root.rglob('*')):
  if any(part in GENERATED_DIRS for part in f.relative_to(root).parts):continue
  if f.is_symlink():raise ValueError('Symlink rejected: '+str(f))
  if f.is_file() and f.relative_to(root).as_posix()!='MANIFEST.json':
   out[f.relative_to(root).as_posix()]={'bytes':f.stat().st_size,'sha256':digest(f)}
 return out
def verify(root):
 expected=json.loads((root/'MANIFEST.json').read_text())['files']
 got=snapshot(root)
 if got!=expected:
  added=sorted(set(got)-set(expected));removed=sorted(set(expected)-set(got))
  changed=sorted(k for k in set(got)&set(expected) if got[k]!=expected[k])
  raise ValueError(f'Manifest mismatch: added={added}; missing={removed}; changed={changed}')
 print(f'MANIFEST PASS ({len(got)} files)',flush=True)
 return got
def extract_pinned(archive,out):
 if digest(archive)!=PARENT_HASH:raise ValueError('Historical archive identity mismatch')
 with zipfile.ZipFile(archive) as z:
  items=z.infolist()
  if len(items)>200 or sum(x.file_size for x in items)>20_000_000:raise ValueError('Archive exceeds fixed bounds')
  seen=set()
  for x in items:
   p=PurePosixPath(x.filename)
   if x.filename in seen or p.is_absolute() or '..' in p.parts or '\\' in x.filename:raise ValueError('Unsafe archive path')
   seen.add(x.filename)
   if stat.S_ISLNK(x.external_attr>>16):raise ValueError('Archive symlink rejected')
   target=out.joinpath(*p.parts)
   if not target.resolve().is_relative_to(out.resolve()):raise ValueError('Path escaped extraction')
   if x.is_dir():target.mkdir(parents=True,exist_ok=True)
   else:
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(z.read(x))
def main():
 before=verify(ROOT)
 with tempfile.TemporaryDirectory(prefix='matching-publication-replay-') as td:
  work=Path(td);copy=work/'copy';shutil.copytree(ROOT,copy,ignore=shutil.ignore_patterns(*GENERATED_DIRS))
  verify(copy)
  env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
  if MODE=='publication':
   extract_pinned(copy/'evidence/Two_Bin_Greedy_Matching_Classification_2026-10-08.zip',work/'historical')
   cwd=work/'historical/two_bin_classification'
   command=[sys.executable,'-B','REPLAY.py']
  else:
   ref=copy/'reference/Two_Bin_Greedy_Matching_Classification_2026-10-08.zip'
   if digest(ref)!=PARENT_HASH:raise ValueError('Reference archive identity mismatch')
   cwd=copy;command=[sys.executable,'-B','starter/check.py','--compare','evidence/starter_controls.json']
  subprocess.run(command,cwd=cwd,env=env,check=True)
  if snapshot(copy)!=before:raise ValueError('Copied package changed during replay')
 if snapshot(ROOT)!=before:raise ValueError('Source package changed during replay')
 print('FRESH-COPY REPLAY PASS; sealed source and copied package unchanged',flush=True)
 print('This command replays Python evidence only; consult formalization/STATUS.json for Lean scope.',flush=True)
if __name__=='__main__':
 try:main()
 except Exception as e:
  print('FAIL: '+str(e),file=sys.stderr);raise SystemExit(1)
