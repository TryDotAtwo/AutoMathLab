#!/usr/bin/env python3
"""Integrity and historical receipt checks; never executes Lean."""
import argparse, hashlib, json
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__);p.add_argument('--external',action='store_true');args=p.parse_args()
root=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((root/'MANIFEST.json').read_text())
for name,digest in manifest['files'].items():
 f=root/name
 if f.is_symlink() or not f.is_file() or sha(f)!=digest:raise SystemExit('Integrity failure: '+name)
receipt=json.loads((root/'checks/REPLAY_RECEIPT.json').read_text())
for row in receipt['results']:
 assert row['exit_code']==0
 assert sha(root/'checks/logs'/(row['module'].replace('.','_')+'.log'))==row['log_sha256']
 if row['source_in_this_package']:
  assert sha(root/'formal'/(row['module'].replace('.','/')+'.lean'))==row['source_sha256']
print('Own package hashes and historical receipt identities PASS; no Lean execution.')
external=json.loads((root/'EXTERNAL_DEPENDENCIES.json').read_text())
missing=[]
for name,info in external['files'].items():
 f=root/'formal'/name
 if not f.is_file():missing.append(name)
 elif f.is_symlink() or sha(f)!=info['sha256']:raise SystemExit('Wrong external source: '+name)
if missing:
 print('Standalone replay BLOCKED: external graph source redistribution/access pending: '+', '.join(missing))
 if args.external:raise SystemExit(2)
else:print('All three external source identities match; access/redistribution terms still require human confirmation.')
