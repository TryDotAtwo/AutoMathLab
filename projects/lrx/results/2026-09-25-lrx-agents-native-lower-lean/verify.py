"""Verify archived evidence. Does NOT perform a fresh Lean kernel replay."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((root/'MANIFEST.json').read_text())
for name,digest in manifest['files'].items():assert sha(root/name)==digest,name
source=root/'source';replay=root/'independent-replay';objects=replay/'fresh-objects'
subprocess.run([sys.executable,str(source/'research/lower-bound-native-20260925/verify_complete.py')],check=True)
b=json.loads((objects/'BUILD_RESULT.json').read_text());assert b['status']=='PASS' and len(b['receipts'])==24
assert '4.34.0' in b['lean_version']
all_axioms={}
for row in b['receipts']:
 assert row['returncode']==0
 assert sha(source/row['source'])==row['source_sha256']
 log=objects/row['log'];assert sha(log)==row['log_sha256']
 text=log.read_text();assert 'sorryAx' not in text
 parsed={k:[x.strip() for x in v.split(',') if x.strip()] for k,v in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text)}
 assert parsed==row['axioms']
 for v in parsed.values():assert set(v)<={'propext','Classical.choice','Quot.sound'}
 all_axioms.update(parsed)
assert 'LRX.LowerBoundNativeComplete.native_lower' in all_axioms
for dep in json.loads((replay/'dependencies.json').read_text()):assert dep['match'] and dep['actual']==dep['expected']
scope=(replay/'ScopeCheck.log').read_text();assert 'sorryAx' not in scope and 'depends on axioms' in scope and 'LRX.LowerBoundNativeComplete.native_lower' in scope
assert not list(root.rglob('*.olean'))
print(json.dumps({'status':'PASS','files':len(manifest['files']),'fresh_compilation_receipts':24,'scope_check':'PASS','new_kernel_run':False}))
