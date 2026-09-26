"""Verify published package integrity and retained author receipts, not theorem correctness."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
source=root/'source'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((source/'MANIFEST.json').read_text())
for rel,item in manifest.items():
 p=source/rel
 assert p.is_file() and p.stat().st_size==item['bytes'] and sha(p)==item['sha256'],rel
receipt=json.loads((source/'BUILD_RECEIPT.json').read_text())
for m in receipt['modules']:
 assert m['exit_code']==0,m['module']
 assert sha(source/'formal'/(m['module']+'.lean'))==m['source_sha256'],m['module']
 assert sha(source/'logs'/(m['module']+'.log'))==m['log_sha256'],m['module']
logs='\n'.join(x.read_text() for x in (source/'logs').glob('*.log'))
assert 'sorryAx' not in logs
exports=json.loads((source/'EXPORTS_AXIOMS.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
for name,axioms in exports.items():
 assert set(axioms)<=allowed,(name,axioms)
 matches=re.findall("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",logs)
 assert matches and any({a.strip() for a in match.split(',')}==set(axioms) for match in matches),name
local={p.stem for p in (source/'formal').glob('*.lean')}
external=set()
for p in (source/'formal').glob('*.lean'):
 for line in p.read_text().splitlines():
  if line.startswith('import '):external.update(line.split()[1:])
assert external-local=={'LRX.BlockExchange'}|{m for m in external if m.startswith('Mathlib.')}
assert len(json.loads((source/'lake-manifest.json').read_text())['packages'])==9
assert (source/'lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.0'
assert not any(p.suffix in {'.olean','.zip'} for p in root.rglob('*'))
print(json.dumps({'manifest_entries':len(manifest),'modules':len(receipt['modules']),'named_axiom_reports':len(exports),'extra_axiom_free_reports':len(re.findall('does not depend on any axioms',logs)),'all_hashes_match':True,'scope':'integrity/receipt audit only; no independent Lean rebuild or mathematical review'},indent=2))
