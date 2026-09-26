from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((R/'MANIFEST.json').read_text())
for f,h in m['files'].items():assert sha(R/f)==h,f
b=json.loads((P/'complete_clean_build/BUILD_RESULT.json').read_text());assert b['status']=='PASS' and b['new_exports']==4 and b['local_sources']==24
all_axioms={}
for row in b['receipts']:
 assert row['returncode']==0 and sha(R/row['source'])==row['source_sha256']
 log=P/'complete_clean_build'/row['log'];assert sha(log)==row['log_sha256'] and 'sorryAx' not in log.read_text()
 assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in row['axioms'].values())
 all_axioms.update(row['axioms'])
assert 'LRX.LowerBoundNativeComplete.native_lower' in all_axioms
new_a=[k for k in all_axioms if k.startswith('LRX.LowerBoundNativeTrace.')]
new_b=[k for k in all_axioms if k.startswith(('LRX.LowerBoundExceptional','LRX.LowerBoundFourParity.'))]
assert len(new_a)==12 and len(new_b)==28,(len(new_a),len(new_b))
for row in json.loads((P/'B_IMPORTED_SOURCES.json').read_text()):assert sha(R/row['path'])==row['sha256']
assert json.loads(subprocess.check_output([sys.executable,str(P/'replay.py')],text=True))==json.loads((P/'replay.json').read_text())
assert not list(R.rglob('*.olean'))
print(json.dumps({'status':'PASS','hashes':len(m['files']),'local_sources':24,'A_exports':len(new_a),'B_exports':len(new_b),'glue_exports':4,'kernel_rebuilt':False}))
