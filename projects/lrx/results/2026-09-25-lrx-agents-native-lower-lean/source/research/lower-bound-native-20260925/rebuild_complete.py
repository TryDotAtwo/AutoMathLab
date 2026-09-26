"""Fresh local import-closure kernel build. Reuses only pinned external package objects."""
from pathlib import Path
import argparse,subprocess,os,json,hashlib,re,datetime
P=Path(__file__).resolve().parent;ROOT=P.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--lean',required=True);ap.add_argument('--packages-directory',required=True);ap.add_argument('--output-directory',required=True);args=ap.parse_args()
 lean=Path(args.lean).resolve();packages=Path(args.packages_directory).resolve();out=Path(args.output_directory).resolve()
 assert not out.exists();(out/'LRX').mkdir(parents=True);(out/'receipts').mkdir()
 version=subprocess.check_output([str(lean),'--version'],text=True);assert '4.34.0' in version
 paths=sorted(packages.glob('*/.lake/build/lib/lean'));assert paths
 env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[out]+paths))
 visited=set();order=[]
 def visit(m):
  if m in visited:return
  visited.add(m);src=ROOT/'formal'/Path(*m.split('.')).with_suffix('.lean');assert src.is_file()
  for dep in re.findall(r'^import (LRX\.\w+)',src.read_text(),re.M):visit(dep)
  order.append(m)
 visit('LRX.LowerBoundExceptionalAudit');visit('LRX.LowerBoundNativeComplete');receipts=[];all_axioms={}
 for m in order:
  rel=Path(*m.split('.')).with_suffix('.lean');src=ROOT/'formal'/rel;obj=out/rel.with_suffix('.olean')
  command=[str(lean),str(rel),'-o',str(obj)]
  run=subprocess.run(command,cwd=ROOT/'formal',env=env,text=True,capture_output=True);log=run.stdout+run.stderr
  logfile=out/'receipts'/(m+'.log');logfile.write_text(log)
  axioms={k:[x.strip() for x in v.split(',') if x.strip()] for k,v in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
  all_axioms.update(axioms)
  rec={'module':m,'source':str(src.relative_to(ROOT)),'source_sha256':sha(src),'command':command,'returncode':run.returncode,'log':str(logfile.relative_to(out)),'log_sha256':sha(logfile),'axioms':axioms,'object_sha256':sha(obj) if obj.exists() else None}
  (out/'receipts'/(m+'.json')).write_text(json.dumps(rec,indent=2)+'\n');receipts.append(rec)
  assert run.returncode==0 and 'sorryAx' not in log,log
  assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values())
  print(m,'PASS',flush=True)
 target=[k for k in all_axioms if k.startswith('LRX.LowerBoundNativeComplete.')];assert len(target)==4
 result={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_version':version.strip(),'local_sources':len(order),'new_exports':len(target),'axioms':{k:all_axioms[k] for k in target},'receipts':receipts,'LEAN_PATH':env['LEAN_PATH'],'scope':'Complete all-n native word lower theorem for n>=4, combined A-v2/B-v1; distance/diameter API corollaries not included.'}
 (out/'BUILD_RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','sources':len(order),'new_exports':len(target)}))
if __name__=='__main__':main()
