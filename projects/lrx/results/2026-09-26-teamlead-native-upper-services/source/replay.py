"""Fresh local Lean objects, portable CLI, pinned external dependency cache only.
No network, source execution or native_decide. Run from any directory.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--lean',default='lean');p.add_argument('--dependency-path',default=os.environ.get('LEAN_PATH',''));p.add_argument('--out',default='fresh-build');a=p.parse_args()
root=pathlib.Path(__file__).resolve().parent;formal=root/'formal';out=pathlib.Path(a.out).resolve();out.mkdir(parents=True,exist_ok=True)
files={str(x.relative_to(formal).with_suffix('')).replace(os.sep,'.'):x for x in formal.rglob('*.lean')}
seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 for line in files[m].read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:
    if dep in files:visit(dep)
 order.append(m)
for m in sorted(files):visit(m)
# A caller cannot accidentally satisfy local imports with a retained olean.
for raw in a.dependency_path.split(os.pathsep):
 if raw and any((pathlib.Path(raw)/pathlib.Path(*m.split('.')).with_suffix('.olean')).exists() for m in files):
  raise SystemExit('dependency-path contains packaged local objects: '+raw)
env=os.environ.copy();env['LEAN_PATH']=str(out)+os.pathsep+a.dependency_path
receipt={'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'lean':subprocess.check_output([a.lean,'--version'],text=True).strip(),'local_objects':'all fresh in out; old local olean paths rejected','external_cache':'pinned Mathlib and dependencies reused, not rebuilt','modules':[],'exit_code':None}
sha=lambda b:hashlib.sha256(b).hexdigest()
for i,m in enumerate(order,1):
 src=files[m];obj=out/pathlib.Path(*m.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=[a.lean,str(src.relative_to(formal)),'-o',str(obj)]
 r=subprocess.run(cmd,cwd=formal,env=env,capture_output=True,text=True)
 log=r.stdout+r.stderr;logp=out/pathlib.Path(*m.split('.')).with_suffix('.log');logp.write_text(log)
 ax={name: [x.strip() for x in axioms.split(',') if x.strip()] for name,axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)}
 entry={'module':m,'source_sha256':sha(src.read_bytes()),'exit_code':r.returncode,'log_sha256':sha(log.encode()),'axioms':ax,'command':cmd}
 if r.returncode==0:entry['object_sha256']=sha(obj.read_bytes())
 receipt['modules'].append(entry);receipt['exit_code']=r.returncode
 (out/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(f'{i}/{len(order)} {m}: exit {r.returncode}',flush=True)
 if r.returncode or 'sorryAx' in log:
  print(log,flush=True);raise SystemExit(1)
receipt['completed_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
(out/'BUILD_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('All packaged local modules passed.',flush=True)
