#!/usr/bin/env python3
"""Fresh local-module Lean replay. Existing output is rejected. External cache reused."""
import argparse,hashlib,json,os,re,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lean',required=True)
p.add_argument('--packages',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();root=Path(__file__).resolve().parent;formal=root/'formal'
lean=str(Path(a.lean).resolve());pkgs=a.packages.resolve();out=a.output.resolve()
assert pkgs.is_dir(),pkgs
out.mkdir(exist_ok=False,parents=True);objects=out/'objects';objects.mkdir()
paths=list(sorted(pkgs.glob('*/.lake/build/lib/lean')))
assert paths,'No pinned dependency cache found; see REPRODUCE.md'
pinned=json.loads((formal/'lake-manifest.json').read_text())
deps=[]
for item in pinned['packages']:
 if item.get('type')=='git':
  head=subprocess.check_output(['git','-C',str(pkgs/item['name']),'rev-parse','HEAD'],text=True).strip()
  assert head==item['rev'],(item['name'],head,item['rev'])
  deps.append({'name':item['name'],'rev':head})
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(objects)]+[str(x) for x in paths])
mods={str(x.relative_to(formal))[:-5].replace('/','.'):x for x in formal.rglob('*.lean') if '.lake' not in x.parts}
done=set();rows=[]
def build(name):
 if name in done:return
 src=mods[name]
 for line in src.read_text().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():
    if dep in mods:build(dep)
 obj=objects/(name.replace('.','/')+'.olean');obj.parent.mkdir(exist_ok=True,parents=True)
 cmd=[lean,'-o',str(obj),str(src.relative_to(formal))]
 r=subprocess.run(cmd,cwd=formal,env=env,text=True,capture_output=True)
 log=out/(name.replace('.','_')+'.log');log.write_text(r.stdout+r.stderr)
 row={'module':name,'exit_code':r.returncode,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'command':cmd}
 rows.append(row);print(name,r.returncode,flush=True)
 if r.returncode:raise SystemExit(log.read_text())
 done.add(name)
build('Submission')
axiomtext=(out/'Submission.log').read_text()
assert 'sorryAx' not in axiomtext
for theorem in ['diameter_lower','reflected_distance']:
 assert theorem in axiomtext,theorem
result={'status':'PASS','scope':'Fresh local modules; pinned external package cache reused','lean':subprocess.check_output([lean,'--version'],text=True).strip(),'dependencies':deps,'results':rows}
(out/'REPLAY.json').write_text(json.dumps(result,indent=2))
