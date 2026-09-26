import copy, importlib.util, json, unittest, os, shutil, subprocess, sys, tempfile
from pathlib import Path
P=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('renderer',P/'scripts/render_lrx_map.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class MapTests(unittest.TestCase):
 def setUp(self): self.d=json.loads((P/'projects/lrx/proof-map.json').read_text(encoding='utf-8'))
 def test_current(self):m.validate(self.d)
 def test_cycle(self):
  self.d['nodes'][0]['requires']=['EQ']
  with self.assertRaises(ValueError):m.validate(self.d)
 def test_unknown_dependency(self):
  self.d['nodes'][0]['requires']=['MISSING']
  with self.assertRaises(ValueError):m.validate(self.d)
 def test_unsupported_done(self):
  n=next(n for n in self.d['nodes'] if n['id']=='PLAN');n['state']='done'
  with self.assertRaises(ValueError):m.validate(self.d)
 def test_premature_equality(self):
  n=next(n for n in self.d['nodes'] if n['id']=='EQ');n.update(state='done',claim='proved',verification='formally-checked',evidence=['test'])
  with self.assertRaises(ValueError):m.validate(self.d)
 def test_alternative_not_mandatory(self):
  next(n for n in self.d['nodes'] if n['id']=='EQ')['requires'].append('ALT-C')
  with self.assertRaises(ValueError):m.validate(self.d)
 def test_cli_utf8_roundtrip_and_exact_registry_bytes(self):
  # A fresh Windows checkout must preserve the registry digest, and neither
  # reading nor generation may depend on the user's default text encoding.
  with tempfile.TemporaryDirectory() as tmp:
   root=Path(tmp); (root/'scripts').mkdir(); target=root/'projects/lrx'; target.mkdir(parents=True)
   shutil.copy2(P/'scripts/render_lrx_map.py',root/'scripts/render_lrx_map.py')
   for name in ['proof-map.json','dashboard-template.html','ROADMAP.md','KANBAN.md','dashboard.html']:
    shutil.copy2(P/'projects/lrx'/name,target/name)
   env=dict(os.environ,PYTHONUTF8='0')
   cmd=[sys.executable,str(root/'scripts/render_lrx_map.py')]
   def run(*args):
    result=subprocess.run([*cmd,*args],env=env,capture_output=True)
    self.assertEqual(result.returncode,0,result.stdout+result.stderr)
   run('--check')
   before={name:(target/name).read_text(encoding='utf-8') for name in ['ROADMAP.md','KANBAN.md','dashboard.html']}
   run()
   run('--check')
   for name,text in before.items():
    self.assertEqual((target/name).read_bytes(),text.encode('utf-8'))
   # -O used to silently disable synchronization and evidence gates.
   optimized=[sys.executable,'-O',str(root/'scripts/render_lrx_map.py'),'--check']
   (target/'ROADMAP.md').write_text('stale\n',encoding='utf-8')
   result=subprocess.run(optimized,env=env,capture_output=True)
   self.assertNotEqual(result.returncode,0)
   self.assertIn(b'Stale generated view',result.stderr)
   run()
   invalid=copy.deepcopy(self.d)
   next(n for n in invalid['nodes'] if n['id']=='PLAN')['state']='done'
   (target/'proof-map.json').write_text(json.dumps(invalid),encoding='utf-8')
   result=subprocess.run(optimized,env=env,capture_output=True)
   self.assertNotEqual(result.returncode,0)
   self.assertIn(b'Unsupported done',result.stderr)
if __name__=='__main__':unittest.main()
