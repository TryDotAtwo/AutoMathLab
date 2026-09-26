import copy, importlib.util, json, unittest, os, shutil, subprocess, sys, tempfile
from pathlib import Path
P=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('renderer',P/'scripts/render_lrx_map.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
class MapTests(unittest.TestCase):
 def setUp(self): self.d=json.loads((P/'projects/lrx/proof-map.json').read_text(encoding='utf-8'))
 def node(self, key):return next(n for n in self.d['nodes'] if n['id']==key)
 def reviewed(self, key):
  # Synthetic metadata, never a proof or a modification of the real registry.
  n=self.node(key); record=copy.deepcopy(self.node('D')['verification']['record'])
  record['statement']=n['statement']
  n.update(state='done',claim='proved')
  n['verification']={'status':'formally-checked','coverage':'full','notes':'Synthetic test fixture','record':record}
  n['evidence']=[record['artifact']['url'],record['review']['url']]
 def alternative(self):
  # Keep the default edges and declare the exact reviewed replacement.
  self.reviewed('U-ALL')
  self.node('U-ALL')['route_selection']={
   'route':'alternative','via':'ALT-C','replaces':['BRIDGE','PLAN','COST'],
   'review':copy.deepcopy(self.node('U-ALL')['verification']['record'])}
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
  self.reviewed('EQ')
  with self.assertRaisesRegex(ValueError,'EQ: unfinished proof prerequisite U-ALL'):m.validate(self.d)
 def test_alternative_not_mandatory(self):
  next(n for n in self.d['nodes'] if n['id']=='EQ')['requires'].append('ALT-C')
  self.node('EQ')['dependency_kinds']['ALT-C']='assumption-discharge'
  with self.assertRaises(ValueError):m.validate(self.d)
 def test_blank_contract_fields(self):
  for field in ['title','owner','reviewer','statement','acceptance','publication','next_action','observed_at']:
   with self.subTest(field=field):
    invalid=copy.deepcopy(self.d);invalid['nodes'][0][field]=' \t\n'
    with self.assertRaises(ValueError):m.validate(invalid)
 def test_unknown_status_and_bad_types(self):
  for field,value in [('claim','nonsense'),('claim',[]),('state',[]),('assignment','nonsense'),
                      ('strategy','nonsense'),('evidence','https://example.org'),('evidence',[3]),
                      ('requires','MODEL'),('requires',[{}]),('title',42)]:
   with self.subTest(field=field,value=value):
    invalid=copy.deepcopy(self.d);invalid['nodes'][0][field]=value
    with self.assertRaises(ValueError):m.validate(invalid)
 def test_verification_is_explicit(self):
  for value in ['nonsense','formally-checked',{},None]:
   with self.subTest(value=value):
    invalid=copy.deepcopy(self.d);invalid['nodes'][0]['verification']=value
    with self.assertRaises(ValueError):m.validate(invalid)
  for field,value in [('status','nonsense'),('coverage','nonsense'),('notes',' '),('status',[])]:
   with self.subTest(field=field):
    invalid=copy.deepcopy(self.d);invalid['nodes'][0]['verification'][field]=value
    with self.assertRaises(ValueError):m.validate(invalid)
 def test_old_scoped_notes_preserved(self):
  self.assertEqual(self.node('BRIDGE')['verification']['notes'],
                   'formally-checked within explicit closed-cut hypothesis; independent replay recorded')
  self.assertEqual(self.node('BRIDGE')['verification']['coverage'],'partial')
  self.assertEqual(self.node('EXEC')['verification']['status'],'independently-reproduced')
  self.assertEqual(self.node('ALT-C')['verification']['notes'],
                   'author package with agent review; no new Lean; coordinator intake only')
 def test_done_requires_full_scope_and_versioned_record(self):
  for field,value in [('coverage','partial'),('status','author-checked'),('record',None)]:
   with self.subTest(field=field):
    invalid=copy.deepcopy(self.d)
    next(n for n in invalid['nodes'] if n['id']=='D')['verification'][field]=value
    with self.assertRaises(ValueError):m.validate(invalid)
 def test_done_record_rejects_changed_statement_and_unpinned_reference(self):
  self.node('D')['statement']+=' An unreviewed stronger statement.'
  with self.assertRaisesRegex(ValueError,'scope/reviewer'):m.validate(self.d)
  self.setUp();self.node('D')['verification']['record']['artifact']['revision']='git:main'
  with self.assertRaisesRegex(ValueError,'full git commit'):m.validate(self.d)
  self.setUp();self.node('D')['verification']['record']['artifact']['url']='https://example.org/blob/main/proof.md'
  with self.assertRaisesRegex(ValueError,'does not identify'):m.validate(self.d)
 def test_done_intermediate_discharge_is_checked(self):
  self.reviewed('PLAN')
  with self.assertRaisesRegex(ValueError,'PLAN: unfinished proof prerequisite BRIDGE'):m.validate(self.d)
 def test_done_conditional_lemma_can_have_open_build_dependency(self):
  self.reviewed('EXEC');self.node('EXEC')['requires']=['PLAN']
  self.node('EXEC')['dependency_kinds']={'PLAN':'build'}
  m.validate(self.d)
 def test_terminal_cannot_downgrade_proof_to_build(self):
  self.node('EQ')['dependency_kinds']['U-ALL']='build'
  with self.assertRaisesRegex(ValueError,'Unconditional proof prerequisites'):m.validate(self.d)
 def test_upper_bound_cannot_hide_prerequisites_behind_build(self):
  self.reviewed('U-ALL');self.reviewed('EQ')
  self.node('U-ALL')['dependency_kinds']={k:'build' for k in self.node('U-ALL')['requires']}
  with self.assertRaisesRegex(ValueError,'Unconditional proof prerequisites'):m.validate(self.d)
 def test_final_obligations_cannot_claim_conditional_scope(self):
  for key in ['U-ALL','EQ']:
   with self.subTest(key=key):
    self.setUp();self.node(key).update(proof_scope='conditional',assumptions=['Unproved hypothesis'])
    with self.assertRaisesRegex(ValueError,'Final LRX obligations'):m.validate(self.d)
 def test_conditional_scope_must_list_assumptions(self):
  self.node('EXEC')['assumptions']=[]
  with self.assertRaisesRegex(ValueError,'scope/assumptions'):m.validate(self.d)
 def test_strategy_labels_cannot_bypass_final_dependencies(self):
  self.reviewed('EQ')
  for n in self.d['nodes']:
   if n['id']!='EQ':n['strategy']='separate'
  with self.assertRaisesRegex(ValueError,'EQ: unfinished proof prerequisite U-ALL'):m.validate(self.d)
 def test_main_route_completion(self):
  for n in self.d['nodes']:
   if n['strategy']=='main':self.reviewed(n['id'])
  m.validate(self.d)
 def test_reviewed_alternative_can_complete_with_replaced_nodes_open(self):
  for key in ['MODEL','U-SOURCE','EXEC','SMALL','ALT-C','EQ']:self.reviewed(key)
  self.alternative()
  m.validate(self.d)
  self.assertEqual(set(m.effective_dependencies(self.node('U-ALL'))),{'MODEL','EXEC','SMALL','ALT-C'})
 def test_alternative_needs_review_and_finished_provider(self):
  self.alternative()
  self.node('U-ALL')['route_selection']['review']=None
  with self.assertRaisesRegex(ValueError,'review record'):m.validate(self.d)
  self.alternative()
  for key in ['MODEL','U-SOURCE','EXEC','SMALL']:self.reviewed(key)
  with self.assertRaisesRegex(ValueError,'unfinished proof prerequisite ALT-C'):m.validate(self.d)
 def test_alternative_cannot_replace_unrelated_dependencies(self):
  self.alternative();self.node('U-ALL')['route_selection']['replaces'].append('MODEL')
  with self.assertRaisesRegex(ValueError,'Unreviewable route replacement'):m.validate(self.d)
 def test_selected_alternative_cycle(self):
  self.alternative();self.node('U-ALL')['state']='review'
  self.node('ALT-C')['requires']=['U-ALL'];self.node('ALT-C')['dependency_kinds']={'U-ALL':'assumption-discharge'}
  with self.assertRaisesRegex(ValueError,'Cycle'):m.validate(self.d)
 def test_dependency_kinds_and_route_ids(self):
  for mutate in [lambda d:d['nodes'][0].update(dependency_kinds={'D':'build'}),
                 lambda d:d['routes'].append(copy.deepcopy(d['routes'][0])),
                 lambda d:d['routes'][0].update(terminal='MISSING')]:
   invalid=copy.deepcopy(self.d);mutate(invalid)
   with self.assertRaises(ValueError):m.validate(invalid)
 def test_safe_links(self):
  for url in ['https://example.org/proof?q=1&x=2#scope','README.md','./reviews/proof.md','../README.md']:
   with self.subTest(url=url):self.assertTrue(m.safe_link(url))
  for url in ['javascript:alert(1)','JaVaScRiPt:alert(1)','data:text/html,hi','file:///C:/x',
              '//example.org/x','\\\\example.org\\x','https://user:pass@example.org',
              'https://example.org:bad/x','https://example.org/%0afoo','https://exa\nmple.org',
              'https://example.org/%5cfoo','%2f%2fevil.org/a.md','%6aavascript:alert(1)',
              '../../../../../outside.md','not-a-source',' ','https://']:
   with self.subTest(url=url):self.assertFalse(m.safe_link(url))
 def test_evidence_and_issue_use_same_url_policy(self):
  for field,value in [('evidence',['javascript:alert(1)']),('issue','data:text/html,hi')]:
   invalid=copy.deepcopy(self.d);invalid['nodes'][0][field]=value
   with self.assertRaisesRegex(ValueError,'Unsafe'):m.validate(invalid)
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
