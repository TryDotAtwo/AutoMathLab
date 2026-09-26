#!/usr/bin/env python3
"""Validate the LRX obligation DAG and render all current views, offline/std-lib."""
import argparse, hashlib, json, re
from pathlib import Path
from urllib.parse import unquote, urlsplit
ROOT=Path(__file__).resolve().parents[1]; P=ROOT/'projects/lrx'
STATES={'backlog':'Очередь','working':'Работа','review':'Проверка','integration':'Интеграция','done':'Готово','blocked':'Блокер'}
def require(condition, message):
 if not condition:
  raise ValueError(message)

CLAIMS = {'open', 'partial', 'claimed', 'proved', 'refuted', 'disputed', 'superseded'}
VERIFICATIONS = {'not-reviewed', 'author-checked', 'independently-reproduced', 'formally-checked'}
DEPENDENCIES = {'build', 'assumption-discharge'}


def nonblank(value):
 return isinstance(value, str) and bool(value.strip())


def enum(value, options, message):
 require(isinstance(value, str) and value in options, message)


def string_list(value, message):
 require(isinstance(value, list) and all(nonblank(x) for x in value), message)
 require(len(value) == len(set(value)), message + ' (duplicate)')


def safe_link(value):
 """HTTPS or a relative file inside the repository; no browser URL guessing."""
 if not nonblank(value) or value != value.strip():
  return False
 decoded = unquote(value)
 if any(ord(c) < 32 or ord(c) == 127 or c.isspace() for c in decoded) or '\\' in decoded:
  return False
 try:
  url = urlsplit(value)
  if url.scheme:
   return (url.scheme == 'https' and bool(url.hostname) and
           url.username is None and url.password is None and url.port in (None, 443))
  if url.netloc or decoded.startswith(('/', '#', '?')):
   return False
  # A bare word such as "not-a-source" is not a file locator. URL escapes must
  # not smuggle a scheme, network path or traversal past the repository root.
  decoded_url = urlsplit(decoded)
  if decoded_url.scheme or decoded_url.netloc or ':' in decoded_url.path:
   return False
  path = P / decoded_url.path
  return bool(path.suffix) and path.resolve().is_relative_to(ROOT.resolve())
 except (ValueError, OSError):
  return False


def pinned_reference(ref):
 require(isinstance(ref, dict) and set(ref) == {'url', 'revision'}, 'Invalid pinned reference')
 require(safe_link(ref['url']), 'Unsafe reference URL')
 revision = ref['revision']
 require(isinstance(revision, str) and re.fullmatch(r'(git:[0-9a-f]{40}|sha256:[0-9a-f]{64})', revision),
         'Reference needs full git commit or SHA-256')
 if revision.startswith('git:'):
  require(bool(re.search(r'/(blob|tree|commit)/' + revision[4:] + r'(/|$)', urlsplit(ref['url']).path)),
          'Reference URL does not identify its git commit')


def review_record(record, statement):
 require(isinstance(record, dict) and set(record) == {'statement', 'reviewer', 'artifact', 'review'},
         'Missing versioned review record')
 require(record['statement'] == statement and nonblank(record['reviewer']), 'Review scope/reviewer mismatch')
 pinned_reference(record['artifact'])
 pinned_reference(record['review'])


def verification_text(node):
 v = node['verification']
 return f"{v['status']} ({v['coverage']}): {v['notes']}"


def dependencies_text(node):
 return ', '.join(f'{key} [{kind}]' for key, kind in effective_dependencies(node).items()) or '—'


def record_text(record):
 if record is None:
  return 'Версионная запись отсутствует; готовность всей формулировки не подтверждена.'
 return (f"Проверяющий: {record['reviewer']}. Артефакт: {record['artifact']['url']} "
         f"({record['artifact']['revision']}). Проверка: {record['review']['url']} "
         f"({record['review']['revision']}).")


def effective_dependencies(node):
 deps = dict(node['dependency_kinds'])
 selection = node.get('route_selection')
 if selection is not None:
  for replaced in selection['replaces']:
   del deps[replaced]
  deps[selection['via']] = 'route-selection'
 return deps


def validate(d):
 require(isinstance(d, dict) and type(d.get('schema_version')) is int and d['schema_version'] == 2,
         'Expected proof-map schema_version 2; migrate legacy verification notes explicitly')
 for field in ['revision', 'evidence_cutoff', 'goal', 'scope', 'status_note', 'freshness', 'update_policy']:
  require(nonblank(d.get(field)), 'Missing map field: ' + field)
 nodes = d.get('nodes')
 require(isinstance(nodes, list) and nodes, 'Missing nodes')
 require(all(isinstance(n, dict) and nonblank(n.get('id')) for n in nodes), 'Invalid node/id')
 ids = [n['id'] for n in nodes]
 require(all(re.fullmatch(r'[A-Z][A-Z0-9-]*', k) for k in ids), 'Invalid node id')
 require(len(set(ids)) == len(ids), 'Duplicate id')
 by = {n['id']: n for n in nodes}
 routes = d.get('routes')
 require(isinstance(routes, list) and routes, 'Missing routes')
 require(all(isinstance(r, dict) and nonblank(r.get('id')) and nonblank(r.get('label')) for r in routes),
         'Invalid route')
 route_ids = [r['id'] for r in routes]
 require(len(set(route_ids)) == len(route_ids), 'Duplicate route')
 route_by = {r['id']: r for r in routes}
 for n in nodes:
  enum(n.get('strategy'), route_by, 'Unknown strategy')
 for route in routes:
  if 'terminal' in route:
   require(isinstance(route['terminal'], str) and route['terminal'] in by, 'Unknown route terminal')
  if 'replaces_when_proved' in route:
   string_list(route['replaces_when_proved'], 'Invalid route replacements')
   require(set(route['replaces_when_proved']) <= set(ids), 'Unknown route replacement')
   require(route.get('requires_explicit_interface_review') is True, 'Replacement route needs interface review')
 for n in nodes:
  for field in ['title', 'owner', 'reviewer', 'acceptance', 'statement', 'publication', 'next_action', 'observed_at']:
   require(nonblank(n.get(field)), 'Missing obligation contract: ' + n['id'] + '.' + field)
  enum(n.get('state'), STATES, 'Unknown state')
  enum(n.get('claim'), CLAIMS, 'Unknown claim')
  enum(n.get('assignment'), {'proposed', 'accepted', 'completed'}, 'Unknown assignment')
  enum(n.get('strategy'), route_by, 'Unknown strategy')
  enum(n.get('proof_scope'), {'conditional', 'unconditional'}, 'Unknown proof scope')
  string_list(n.get('assumptions'), 'Invalid explicit assumptions')
  require((n['proof_scope'] == 'conditional') == bool(n['assumptions']), 'Proof scope/assumptions mismatch')
  if n['id'] in {'U-ALL', 'EQ'}:
   require(n['proof_scope'] == 'unconditional', 'Final LRX obligations must be unconditional')
  require('next_checkpoint' in n and (n['next_checkpoint'] is None or nonblank(n['next_checkpoint'])),
          'Invalid checkpoint')
  require('issue' in n and (n['issue'] is None or safe_link(n['issue'])), 'Unsafe issue URL')
  string_list(n.get('evidence'), 'Invalid evidence')
  require(all(safe_link(url) for url in n['evidence']), 'Unsafe evidence URL or missing file locator')
  string_list(n.get('requires'), 'Invalid dependencies')
  require(set(n['requires']) <= set(ids), 'Unknown dependency')
  kinds = n.get('dependency_kinds')
  require(isinstance(kinds, dict) and set(kinds) == set(n['requires']), 'Dependency kinds must match requires')
  for kind in kinds.values():
   enum(kind, DEPENDENCIES, 'Unknown dependency kind')
  if n['proof_scope'] == 'unconditional':
   require('build' not in kinds.values(), 'Unconditional proof prerequisites cannot be build-only')
  v = n.get('verification')
  require(isinstance(v, dict) and set(v) == {'status', 'coverage', 'notes', 'record'}, 'Invalid verification model')
  enum(v['status'], VERIFICATIONS, 'Unknown verification')
  enum(v['coverage'], {'none', 'partial', 'full'}, 'Unknown verification coverage')
  require(nonblank(v['notes']), 'Missing verification notes')
  require((v['status'] == 'not-reviewed') == (v['coverage'] == 'none'), 'Inconsistent verification coverage')
  if v['record'] is not None:
   review_record(v['record'], n['statement'])
   require(all(v['record'][key]['url'] in n['evidence'] for key in ['artifact', 'review']),
           'Review record must be linked in evidence')
  if n['state'] == 'done':
   require(n['evidence'] and n['claim'] == 'proved' and v['coverage'] == 'full' and
           v['status'] in {'independently-reproduced', 'formally-checked'}, 'Unsupported done')
   review_record(v['record'], n['statement'])
  selection = n.get('route_selection')
  if selection is not None:
   require(isinstance(selection, dict) and set(selection) == {'route', 'via', 'replaces', 'review'},
           'Invalid route selection')
   enum(selection['route'], route_by, 'Unknown selected route')
   route = route_by[selection['route']]
   require('replaces_when_proved' in route, 'Selected route is not a replacement')
   via = selection['via']
   require(isinstance(via, str) and via in by and by[via].get('strategy') == route['id'], 'Wrong alternative provider')
   string_list(selection['replaces'], 'Invalid selected replacements')
   require(selection['replaces'] and set(selection['replaces']) <= set(n['requires']) and
           set(selection['replaces']) <= set(route['replaces_when_proved']), 'Unreviewable route replacement')
   review_record(selection['review'], n['statement'])
  # An alternative is selected with a reviewed interface, never made mandatory
  # by appending it to the default proof path.
  require(all('replaces_when_proved' not in route_by.get(by[k].get('strategy'), {}) for k in n['requires']),
          'Alternative incorrectly mandatory')
 for route in routes:
  if 'terminal' in route:
   require(all(kind != 'build' for kind in effective_dependencies(by[route['terminal']]).values()),
           'Terminal proof dependencies cannot be build-only')
 def acyclic(graph):
  seen, active = set(), set()
  def visit(k):
   require(k not in active, 'Cycle')
   if k in seen:
    return
   active.add(k)
   for dep in graph[k]:
    visit(dep)
   active.remove(k)
   seen.add(k)
  for k in ids:
   visit(k)
 acyclic({k: by[k]['requires'] for k in ids})
 effective = {k: effective_dependencies(by[k]) for k in ids}
 acyclic(effective)
 for n in nodes:
  if n['state'] == 'done':
   for dep, kind in effective[n['id']].items():
    if kind != 'build':
     require(by[dep]['state'] == 'done', n['id'] + ': unfinished proof prerequisite ' + dep)
 return d

def render(d):
 digest=hashlib.sha256((P/'proof-map.json').read_bytes()).hexdigest(); ns=d['nodes']
 head=f"Срез свидетельств: {d['evidence_cutoff']}. Версия {d['revision']}. SHA-256 реестра: `{digest}`.\n\n{d['freshness']}\n\n"
 roadmap='# LRX: текущая карта доказательства\n\n'+head+d['goal']+'\n\n'+d['status_note']+'\n\n'
 roadmap+='Основной путь: MODEL + U-SOURCE → LIFT/BRIDGE → PLAN + EXEC + CAP → COST/SMALL → U-ALL; D + U-ALL → EQ. Это зависимости применения, не запрет параллельной работы. ALT-C — альтернативный путь; RELEASE — отдельная публикационная задача.\n\n'
 roadmap+='| Узел | Статус пакета | Ответственный / принятие | Зависимости |\n|---|---|---|---|\n'
 for n in ns:roadmap+=f"| [{n['id']}](#{n['id'].lower()}) · {n['title']} | {STATES[n['state']]} | {n['owner']} / {n['assignment']} | {dependencies_text(n)} |\n"
 for n in ns:
  roadmap+=f"\n## {n['id']}\n\n{n['statement']}\n\n- Утверждение: {n['claim']}; проверка: {verification_text(n)}; публикация: {n['publication']}.\n- Приёмка: {n['acceptance']}\n- Следующий шаг: {n['next_action']}\n- Reviewer: {n['reviewer']}. Checkpoint: {n['next_checkpoint'] or 'новый срок не подтверждён'}.\n- Issue: {n['issue'] or 'см. общую координацию #3'}.\n- Свидетельства: {', '.join(n['evidence']) or 'обязательство; результата пока нет'}.\n- {record_text(n['verification']['record'])}\n"
  if n.get('route_selection'):
   choice=n['route_selection']
   roadmap+=f"- Выбран маршрут {choice['route']} через {choice['via']}; заменены {', '.join(choice['replaces'])}. {record_text(choice['review'])}\n"
 kanban='# LRX: текущий канбан\n\n'+head+'Состояние пакета не равно доказанности всей гипотезы.\n'
 for state,label in STATES.items():
  kanban+='\n## '+label+'\n\n'
  for n in ns:
   if n['state']==state:kanban+=f"- **{n['id']} · {n['title']}** — {n['owner']} ({n['assignment']}). {n['next_action']}\n"
 payload=json.dumps(d,ensure_ascii=False).replace('<','\\u003c').replace('>','\\u003e').replace('&','\\u0026')
 template=(P/'dashboard-template.html').read_text(encoding='utf-8')
 page=template.replace('__DATA__',payload).replace('__HASH__',digest)
 return {'ROADMAP.md':roadmap.rstrip()+'\n','KANBAN.md':kanban.rstrip()+'\n','dashboard.html':page}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
 output=render(validate(json.loads((P/'proof-map.json').read_text(encoding='utf-8'))))
 for name,text in output.items():
  if args.check:require((P/name).exists() and (P/name).read_text(encoding='utf-8')==text, f'Stale generated view: {name}')
  else:(P/name).write_text(text, encoding='utf-8', newline='\n')
 print('PASS: schema, evidence metadata, selected dependency DAG, safe links, 3 synchronized views. No mathematical or remote-artifact verification.')
