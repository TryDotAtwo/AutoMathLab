"""Explicit local Lean replay only. No installs, network, ambient credentials or CI hooks."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import time

MODULES = (
    'BlockTransport', 'BlockTransportRight', 'GrowingCollector',
    'TwoBlockCollector', 'Navigation', 'CollectorNavigation',
    'GapRepresentation', 'NavigationCoordinates',
)
ALLOWED = {'propext', 'Quot.sound'}
AXIOMS = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def child_limits():
    resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path, help='Existing Lean4.19.0 executable')
    parser.add_argument('--out', required=True, type=Path, help='New, nonexisting evidence directory')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    lean = args.lean.resolve(strict=True)
    out = args.out.resolve()
    if out == root or root.is_relative_to(out):
        raise SystemExit('Evidence must not contain or replace the source directory')
    out.mkdir(parents=True, exist_ok=False)
    build = out / 'build'
    build.mkdir()
    # Deliberately do not inspect/inherit tokens or credential variables.
    child_env = {'PATH': '/usr/bin:/bin', 'LEAN_PATH': str(build)}
    inputs = [name+'.lean' for name in MODULES] + ['lean-toolchain', 'declarations.txt', 'verify.py']
    before = {name: sha(root/name) for name in inputs}
    expected = (root/'declarations.txt').read_text().splitlines()
    if len(expected) != len(set(expected)) or not expected:
        raise SystemExit('Empty or duplicate declaration list')
    if (root/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.19.0':
        raise SystemExit('Unexpected toolchain pin')
    version = subprocess.run([str(lean), '--version'], env=child_env,
        capture_output=True, text=True, timeout=10, check=True).stdout.strip()
    if not re.search(r'\bversion 4\.19\.0,', version):
        raise SystemExit('Lean version differs from4.19.0: '+version)
    report = dict(schema=1, scope='Listed local collector/navigation declarations only; full LRX OPEN',
        lean_version=version, lean_binary_sha256=sha(lean),
        child_limits=dict(cpu_seconds=10,address_space_bytes=1024**3,wall_seconds=15,threads=1),
        inputs_before=before, phases=[], axioms={}, success=False)
    started=time.monotonic()
    try:
        for name in MODULES:
            source=root/(name+'.lean')
            if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s',source.read_text(),re.M):
                raise RuntimeError('Disallowed source marker in '+source.name)
            argv=[str(lean),'-j1','-o',str(build/(name+'.olean')),source.name]
            phase=dict(module=name,command=['lean','-j1','-o','build/'+name+'.olean',source.name])
            report['phases'].append(phase)
            with (out/(name+'.stdout.log')).open('wb') as stdout, (out/(name+'.stderr.log')).open('wb') as stderr:
                completed=subprocess.run(argv,cwd=root,env=child_env,stdout=stdout,stderr=stderr,
                    timeout=15,preexec_fn=child_limits,check=False)
            phase.update(returncode=completed.returncode,
                stdout_sha256=sha(out/(name+'.stdout.log')),stderr_sha256=sha(out/(name+'.stderr.log')))
            if completed.returncode:
                raise RuntimeError('Lean failed in '+name)
            phase['olean_sha256']=sha(build/(name+'.olean'))
            output=(out/(name+'.stdout.log')).read_text()
            for declaration,raw in AXIOMS.findall(output):
                if declaration in report['axioms']:
                    raise RuntimeError('Duplicate audit '+declaration)
                axioms=[item.strip() for item in raw.split(',') if item.strip()]
                if set(axioms)-ALLOWED:
                    raise RuntimeError('Unexpected axioms for '+declaration+': '+str(axioms))
                report['axioms'][declaration]=axioms
        if set(report['axioms']) != set(expected):
            raise RuntimeError('Audit declarations differ from the explicit expected list')
        report['inputs_after']={name:sha(root/name) for name in inputs}
        if before != report['inputs_after']:
            raise RuntimeError('Selected sources changed during replay')
        report['success']=True
    except Exception as exc:
        report['error']=type(exc).__name__+': '+str(exc)
    finally:
        report['elapsed_seconds']=time.monotonic()-started
        (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(success=report['success'],modules=len(report['phases']),
        audited_declarations=len(report['axioms']),scope=report['scope']),indent=2))
    if not report['success']:
        raise SystemExit(1)

if __name__=='__main__':
    main()
