#!/usr/bin/env python3
"""Check exact published baseline; optionally rebuild in an isolated temporary directory.
No downloads, no modification of historical sources/logs, no public messages.
"""
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check_logs(text, expected):
    assert 'error:' not in text and 'sorryAx' not in text
    reported = re.findall(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", text, re.S)
    assert len(reported) == len(expected), (len(reported), len(expected))
    assert {n.rsplit('.',1)[-1] for n,_ in reported} == set(expected)
    axioms = {a.strip() for _,group in reported for a in group.split(',') if a.strip()}
    assert axioms <= ALLOWED, axioms
    return sorted(axioms)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--build',action='store_true')
    ap.add_argument('--packages',type=Path);ap.add_argument('--lean-bin',type=Path)
    ap.add_argument('--output',type=Path);args=ap.parse_args()
    manifest=json.loads((ROOT/'SOURCE_MANIFEST.json').read_text())
    for e in manifest['files']:
        p=ROOT/e['path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'], e['path']
    receipt=json.loads((ROOT/'BUILD_RECEIPT.json').read_text())
    theorems=json.loads((ROOT/'THEOREMS.json').read_text()); assert len(theorems)==29
    for m in receipt['modules']:
        source=ROOT/'formal/LRX'/(m['module']+'.lean'); text=source.read_text()
        assert sha(source)==m['source_sha256'] and sha(ROOT/m['log'])==m['log_sha256']
        assert m['exit_code']==0 and m['passed']
        assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|decide\s+\+native',text)
        expected=re.findall(r'^#print axioms (\S+)',text,re.M)
        check_logs((ROOT/m['log']).read_text(), expected)
        for imp in re.findall(r'^import (\S+)',text,re.M):
            assert imp.startswith(('Mathlib.', 'LRX.')), imp
    print('Integrity PASS: 8 modules; 29 matching historical axiom reports. This is not a fresh Lean build.')
    if not args.build:return
    assert args.output, '--build requires --output OUTSIDE this published package'
    out=args.output.resolve(); assert out!=ROOT and ROOT not in out.parents
    out.mkdir(parents=True,exist_ok=False)
    packages=(args.packages or ROOT/'formal/.lake/packages').resolve();assert packages.is_dir()
    lock=json.loads((ROOT/'formal/lake-manifest.json').read_text())
    for pkg in lock['packages']:
        got=subprocess.check_output(['git','-C',str(packages/pkg['name']),'rev-parse','HEAD'],text=True).strip()
        assert got==pkg['rev'], (pkg['name'],got,pkg['rev'])
    env=os.environ.copy()
    if args.lean_bin:env['PATH']=str(args.lean_bin.resolve())+os.pathsep+env['PATH']
    version=subprocess.check_output(['lean','--version'],env=env,text=True).strip();assert 'version 4.34.0,' in version,version
    result={'lean_version':version,'modules':[]}
    with tempfile.TemporaryDirectory(prefix='lrx-b-baseline-') as tmp:
        formal=Path(tmp)/'formal';shutil.copytree(ROOT/'formal',formal,ignore=shutil.ignore_patterns('.lake'))
        (formal/'.lake').mkdir();(formal/'.lake/packages').symlink_to(packages,target_is_directory=True)
        dest=formal/'.lake/build/lib/lean/LRX';dest.mkdir(parents=True)
        for m in receipt['modules']:
            name=m['module'];cmd=['lake','env','lean','-j','1','-o',str(dest/(name+'.olean')),'LRX/'+name+'.lean']
            log=out/(name+'.log')
            with log.open('w') as f:r=subprocess.run(cmd,cwd=formal,env=env,stdout=f,stderr=subprocess.STDOUT)
            assert r.returncode==0,(name,r.returncode)
            expected=re.findall(r'^#print axioms (\S+)',(formal/'LRX'/(name+'.lean')).read_text(),re.M)
            ax=check_logs(log.read_text(),expected)
            result['modules'].append({'name':name,'command':cmd,'exit_code':0,'axioms':ax,'source_sha256':m['source_sha256'],'log_sha256':sha(log)})
        with (out/'LRX.log').open('w') as f:r=subprocess.run(['lake','env','lean','LRX.lean'],cwd=formal,env=env,stdout=f,stderr=subprocess.STDOUT)
        assert r.returncode==0
    result['status']='passed';(out/'BUILD_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Fresh Lean build PASS; receipt at',out)
if __name__=='__main__':main()
