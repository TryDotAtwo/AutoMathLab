#!/usr/bin/env python3
"""Dependency-free finite checks; this is not a universal theorem prover."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]

def replay(n,u,w):
    p=list(range(n));C=u;r=0;history=[]
    def snapshot():
        c,h=C%n,C//n
        z=[p.index(x) for x in range(n)]
        return (p[:],C,r,[q-int(q>c)+h for q in z])
    history.append(snapshot())
    for op in w:
        c=C%n
        if op=='L':C+=1;r+=1
        elif op=='R':C-=1;r+=1
        else:
            assert op=='X'
            p[c],p[(c+1)%n]=p[(c+1)%n],p[c]
        history.append(snapshot())
    return history

def visible(n,w):
    p=list(range(n))
    for op in w:
        if op=='L':p=p[1:]+p[:1]
        elif op=='R':p=p[-1:]+p[:-1]
        else:p[0],p[1]=p[1],p[0]
    return p

def local(row):
    j,u,w=row['j'],row['u'],row['word'];hist=replay(j,u,w)
    for k,op in enumerate(w):
        if op=='X':assert hist[k][1]%j!=j-1
        delta=[b-a for a,b in zip(hist[k][3],hist[k+1][3])]
        assert sum(map(abs,delta))==int(op!='X')
    p,C,r,F=hist[-1]
    assert p==list(range(j-1,-1,-1)) and C%j==(j-2-u)%j
    outside=[s for s in hist if s[1]%j==j-1];assert outside
    Z=hist[0][3]
    if u==j-1:
        assert r>=sum(abs(a-b) for a,b in zip(F,Z))>=j*j//2
    else:
        assert len({a+b for a,b in zip(Z,F)})==1
        for _,_,cost,P in outside:
            A=[a-b for a,b in zip(P,Z)];B=[a-b for a,b in zip(F,P)]
            assert cost>=sum(map(abs,A)) and r-cost>=sum(map(abs,B))
            assert r>=sum(map(abs,A))+sum(map(abs,B))>=sum(abs(a-b) for a,b in zip(A,B))>=j*j//2
    return {'j':j,'u':u,'rotations':r,'outside_states':len(outside)}

def global_trace(row):
    a,b,u,w=(row[k] for k in ('a','b','u','word'));n=a+b
    hist=replay(n,u,w);p,C,r,_=hist[-1]
    assert p==list(range(a-1,-1,-1))+list(range(n-1,a-1,-1))
    assert C%n==(a-2-u)%n and visible(n,w)==[(1-i)%n for i in range(n)]
    pairs=[]
    for k,op in enumerate(w):
        if op=='X':
            state,c,_,_=hist[k];c%=n
            assert c not in (a-1,n-1)
            pairs.append(tuple(sorted((state[c],state[c+1]))))
    M=a*(a-1)//2+b*(b-1)//2
    assert len(pairs)==len(set(pairs))==M
    assert len(w)>=n*(n-1)//2
    if min(a,b)>=2:assert r>=M+n//2
    return {'n':n,'a':a,'b':b,'u':u,'rotations':r,'exchanges':M,'length':len(w)}

def main():
    source=ROOT/'data/traces.json';data=json.loads(source.read_text())
    result={'status':'PASS','global_traces':[global_trace(r) for r in data['global_traces']],
            'local_traces':[local(r) for r in data['local_traces']],
            'data_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
            'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Finite explicit-word and coordinate checks only; no BFS, no external arrays, no Lean claim.'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
