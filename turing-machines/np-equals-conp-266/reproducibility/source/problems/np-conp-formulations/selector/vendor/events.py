"""Complete binary tables with transition-labelled events.

Time zero is the blank initial configuration. Row flag one emits on applying
that row, so the first possible physical event is transition one. This module
imports no compiler. Legacy state-exit tables are a checked special case.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path


@dataclass
class Table:
    start: int
    rows: dict

    @property
    def count(self):
        return len(self.rows)//2


def validate(m):
    n=m.count
    if n<1 or type(m.start) is not int or not 0<=m.start<n:
        raise ValueError('bad start/count')
    if set(m.rows)!={(q,b) for q in range(n) for b in (0,1)}:
        raise ValueError('not a total contiguous binary table')
    if any(not isinstance(key,tuple) or len(key)!=2 or
           any(type(v) is not int for v in key) for key in m.rows):
        raise ValueError('noninteger state or read bit')
    for w,d,t,e in m.rows.values():
        if any(type(v) is not int for v in (w,d,t,e)) or w not in (0,1) or d not in (-1,1) or not 0<=t<n or e not in (0,1):
            raise ValueError('invalid write/move/target/event')
    return m


def natural(text):
    if not text.isdecimal() or str(int(text))!=text:
        raise ValueError('noncanonical natural number')
    return int(text)


def parse(path):
    headers={}; raw=[]
    for line in Path(path).read_text().splitlines():
        if not line or line=='#' or line.startswith('# '):
            continue
        fields=line.split()
        if not fields:
            raise ValueError('blank whitespace row')
        if fields[0]=='#!':
            if len(fields)!=3 or fields[1] in headers:
                raise ValueError('bad/duplicate header')
            headers[fields[1]]=fields[2]
        else:
            raw.append(fields)
    kind=headers.get('format')
    legacy=kind=='beeper-v1'
    required={'format','states','start','blank','head'}|({'beep'} if legacy else set())
    if set(headers)!=required or kind not in ('beeper-v1','beeper-events-v1'):
        raise ValueError('unknown/missing table convention')
    if headers['blank']!='0' or headers['head']!='0':
        raise ValueError('expected blank zero/head zero')
    n=natural(headers['states']); start=natural(headers['start'])
    B=natural(headers['beep']) if legacy else None
    if legacy and not 0<=B<n:
        raise ValueError('invalid B')
    rows={}
    for f in raw:
        if len(f)!=(5 if legacy else 6):
            raise ValueError('wrong row width')
        q,b,w,d,t=f[:5]
        if b not in ('0','1') or w not in ('0','1') or d not in ('L','R'):
            raise ValueError('invalid binary action')
        q=natural(q); target=natural(t)
        e=int(q==B) if legacy else natural(f[5])
        key=(q,int(b))
        if key in rows:
            raise ValueError('duplicate row')
        rows[key]=(int(w),-1 if d=='L' else 1,target,e)
    m=validate(Table(start,rows))
    if n!=m.count:
        raise ValueError('incorrect counted inventory')
    return m


def emit(m,path):
    validate(m)
    lines=['#! format beeper-events-v1',f'#! states {m.count}',
           f'#! start {m.start}','#! blank 0','#! head 0']
    for (q,b),(w,d,t,e) in sorted(m.rows.items()):
        lines.append(f'{q} {b} {w} {"L" if d<0 else "R"} {t} {int(e)}')
    Path(path).write_text('\n'.join(lines)+'\n')


def from_legacy(m):
    return validate(Table(m.start,{key:(w,d,t,int(key[0]==m.beep))
                                  for key,(w,d,t) in m.rows.items()}))


def check_exit_state(m,B):
    validate(m)
    if not 0<=B<m.count or any(e!=int(q==B) for (q,b),(w,d,t,e) in m.rows.items()):
        raise ValueError('event predicate is not exits from this B')


def ingress(m,B):
    """Shift each B-exit event to the preceding entry, then allow quotienting.

    Totality and start!=B imply a bijection between entry events at t and
    exit events at t+1. No physical action is changed by this first stage.
    """
    check_exit_state(m,B)
    if m.start==B:
        raise ValueError('initial B requires a separate initial-event adapter')
    return Table(m.start,{key:(w,d,t,int(t==B)) for key,(w,d,t,e) in m.rows.items()})


def check_ingress(old,new,B):
    check_exit_state(old,B);validate(new)
    if old.start==B or old.start!=new.start or old.count!=new.count:
        raise ValueError('bad ingress domain')
    for key,(w,d,t,e) in old.rows.items():
        if new.rows[key]!=(w,d,t,int(t==B)):
            raise ValueError('not the claimed event relocation')


def quotient(m):
    """Deterministic exact bisimulation including write, move and row event."""
    validate(m)
    groups=[0]*m.count
    while True:
        keys={}; fresh=[]
        for q in range(m.count):
            signature=tuple((w,d,e,groups[t]) for w,d,t,e in (m.rows[q,0],m.rows[q,1]))
            fresh.append(keys.setdefault(signature,len(keys)))
        if fresh==groups:
            break
        groups=fresh
    start_group=groups[m.start]
    order=[start_group]+[g for g in range(len(set(groups))) if g!=start_group]
    renumber={g:i for i,g in enumerate(order)}
    mapping=[renumber[g] for g in groups]
    rows={}
    for (q,b),(w,d,t,e) in sorted(m.rows.items()):
        key=mapping[q],b; action=w,d,mapping[t],e
        if key in rows and rows[key]!=action:
            raise AssertionError('unstable partition')
        rows[key]=action
    out=validate(Table(mapping[m.start],rows))
    check_quotient(m,out,mapping)
    return out,mapping


def check_quotient(old,new,mapping):
    """Check an explicit map; independent of partition construction."""
    validate(old);validate(new)
    if len(mapping)!=old.count or any(type(q) is not int for q in mapping):
        raise ValueError('bad map domain')
    if set(mapping)!=set(range(new.count)) or mapping[old.start]!=new.start:
        raise ValueError('not a start-preserving surjection')
    for (q,b),(w,d,t,e) in old.rows.items():
        if new.rows[mapping[q],b]!=(w,d,mapping[t],e):
            raise ValueError('quotient changes a physical action or event')


def simulate(m,steps,*,events=None,stop_state=None,initial=None):
    validate(m)
    q,h,tape=(m.start,0,set()) if initial is None else initial
    tape=set(tape);times=[];t=0
    while t<steps and q!=stop_state:
        w,d,target,event=m.rows[q,int(h in tape)]
        if event:
            times.append(t+1)
        if w:tape.add(h)
        else:tape.discard(h)
        h+=d;q=target;t+=1
        if events is not None and len(times)>=events:
            break
    return dict(steps=t,state=q,head=h,ones=sorted(tape),beeps=times)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=('count','run'))
    ap.add_argument('table',type=Path)
    ap.add_argument('--steps',type=int,default=100000)
    ap.add_argument('--events',type=int)
    a=ap.parse_args();m=parse(a.table)
    if a.action=='count':
        result=dict(states=m.count,transitions=len(m.rows),start=m.start,
                    event_rows=[list(k) for k,v in sorted(m.rows.items()) if v[3]],
                    sha256=hashlib.sha256(a.table.read_bytes()).hexdigest())
    else:result=simulate(m,a.steps,events=a.events)
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':main()
