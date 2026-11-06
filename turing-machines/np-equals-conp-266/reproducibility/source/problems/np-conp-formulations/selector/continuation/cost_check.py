"""Independent literal accounting and complete state-map partition.

This checker imports no compiler or table emitter. It verifies both exact
quotient maps on every row, the event shift, and every named-state category.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json

HERE=Path(__file__).resolve().parent

def table(path,event=False):
    headers={};rows={}
    for line in Path(path).read_text().splitlines():
        if line.startswith('#!'):
            key,value=line[2:].strip().split(' ',1);headers[key]=value;continue
        if not line.strip():continue
        fields=line.split();assert len(fields)==(6 if event else 5)
        q,r,w=int(fields[0]),int(fields[1]),int(fields[2]);move=fields[3];target=int(fields[4])
        mark=int(fields[5]) if event else int(q==int(headers['beep']))
        assert r in (0,1) and w in (0,1) and mark in (0,1) and move in ('L','R')
        assert (q,r) not in rows;rows[q,r]=(w,move,target,mark)
    count=int(headers['states']);assert count>0
    assert set(rows)=={(q,r) for q in range(count) for r in (0,1)}
    assert all(0<=v[2]<count for v in rows.values())
    assert headers['start']==headers['blank']==headers['head']=='0'
    return count,rows

def category(name):
    if name.startswith('shared.selector.'):return 'shared selector and bootstrap adapter'
    if name.startswith('0a.boot1.'):return 'blank bootstrap'
    if name in ('B','beep'):return 'event adapter'
    if name.startswith('3.'):return 'register operation entries'
    if name=='silent.sink':return 'totalization'
    if name[0].isdigit():return 'remaining engine and dispatch'
    return 'compiled arithmetic and control'

def check(directory):
    d=Path(directory);raw_count,raw=table(d/'raw.tm');b_count,parent=table(d/'machine.tm')
    event_count,event=table(d/'events.tm',True);ingress_count,ingress=table(d/'ingress-prequotient.tm',True)
    q=json.loads((d/'quotient.json').read_text());em=json.loads((d/'event-quotient.json').read_text());event_map=em['mapping']
    def lookup(mapping,key):return mapping[key] if isinstance(mapping,list) else mapping[str(key)]
    assert len(q)==raw_count and len(event_map)==b_count
    assert {lookup(q,i) for i in range(raw_count)}==set(range(b_count))
    assert {lookup(event_map,i) for i in range(b_count)}==set(range(event_count))
    for (s,r),(w,m,t,e) in raw.items():assert parent[lookup(q,s),r]==(w,m,lookup(q,t),e)
    assert ingress_count==b_count and em['time_shift']==-1 and em['source_B']!=0
    for (s,r),(w,m,t,e) in parent.items():
        mark=int(t==em['source_B']);assert ingress[s,r]==(w,m,t,mark)
        assert event[lookup(event_map,s),r]==(w,m,lookup(event_map,t),mark)
    assert lookup(q,0)==lookup(event_map,0)==0
    names=json.loads((d/'names.json').read_text());assert set(names.values())==set(range(raw_count))
    groups={};egroups={}
    for name,state in names.items():
        target=lookup(q,state);groups.setdefault(target,set()).add(category(name))
        egroups.setdefault(lookup(event_map,target),set()).add(category(name))
    profile=dict(sorted(Counter(' + '.join(sorted(v)) for v in groups.values()).items()))
    event_profile=dict(sorted(Counter(' + '.join(sorted(v)) for v in egroups.values()).items()))
    metadata=json.loads((d/'metadata.json').read_text())
    assert profile==metadata['profile'] and sum(profile.values())==b_count
    assert sum(event_profile.values())==event_count and metadata['halt_states_excluded']==0
    h=lambda p:hashlib.sha256((d/p).read_bytes()).hexdigest()
    assert em['source_table_sha256']==h('machine.tm') and em['predecessor_sha256']==h('ingress-prequotient.tm') and em['result_sha256']==h('events.tm')
    return {'raw_states':raw_count,'B_exit_states':b_count,'event_states':event_count,
            'raw_rows':len(raw),'B_exit_rows':len(parent),'event_rows':len(event),
            'raw_sha256':h('raw.tm'),'B_exit_sha256':h('machine.tm'),'event_sha256':h('events.tm'),
            'B_exit_partition':profile,'event_partition':event_profile,
            'marked_rows':[[s,r,*v] for (s,r),v in sorted(event.items()) if v[3]],
            'scope':'independent literal parsing, complete row correspondences and disjoint physical partition'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--directory',type=Path,default=HERE/'machines/selected');p.add_argument('--out',type=Path);p.add_argument('--check',type=Path);a=p.parse_args()
    result=check(a.directory)
    if a.out:a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    if a.check:assert result==json.loads(a.check.read_text())
    print(json.dumps(result,indent=2))
