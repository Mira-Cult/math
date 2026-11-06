"""Verify the complete table, selected proof checks, and optional literal prefix."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
C=ROOT/'reproducibility/source/problems/np-conp-formulations/selector/continuation/compact'
H=C/'control_regions';M=H/'machines/reuse_clock_roles_zero_geometry';V=H/'machines/reuse_clock_roles_zero_geometry_selected'

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def source_manifest():
    spec=importlib.util.spec_from_file_location('public_reproduction',ROOT/'reproducibility/reproduce.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod.verify_sources()

def table(path,states,marked):
    headers={};rows={}
    for line in path.read_text().splitlines():
        if line.startswith('#!'):
            k,_,v=line[2:].strip().partition(' ');headers[k]=v;continue
        if not line.strip():continue
        parts=line.split();assert len(parts)==(6 if marked else 5)
        q,b,w,d,t=int(parts[0]),int(parts[1]),int(parts[2]),parts[3],int(parts[4]);m=int(parts[5]) if marked else 0
        assert 0<=q<states and b in (0,1) and w in (0,1) and d in ('L','R') and 0<=t<states and m in (0,1)
        assert (q,b) not in rows;rows[q,b]=(w,d,t,m)
    assert set(rows)=={(q,b) for q in range(states) for b in (0,1)}
    assert headers['states']==str(states) and headers['start']==headers['blank']==headers['head']=='0'
    if marked:assert [(q,b,*r) for (q,b),r in rows.items() if r[3]]==[(104,1,0,'L',1,1)]
    else:assert headers['beep']=='1'
    return {'states':states,'rows':len(rows),'sha256':sha(path)}

def checks(out):
    configs={
     'source':['review/source/check_source.py','--source',H/'sources/reuse_clock_roles.py','--reference',C/'phase_swap/source.py'],
     'control':['review/source/check_control.py','--folder',M],
     'regions':['review/source/check_regions.py','--parent',M,'--source',H/'sources/reuse_clock_roles.py'],
     'static':['review/physical/check_static.py','--parent',M,'--selected',V,'--plan',H/'plans/reuse_clock_roles_zero_geometry/completion.json','--source',H/'sources/reuse_clock_roles.py'],
     'rows':['review/physical/check_rows.py','--parent',M,'--selected',V],
     'fixtures':['review/physical/check_fixtures.py','--parent',M,'--selected',V]}
    result={}
    for name,args in configs.items():
        target=out/(name+'.json');cmd=[sys.executable,'-B',str(H/args[0]),*map(str,args[1:]),'--out',str(target)]
        subprocess.run(cmd,check=True,capture_output=True,text=True)
        result[name]=json.loads(target.read_text())
    return result

def literal(out):
    binaries={}
    for name,compiler,standard,suffix in [('deque','c++','c++17','cpp'),('bitset','cc','c11','c')]:
        binary=out/name
        subprocess.run([compiler,'-std='+standard,'-O2',str(ROOT/f'reproducibility/literal_{name}.{suffix}'),'-o',str(binary)],check=True,capture_output=True,text=True)
        binaries[name]=binary
    result={};limit=112620826
    for name,expected in [('events',[89844341,99174101,112620825]),('machine',[89844342,99174102,112620826])]:
        values=[]
        for binary in binaries.values():
            value=json.loads(subprocess.check_output([str(binary),str(ROOT/(name+'.tm')),str(limit)],text=True));values.append(value)
        assert values[0]==values[1],('complete literal configuration disagreement',name)
        value=values[0];assert value['events']==expected
        result[name]={'steps':limit,'events':value['events'],'state':value['state'],'head':value['head'],'one_cells':len(value['ones']),
                      'complete_configuration_sha256':hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
                      'engines_agree_on_all_one_cells':True}
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--literal',action='store_true');p.add_argument('--quick',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args()
    manifest=source_manifest()
    result={'format':'np-conp-266-public-verification-v1','exported_source_files_verified':len(manifest['files']),
            'source_manifest_sha256':sha(ROOT/'SOURCE_MANIFEST.json'),'wrapper_sha256':sha(__file__),
            'python_version':sys.version.split()[0],
            'tables':{'marked':table(ROOT/'events.tm',266,True),'B_exit':table(ROOT/'machine.tm',267,False)},
            'status':'passed','scope':'Finite reproducibility, source/control/certificate checks and optional literal prefix; not a Lean theorem, new independent review, or decision of eventual silence.'}
    assert (ROOT/'events.tm').read_bytes()==(V/'events.tm').read_bytes()
    assert (ROOT/'machine.tm').read_bytes()==(V/'machine.tm').read_bytes()
    with tempfile.TemporaryDirectory(prefix='npconp266-check-') as tmp:
        out=Path(tmp)
        result['checks']='not run (--quick)' if a.quick else checks(out)
        result['literal']=literal(out) if a.literal else 'not run (add --literal)'
    if a.receipt:a.receipt.parent.mkdir(parents=True,exist_ok=True);a.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
