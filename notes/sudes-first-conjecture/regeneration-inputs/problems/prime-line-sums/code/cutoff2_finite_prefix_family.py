#!/usr/bin/env python3
"""Exact replay of a bounded finite prime-pair population family."""
from pathlib import Path
from fractions import Fraction as F
from array import array
from math import isqrt
from bisect import bisect_right,bisect_left
from functools import lru_cache
import json,hashlib,sys,subprocess,shutil,tempfile,csv,importlib.util,copy
ROOT=Path(__file__).resolve().parent.parent
SELF='code/cutoff2_finite_prefix_family.py';CPP='code/cutoff2_finite_prefix_family_generator.cpp'
INPUT=ROOT/'inputs/cutoff2_finite_prefix_family_inputs.json'
SOURCES={'PROBLEM.md': '9632c547445ed661a5df4ccfdc14892a0aeaf3ed108203c08bf075df8720c023',
 'code/cutoff2_finite_prefix_family_generator.cpp': '9deb0fa9a0f598fbc8db8f0fde415ac0fc9959c21141cac96ad8433327d61e76',
 'code/cutoff2_finite_prefix_population.py': '7e2a6c48e738a5225498f11ea0d7746829fd50f43e86403e8e2d307b1c4420ca',
 'inputs/cutoff2_finite_prefix_population_inputs.json': 'fda6651da4941ae8df019d9090efe98c47ceb6b0d3b84ac21641df990e01ff3f',
 'manuscripts/cutoff2_finite_prefix_family.md': 'd0578448c722d6af1e894f0d3b751d46cd1b1c9a4edd5188c748b108e8dd5eee',
 'manuscripts/cutoff2_finite_prefix_population.md': '468c71cd24241422fe6cf6e38ce2f61e0a1d5179dbd4e72fc2c667d42527eba4',
 'manuscripts/cutoff2_prefix_balance_experiment.md': 'efca80ca4c0c5b470cd46e90b736e54143b1337b7aadf2593f820570e626f395'}
SCHEMA='sude-finite-prefix-family-v1'
CASES=[['L',2000,2400,60000000,14448,24,13000000,55000000,3562114],
 ['C27',2400,3000,95000000,18048,24,27000000,74000000,5489748],
 ['M',3000,5000,150000000,30048,26,44,150000000,8444395],
 ['H',5000,10000,450000000,60048,28,44,450000000,23853037],
 ['T',10000,19483,1800000000,116946,30,44,1800000000,88862421]]
FIELDS=['name','order_min','order_max','bound','pairs_per_stage','stages','lower','upper','odd_prime_count']
SCOPE='Finite disjoint common-gap populations and conditional allocation for integer orders2000..19483; no square or infinite-tail theorem.'

def require(ok,label):
 if not ok:raise ValueError(label)

def parse_json(text):
 def pairs(items):
  out={}
  for k,v in items:require(k not in out,'duplicate JSON key');out[k]=v
  return out
 def bad(x):raise ValueError('nonfinite JSON value')
 return json.loads(text,object_pairs_hook=pairs,parse_constant=bad)

def default_bindings():return dict(SOURCES,**{SELF:hashlib.sha256((ROOT/SELF).read_bytes()).hexdigest()})

def source_check(bindings,root=ROOT):
 require(type(bindings) is dict and bool(SOURCES) and set(bindings)==set(SOURCES)|{SELF},'complete exact nonempty source map')
 for ancestor in (root,*root.parents):require(not ancestor.is_symlink(),'source root ancestor symlink')
 for name in sorted(bindings):
  h=bindings[name];require(type(h) is str and len(h)==64 and all(c in '0123456789abcdef' for c in h),'malformed digest')
  if name!=SELF:require(h==SOURCES[name],'canonical source digest')
  p=root
  for part in Path(name).parts:p/=part;require(not p.is_symlink(),'source ancestor symlink')
  require(p.is_file(),'missing or nonregular source');raw=p.read_bytes();require(bool(raw),'empty source')
  require(hashlib.sha256(raw).hexdigest()==h,'source content mismatch')
 for name in SOURCES:
  if name.startswith('inputs/') and name.endswith('_inputs.json'):
   sub=parse_json((root/name).read_text());src=sub.get('sources',sub.get('required_sources'))
   require(type(src) is dict and bool(src),'nonempty public helper map')
   for p,h in src.items():require(p in bindings and bindings[p]==h,'complete unchanged public helper closure')

def manifest(path=INPUT):
 require(path.is_file() and not path.is_symlink(),'regular input manifest');raw=path.read_bytes();require(bool(raw),'nonempty input manifest')
 data=parse_json(raw.decode());require(type(data) is dict and set(data)=={'schema','scope','profiles','sources'},'complete manifest fields')
 require(data['schema']==SCHEMA and data['scope']==SCOPE,'canonical source schema and scope');source_check(data['sources'])
 require(type(data['profiles']) is list and len(data['profiles'])==5,'all five finite profiles')
 for expected,row in zip(CASES,data['profiles']):
  require(type(row) is dict and set(row)==set(FIELDS)|{'rows','stream_sha256','csv_sha256'},'complete profile fields')
  for k,v in zip(FIELDS,expected):require(type(row[k]) is type(v) and row[k]==v,'canonical exact profile parameter '+k)
  for key in('stream_sha256','csv_sha256'):
   h=row[key];require(type(h) is str and len(h)==64 and all(c in '0123456789abcdef' for c in h),'canonical stream/transcript digest')
 return data

def compile_source(temp):
 compiler=shutil.which('g++') or shutil.which('clang++');require(compiler is not None,'public C++17 compiler required')
 binary=Path(temp)/'finite_prefix_family';result=subprocess.run([compiler,'-O3','-std=c++17','-Wall','-Wextra',str(ROOT/CPP),'-o',str(binary)],capture_output=True,text=True)
 require(result.returncode==0,'pinned finite population source compiles: '+result.stderr[:1000]);return binary

def strict_rows(text):
 rows=[]
 names=['stage','gap','candidates','chosen_start','first_lower','last_lower','width','sum_lower','min_upper','max_upper','retained']
 reader=csv.DictReader(text.splitlines());require(reader.fieldnames==names,'exact transcript header')
 for row in reader:
  require(set(row)==set(names) and all(type(v) is str and v.isascii() and v.isdecimal() and str(int(v))==v for v in row.values()),'exact transcript integer fields')
  rows.append({k:int(v) for k,v in row.items()})
 return rows

def stream_verify(spec,rows,raw):
 P,Q=spec['stages'],spec['pairs_per_stage'];require(type(raw) is bytes and len(raw)==4*P*Q,'complete declared endpoint stream')
 require(hashlib.sha256(raw).hexdigest()==spec['stream_sha256'],'exact retained stream identity')
 values=array('I');require(values.itemsize==4,'four-byte unsigned integer decoder');values.frombytes(raw)
 if sys.byteorder!='little':values.byteswap()
 require(type(rows) is list and len(rows)==P and rows==spec['rows'],'every exact stage transcript row')
 kept=[];entries=[];coverage=0;checks=0
 for j,row in enumerate(rows):
  require(type(row) is dict and all(type(x) is int for x in row.values()),'exact stage metadata types')
  h=1<<(j+1);seq=values[j*Q:(j+1)*Q]
  require(row['stage']==j and row['gap']==h and row['retained']==Q and row['candidates']>=Q and 0<=row['chosen_start']<=row['candidates']-Q,'full finite stage candidate/cardinality metadata')
  require(seq[0]>=spec['lower'] and seq[-1]+h<=spec['upper']<=spec['bound'] and seq[0]>43,'actual endpoint and screening bounds')
  require(all(p%2==1 and p<q for p,q in zip(seq,seq[1:])) and seq[-1]%2==1,'strict ordered odd lower endpoints')
  require(row['first_lower']==seq[0] and row['last_lower']==seq[-1] and row['width']==seq[-1]-seq[0] and row['sum_lower']==sum(seq),'exact stage range and sum')
  require(row['min_upper']==seq[0]+h and row['max_upper']==seq[-1]+h,'exact upper endpoint bounds')
  require(h==coverage+2,'complete even-grid induction including initial stage');coverage+=h
  kept.append(seq);entries.extend(seq);entries.extend(p+h for p in seq);checks+=7
 entries.sort();require(all(a<b for a,b in zip(entries,entries[1:])),'complete cross-stage vertex disjointness');checks+=1
 require(coverage==(1<<(P+1))-2,'exact final complete even-grid radius');checks+=1
 return kept,{'stages':P,'pairs_per_stage':Q,'coverage':coverage,'retained_entries':2*P*Q,'stream_sha256':spec['stream_sha256'],'semantic_controls':checks}

def run_generator(binary,temp,spec):
 stem=Path(temp)/spec['name'];args=[str(binary),str(stem),str(spec['bound']),str(spec['pairs_per_stage']),str(spec['stages']),str(spec['lower']),str(spec['upper'])]
 result=subprocess.run(args,capture_output=True,text=True);require(result.returncode==0,'complete finite population enumeration: '+result.stderr[-1000:])
 logs=result.stderr.splitlines();require(bool(logs) and logs[0]=='odd primes='+str(spec['odd_prime_count']),'complete exact odd-prime count')
 require(spec['odd_prime_count']<=spec['order_min']**2 and spec['pairs_per_stage']==6*(spec['order_max']+8),'every endpoint in every prescribed band input pool')
 transcript=stem.with_suffix('.csv').read_bytes();require(hashlib.sha256(transcript).hexdigest()==spec['csv_sha256'],'complete stage transcript identity')
 kept,summary=stream_verify(spec,strict_rows(transcript.decode()),stem.with_suffix('.bin').read_bytes())
 summary.update(name=spec['name'],order_min=spec['order_min'],order_max=spec['order_max'],bound=spec['bound'],odd_prime_count=spec['odd_prime_count'])
 return kept,summary

def prime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def small_control(binary,temp):
 B,Q,P=20000,12,6;stem=Path(temp)/'independent_small';result=subprocess.run([str(binary),str(stem),str(B),str(Q),str(P),'44',str(B)],capture_output=True,text=True)
 require(result.returncode==0,'independent small finite replay')
 primes=[p for p in range(3,B+1,2) if prime(p)];live={p for p in primes if p>43};kept=[];rows=[]
 for j in range(P):
  h=1<<(j+1);cand=sorted(p for p in live if p+h in live)
  start=min(range(len(cand)-Q+1),key=lambda i:cand[i+Q-1]-cand[i]);seq=cand[start:start+Q]
  require(len({x for p in cand for x in(p,p+h)})==2*len(cand),'all power-gap candidates already a matching')
  kept.extend(seq);live.difference_update(seq);live.difference_update(p+h for p in seq)
  rows.append({'stage':j,'gap':h,'candidates':len(cand),'chosen_start':start,'first_lower':seq[0],'last_lower':seq[-1],'width':seq[-1]-seq[0],'sum_lower':sum(seq),'min_upper':seq[0]+h,'max_upper':seq[-1]+h,'retained':Q})
 require(strict_rows(stem.with_suffix('.csv').read_text())==rows,'independent complete trial-prime stage selection')
 raw=b''.join(p.to_bytes(4,'little') for p in kept);require(stem.with_suffix('.bin').read_bytes()==raw,'independent selected stream')
 return {'bound':B,'stages':P,'pairs_per_stage':Q,'selected_pairs':len(kept),'independent_trial_prime_count':len(primes)+1}

def prepare(kept,spec):
 sums=[]
 for seq in kept:
  row=array('Q',[0]);v=0
  for p in seq:v+=p;require(v<1<<64,'finite prefix-sum integer range');row.append(v)
  sums.append(row)
 return {'spec':spec,'kept':kept,'prefix_sums':sums,'gaps':[1<<(j+1) for j in range(len(kept))]}

def order_data(pop,n):
 spec=pop['spec'];require(type(n) is int and spec['order_min']<=n<=spec['order_max'],'actual integer order in its declared population band')
 Q=6*(n+8);require(Q<=spec['pairs_per_stage'],'every actual Q truncation paid')
 ranges=[seq[Q-1]-seq[0] for seq in pop['kept']];means=[F(row[Q],Q)+F(h,2) for row,h in zip(pop['prefix_sums'],pop['gaps'])]
 total=sum(2*row[Q]+Q*h for row,h in zip(pop['prefix_sums'],pop['gaps']))
 require(total==2*Q*sum(means,F()),'exact original retained mean identity')
 return {'n':n,'Q':Q,'P':len(ranges),'reserved_entries':2*Q*len(ranges),'variance':18*sum(w*w for w in ranges)+4*max(ranges)**2,
  'max_range':max(ranges),'sum_stage_means':sum(means,F()),'min_stage_mean':min(means),'max_stage_mean':max(means),'prefix_prime_sum':total,'coverage':sum(pop['gaps'])}

def protected_interval_count(pop,n,left,right):
 require(type(left) in(int,F) and type(right) in(int,F) and left<=right,'exact rational protected interval')
 Q=6*(n+8);require(pop['spec']['order_min']<=n<=pop['spec']['order_max'] and Q<=pop['spec']['pairs_per_stage'],'protected actual order')
 count=0
 for seq,h in zip(pop['kept'],pop['gaps']):
  for shift in(0,h):count+=bisect_right(seq,right-shift,0,Q)-bisect_right(seq,left-shift,0,Q)
 return count

@lru_cache(None)
def populations(path=INPUT):
 data=manifest(Path(path));out={};summaries=[]
 with tempfile.TemporaryDirectory(prefix='sude-finite-prefix-family-') as temp:
  binary=compile_source(temp);control=small_control(binary,temp)
  for spec in data['profiles']:
   kept,summary=run_generator(binary,temp,spec);out[spec['name']]=prepare(kept,spec);summaries.append(summary)
 return out,summaries,control

def reject(action):
 try:action()
 except (ValueError,TypeError,OSError,KeyError,UnicodeError,OverflowError) as err:return str(err)
 raise ValueError('negative control unexpectedly accepted')

def negatives(bindings,pops):
 out={}
 for label,value in [('empty',{}),('list',[]),('null',None)]:out['source_'+label]=reject(lambda value=value:source_check(value))
 for name in bindings:
  bad=dict(bindings);bad.pop(name);out['missing:'+name]=reject(lambda bad=bad:source_check(bad))
 for h in('','x'*64,'0'*64):
  bad=dict(bindings);bad[next(iter(SOURCES))]=h;out['hash:'+h[:4]]=reject(lambda bad=bad:source_check(bad))
 out['extra_source']=reject(lambda:source_check(dict(bindings,unexpected='0'*64)))
 p=pops['L'];n=p['spec']['order_min']
 out['below_band']=reject(lambda:order_data(p,n-1));out['above_band']=reject(lambda:order_data(p,p['spec']['order_max']+1))
 out['boolean_order']=reject(lambda:order_data(p,True));out['reversed_interval']=reject(lambda:protected_interval_count(p,n,F(2),F(1)))
 spec=p['spec'];raw=b''.join(seq.tobytes() if sys.byteorder=='little' else b''.join(x.to_bytes(4,'little') for x in seq) for seq in p['kept'])
 for label,content in [('empty',b''),('truncated',raw[:-4]),('changed',raw[:5]+bytes([raw[5]^1])+raw[6:])]:out['stream_'+label]=reject(lambda content=content:stream_verify(spec,spec['rows'],content))
 for key in('candidates','gap','sum_lower','retained'):
  rows=copy.deepcopy(spec['rows']);rows[0][key]+=1;out['row_'+key]=reject(lambda rows=rows:stream_verify(spec,rows,raw))
 for label,text in [('empty',''),('duplicate','{"a":1,"a":2}'),('malformed','{'),('nonfinite','{"a":NaN}')]:out['json_'+label]=reject(lambda text=text:parse_json(text))
 return out

def physical_attacks(bindings):
 attacks=0
 with tempfile.TemporaryDirectory(prefix='sude-prefix-family-source-attacks-') as temp:
  root=Path(temp)
  for name in bindings:
   p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((ROOT/name).read_bytes())
  for name in bindings:
   p=root/name;raw=p.read_bytes()
   for kind in('missing','empty','changed','directory','symlink'):
    p.unlink()
    if kind=='empty':p.write_bytes(b'')
    elif kind=='changed':p.write_bytes(raw+b'\nchanged\n')
    elif kind=='directory':p.mkdir()
    elif kind=='symlink':p.symlink_to(ROOT/name)
    reject(lambda:source_check(bindings,root));attacks+=1
    if p.is_file() or p.is_symlink():p.unlink()
    elif p.is_dir():p.rmdir()
    p.write_bytes(raw)
 return attacks

def run(path=INPUT):
 require(__debug__,'ordinary exact execution');data=manifest(path)
 pops,summaries,control=populations(path);orders=[];checks=0
 for name,pop in pops.items():
  previous=0;digest=hashlib.sha256();first=last=None
  for n in range(pop['spec']['order_min'],pop['spec']['order_max']+1):
   row=order_data(pop,n);require(row['variance']>=previous,'all integer truncation ranges and variance monotone');previous=row['variance']
   serial={k:str(v) if type(v) is F else v for k,v in row.items()};digest.update((json.dumps(serial,sort_keys=True,separators=(',',':'))+'\n').encode())
   if first is None:first=serial
   last=serial;checks+=1
  orders.append({'name':name,'integer_orders':pop['spec']['order_max']-pop['spec']['order_min']+1,'order_table_sha256':digest.hexdigest(),'first':first,'last':last})
 return {'status':'PASS_FINITE_PREFIX_FAMILY','scope':SCOPE,'profiles':summaries,'all_order_tables':orders,
  'integer_order_controls':checks,'independent_trial_fixture':control,'negative_controls':negatives(data['sources'],pops),
  'physical_source_attacks':physical_attacks(data['sources']),'source_bindings':data['sources'],
  'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'square_cutoff_claimed':False,'formal_kernel_verification':False}
if __name__=='__main__':
 require(len(sys.argv)<=2,'at most one input manifest')
 print(json.dumps(run(Path(sys.argv[1]) if len(sys.argv)==2 else INPUT),indent=2,sort_keys=True))
