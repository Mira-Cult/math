#!/usr/bin/env python3
"""Exact finite prime-pair count; no all-scale twin-prime assertion."""
from pathlib import Path
from fractions import Fraction as F
from math import isqrt,gcd
import hashlib,json,sys,tempfile,copy
ROOT=Path(__file__).resolve().parent.parent
SELF='code/cutoff2_finite_twin_seed.py'
INPUT=ROOT/'inputs/cutoff2_finite_twin_seed_inputs.json'
SOURCES={'PROBLEM.md': '9632c547445ed661a5df4ccfdc14892a0aeaf3ed108203c08bf075df8720c023',
 'manuscripts/cutoff2_finite_twin_seed.md': '64bd7357fc5ddf417445441ab9d34953df7f456350c9ee664041d1434483ab2a',
 'manuscripts/cutoff2_narrowest_seed.md': 'b70e838ca620130bfee85f4040fec002b709dc91d72c53262242890fd5ef1ac4'}
SCHEMA='sude-finite-twin-seed-v1'
PARAMETERS={'bound':1<<30,'odd_segment_size':1<<20,'lower_endpoint_strictly_above':43,
 'expected_pairs':3650551,'expected_pi':54400028,'expected_first_lower':59,'expected_last_lower':1073741717}
SCOPE='A finite disjoint gap-two matching and a conditional bounded-order seed specialization; no square cutoff or infinite twin-prime claim.'

def require(ok,label):
 if not ok:raise ValueError(label)

def parse_json(text):
 def pairs(rows):
  out={}
  for k,v in rows:require(k not in out,'duplicate JSON key');out[k]=v
  return out
 def bad(value):raise ValueError('nonfinite JSON constant')
 return json.loads(text,object_pairs_hook=pairs,parse_constant=bad)

def source_check(bindings,root=ROOT):
 required=set(SOURCES)|{SELF};require(type(bindings) is dict and bool(SOURCES) and set(bindings)==required,'complete exact nonempty source map')
 for ancestor in (root,*root.parents):require(not ancestor.is_symlink(),'source root ancestor symlink')
 for name in sorted(required):
  digest=bindings[name]
  require(type(digest) is str and len(digest)==64 and all(c in '0123456789abcdef' for c in digest),'malformed source digest')
  if name!=SELF:require(digest==SOURCES[name],'noncanonical source digest')
  p=root
  for part in Path(name).parts:p/=part;require(not p.is_symlink(),'source ancestor symlink')
  require(p.is_file(),'missing or nonregular source');raw=p.read_bytes();require(bool(raw),'empty source')
  require(hashlib.sha256(raw).hexdigest()==digest,'source content mismatch')

def prime(p):return type(p) is int and p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def sieve(bound,slots):
 require(type(bound) is int and 100<=bound<=1<<32 and type(slots) is int and 1<=slots<=1<<22,'exact finite sieve domain')
 root=isqrt(bound);base=bytearray(b'\x01')*(root+1);base[:2]=b'\x00\x00'
 for p in range(2,isqrt(root)+1):
  if base[p]:base[p*p::p]=b'\x00'*((root-p*p)//p+1)
 primes=[p for p in range(3,root+1,2) if base[p]]
 require(all(bool(base[p])==prime(p) for p in range(root+1)),'complete independent base-prime trial division')
 total=0;pi=14;previous=b'';rows=[];first_lower=last_lower=0
 for lo in range(45,bound+1,2*slots):
  size=min(slots,(bound-lo)//2+1);hi=lo+2*(size-1)
  require(lo%2==hi%2==1 and lo>=45 and lo<=hi<=bound,'exact odd segment endpoints')
  if rows:require(lo==rows[-1]['hi']+2,'no segment gap or repetition')
  mask=bytearray(b'\x01')*size
  for p in primes:
   if p*p>hi:break
   start=max(p*p,((lo+p-1)//p)*p)
   if start%2==0:start+=p
   if start<=hi:
    i=(start-lo)//2;length=(size-1-i)//p+1
    require(i>=0 and start%p==0 and start%2==1 and start>=p*p,'composite-only first marking index')
    mask[i::p]=b'\x00'*length
  require(b'\x01\x01\x01' not in mask and b'\x01\x01\x01' not in previous+mask[:2],
          'no overlapping three-prime pattern above3')
  inside=mask.count(b'\x01\x01');boundary=int(bool(previous) and previous[-1]==1 and mask[0]==1)
  pairs=inside+boundary;pc=mask.count(1)
  if pairs:
   first=(lo-2) if boundary else lo+2*mask.find(b'\x01\x01')
   last=lo+2*mask.rfind(b'\x01\x01') if inside else lo-2
   if not first_lower:first_lower=first
   last_lower=last
  total+=pairs;pi+=pc
  rows.append({'lo':lo,'hi':hi,'pairs_internal':inside,'pairs_crossing':boundary,'primes':pc})
  previous=bytes((previous+mask)[-2:])
 require(rows[-1]['hi']==bound-(bound%2==0),'complete final odd segment')
 return {'pairs':total,'pi':pi,'first_lower':first_lower,'last_lower':last_lower,'segments':rows,
         'base_prime_count_including_two':len(primes)+1,'bound':bound,'slots':slots}

def matching_check(pairs):
 require(type(pairs) is list and bool(pairs),'nonempty pair list')
 entries=[]
 for row in pairs:
  require(type(row) is tuple and len(row)==2 and row[0]>43 and row[1]-row[0]==2,'exact screened gap-two pair')
  require(prime(row[0]) and prime(row[1]),'actual primes in a finite matching');entries.extend(row)
 require(len(entries)==len(set(entries)),'every matching entry distinct')
 return len(pairs)

def seed_invoice(nupper,degree,s,t,Xlower):
 require(all(type(x) is int and x>0 for x in (nupper,degree,s,t)) and type(Xlower) is F,'exact bounded seed parameters')
 require(degree%2==0 and Xlower>4*PARAMETERS['bound'],'even degree and complete bridge separation')
 need=degree*(nupper+8)*(s+t-1)
 require(need<=PARAMETERS['expected_pairs'],'complete retained and narrowest candidate groups')
 return {'candidate_pairs':need,'available_pairs':PARAMETERS['expected_pairs'],'seed_span_over_X_upper':str(F(PARAMETERS['bound'])/Xlower)}

def controls():
 checks=0
 for bound in (100,121,343,1000,10001):
  plist=[p for p in range(2,bound+1) if prime(p)];pairs=[(p,p+2) for p in plist if p>43 and p+2<=bound and prime(p+2)]
  if pairs:require(matching_check(pairs)==len(pairs),'independent complete matching');checks+=len(pairs)
  for slots in (1,2,3,7,31,128,257):
   data=sieve(bound,slots)
   require(data['pairs']==len(pairs) and data['pi']==len(plist),'complete independent trial-division count at arbitrary boundaries');checks+=1
 for p in range(45,20000,2):
  require(not(prime(p) and prime(p+2) and prime(p+4)),'three-prime overlap exclusion');checks+=1
 # Range algebra uses the actual selected matching span; it does not assert prime density.
 for t in range(2,20):
  for kept in range(1,12):
   values=[F(j*j,100) for j in range(kept+t-1)];ranges=sorted(values)[:kept]
   width=sum(values,F());z=max(ranges)
   require(sum(x*x for x in ranges)<=z*(width-(t-1)*z)<=width*width/(4*(t-1)),'same narrowest range algebra at finite seed span');checks+=1
 require(seed_invoice(27555,6,16,5,F(8000000000))['candidate_pairs']==3307560,'actual whole-band matching application');checks+=1
 return checks

def reject(action):
 try:action()
 except (ValueError,TypeError,OSError,KeyError,UnicodeError,ZeroDivisionError) as err:return str(err)
 raise ValueError('negative control unexpectedly accepted')

def verify_count(data,expected_rows):
 require(type(expected_rows) is list and len(expected_rows)==512,'complete fixed segment table')
 for row in expected_rows:
  require(type(row) is dict and set(row)=={'lo','hi','pairs_internal','pairs_crossing','primes'} and all(type(x) is int and x>=0 for x in row.values()),'exact integer segment table fields')
 require(data['segments']==expected_rows,'every recomputed segment count matches exact input table')
 require(data['pairs']==PARAMETERS['expected_pairs'] and data['pi']==PARAMETERS['expected_pi']
   and data['first_lower']==PARAMETERS['expected_first_lower'] and data['last_lower']==PARAMETERS['expected_last_lower'],'exact complete finite count and endpoints')

def negative_controls(data,bindings):
 out={}
 for label,value in [('missing',data['segments'][:-1]),('empty',[]),('wrong',copy.deepcopy(data['segments']))]:
  if label=='wrong':value[0]['pairs_internal']+=1
  out['segment_'+label]=reject(lambda value=value:verify_count(data,value))
 for label,k in [('pairs','pairs'),('prime_count','pi'),('first','first_lower'),('last','last_lower')]:
  x=copy.deepcopy(data);x[k]+=1;out[label]=reject(lambda x=x:verify_count(x,data['segments']))
 bad_table=copy.deepcopy(data['segments']);bad_table[0]['pairs_crossing']=False
 out['boolean_segment_count']=reject(lambda:verify_count(data,bad_table))
 out['overlapping_pairs']=reject(lambda:matching_check([(3,5),(5,7)]))
 out['repeated_pair']=reject(lambda:matching_check([(59,61),(59,61)]))
 out['composite_endpoint']=reject(lambda:matching_check([(61,63)]))
 out['wrong_gap']=reject(lambda:matching_check([(59,67)]))
 out['bridge_separation']=reject(lambda:seed_invoice(20000,6,10,2,F(1<<32)))
 out['candidate_overflow']=reject(lambda:seed_invoice(30000,6,100,2,F(1<<33)))
 out['invalid_sieve_bound']=reject(lambda:sieve(99,100))
 out['invalid_segment']=reject(lambda:sieve(1000,0))
 for label,x in [('empty',{}),('array',[]),('null',None)]:out['source_'+label]=reject(lambda x=x:source_check(x))
 for name in bindings:
  x=dict(bindings);x.pop(name);out['missing_source:'+name]=reject(lambda x=x:source_check(x))
 for digest in ('','x'*64,'0'*64):
  x=dict(bindings);x[next(iter(SOURCES))]=digest;out['bad_digest:'+digest[:4]]=reject(lambda x=x:source_check(x))
 out['extra_source']=reject(lambda:source_check(dict(bindings,unexpected='0'*64)))
 for label,text in [('empty',''),('duplicate','{"a":1,"a":2}'),('malformed','{'),('nonfinite','{"a":NaN}')]:out['json_'+label]=reject(lambda text=text:parse_json(text))
 return out

def physical_attacks(bindings):
 count=0
 with tempfile.TemporaryDirectory(prefix='sude-twin-seed-sources-') as temp:
  root=Path(temp)
  for name in bindings:
   p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((ROOT/name).read_bytes())
  for name in bindings:
   p=root/name;raw=p.read_bytes()
   for kind in ('missing','empty','changed','directory','symlink'):
    p.unlink()
    if kind=='empty':p.write_bytes(b'')
    elif kind=='changed':p.write_bytes(raw+b'\nchanged\n')
    elif kind=='directory':p.mkdir()
    elif kind=='symlink':p.symlink_to(ROOT/name)
    reject(lambda:source_check(bindings,root));count+=1
    if p.is_symlink() or p.is_file():p.unlink()
    elif p.is_dir():p.rmdir()
    p.write_bytes(raw)
  for name in ('manuscripts','code'):
   p=root/name;q=root/(name+'_kept');p.rename(q);p.symlink_to(q,target_is_directory=True)
   reject(lambda:source_check(bindings,root));count+=1;p.unlink();q.rename(p)
  source_check(bindings,root)
 return count

def run(path=INPUT):
 require(__debug__,'run without -O');require(path.is_file() and not path.is_symlink(),'regular input manifest')
 raw=path.read_bytes();require(bool(raw),'nonempty manifest');manifest=parse_json(raw.decode())
 require(type(manifest) is dict and set(manifest)=={'schema','scope','parameters','segments','sources'},'complete exact input manifest')
 require(manifest['schema']==SCHEMA and manifest['scope']==SCOPE and manifest['parameters']==PARAMETERS,'canonical exact source parameters')
 require(all(type(x) is int for x in manifest['parameters'].values()),'integer finite input parameters')
 source_check(manifest['sources']);data=sieve(PARAMETERS['bound'],PARAMETERS['odd_segment_size']);verify_count(data,manifest['segments'])
 return {'status':'PASS_FINITE_TWIN_SEED_MATCHING','count':data,'finite_controls':controls(),
  'negative_controls':negative_controls(data,manifest['sources']),'physical_source_attacks':physical_attacks(manifest['sources']),
  'required_sources':manifest['sources'],'input_sha256':hashlib.sha256(raw).hexdigest(),
  'scope':SCOPE,'formal_proof':False,'prime_analytic_imports_for_count':[],'conditional_allocation_premise':'NS range and allocation theorem; the sieve does not establish it','infinite_twin_prime_assertion':False,'square_cutoff_asserted':False}

if __name__=='__main__':
 require(len(sys.argv)<=2,'at most one manifest path')
 print(json.dumps(run(Path(sys.argv[1]) if len(sys.argv)==2 else INPUT),indent=2,sort_keys=True))
