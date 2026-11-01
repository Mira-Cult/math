"""Fourteen-side integer compiler with complete finite contact certificates.

The finite witnesses support the ordinary mathematical argument in
manuscripts/geometry-v3.md. They are not a kernel-checked infinite theorem.
Reviewed v1/v2 sources are unchanged.
"""
from __future__ import annotations

from dataclasses import dataclass,asdict
from itertools import product
from functools import lru_cache
from collections import deque,Counter
import json

from geometry_v2 import cross,rotate,rectangles,pose_boxes,overlap,forced_offsets,oriented_key


@dataclass(frozen=True)
class Parameters:
    H:int=8
    V:int=6
    L:int=66
    south_depth:int=19
    east_depth:int=13
    horizontal_length:int=19
    vertical_length:int=25


def validate_parameters(P):
    if not all(isinstance(x,int) and x>0 for x in asdict(P).values()):
        raise ValueError('positive integer parameters required')
    L=P.L;d=P.south_depth;f=P.east_depth;t=P.horizontal_length;u=P.vertical_length
    if not (f<t and t+P.V-1<L and u+P.H-1<L-d):
        raise ValueError('profiles must have positive separating corridors')
    area=L*L-d*(P.V-1)-f*(P.H-1)
    if area<=max(d*(P.V-1),f*(P.H-1)):
        raise ValueError('core too small to exclude additional seam tiles')
    if d==f:raise ValueError('different extents fix the quarter-turn frame')


def default_parameters(H,V):
    if (H,V)==(8,6):return Parameters()
    if (H,V)==(10,5):return Parameters(10,5,75,23,17,23,28)
    M=max(H,V)+1
    return Parameters(H,V,30*M,11*M,9*M,11*M,12*M)


def polygon(P,n,e,s,w):
    L=P.L;d=P.south_depth;f=P.east_depth;t=P.horizontal_length;u=P.vertical_length
    assert 0<=n<P.V and 0<=s<P.V and 0<=e<P.H and 0<=w<P.H
    return ((0,-d),(t+s,-d),(t+s,0),(L+f,0),(L+f,u+e),(L,u+e),
            (L,L),(t+n,L),(t+n,L-d),(0,L-d),(0,u+w),(f,u+w),(f,0),(0,0))


def convex_pool(P):
    out=set()
    for side,count in enumerate((P.V,P.H,P.V,P.H)):
        for c in range(count):
            codes=[0]*4;codes[side]=c;p=polygon(P,*codes)
            out|={v for i,v in enumerate(p) if cross(p[i-1],v,p[(i+1)%14])>0}
    return out


def target(P,direction,color=0,second=False):
    L=P.L;d=P.south_depth;f=P.east_depth;t=P.horizontal_length;u=P.vertical_length
    if direction=='west':return ((f,u+color) if second else (f,0)),(-L,0)
    if direction=='east':return (L,u+color),(L,0)
    if direction=='north':return (t+color,L-d),(0,L)
    if direction=='south':return (t+color,0),(0,-L)
    raise ValueError(direction)


@lru_cache(maxsize=None)
def carrier_boxes(P):
    return (rectangles(polygon(P,P.V-1,0,0,P.H-1)),
            rectangles(polygon(P,0,P.H-1,P.V-1,0)))


def cluster_poses(pose,offsets):
    k,d=pose
    return {(k,(d[0]+rotate(o,k)[0],d[1]+rotate(o,k)[1])) for o in offsets}


def cavity_witness(P,poses):
    """Exact compressed-grid bounded-complement witness, or None.

    Every grid line is a core/envelope rectangle boundary.  The reported open
    rectangle is outside all present envelopes in a bounded complement
    component of the closed mandatory cores, whose area is below the area of
    any one further tile.
    """
    C,E=carrier_boxes(P)
    A=[b for k,d in poses for b in pose_boxes(C,k,d)]
    B=[b for k,d in poses for b in pose_boxes(E,k,d)]
    xs={x for b in A+B for x in (b[0],b[2])}
    ys={y for b in A+B for y in (b[1],b[3])}
    xs=sorted(xs|{min(xs)-1,max(xs)+1});ys=sorted(ys|{min(ys)-1,max(ys)+1})
    xi={x:i for i,x in enumerate(xs)};yi={y:i for i,y in enumerate(ys)}
    W=len(xs)-1;H=len(ys)-1
    def cover(boxes):
        return {(i,j) for a,b,c,d in boxes for i in range(xi[a],xi[c]) for j in range(yi[b],yi[d])}
    core=cover(A);env=cover(B);outside={(0,0)};todo=deque(outside)
    while todo:
        i,j=todo.popleft()
        for p in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
            if 0<=p[0]<W and 0<=p[1]<H and p not in core and p not in outside:
                outside.add(p);todo.append(p)
    remain={(i,j) for i in range(W) for j in range(H)}-core-outside
    core_area=sum((c-a)*(d-b) for a,b,c,d in C)
    while remain:
        p=min(remain);component={p};remain.remove(p);todo=deque([p])
        while todo:
            i,j=todo.popleft()
            for q in ((i-1,j),(i+1,j),(i,j-1),(i,j+1)):
                if q in remain:remain.remove(q);component.add(q);todo.append(q)
        area=sum((xs[i+1]-xs[i])*(ys[j+1]-ys[j]) for i,j in component)
        unfilled=component-env
        if area<core_area and unfilled:
            i,j=min(unfilled)
            return {'kind':'cavity','poses':sorted(poses),'area':area,
                    'unfilled':(xs[i],ys[j],xs[i+1],ys[j+1]),
                    'component':[(xs[i],ys[j],xs[i+1],ys[j+1]) for i,j in sorted(component)]}
    return None


def reject_cluster(P,poses,cavities=True):
    C,_=carrier_boxes(P);poses=sorted(poses)
    boxes=[pose_boxes(C,*p) for p in poses]
    for i,a in enumerate(poses):
        for j in range(i+1,len(poses)):
            box=overlap(boxes[i],boxes[j])
            if box:return {'kind':'overlap','a':a,'b':poses[j],'overlap':box}
    return cavity_witness(P,poses) if cavities else None


def corner_record(P,direction,color,rules,second=False):
    z,_=target(P,direction,color,second);offsets=forced_offsets(rules,1)
    home=cluster_poses((0,(0,0)),offsets)
    poses={(k,(z[0]-rotate(v,k)[0],z[1]-rotate(v,k)[1]))
           for k in range(4) for v in convex_pool(P)}
    rejected=[];survivors=[]
    for pose in sorted(poses):
        w=reject_cluster(P,home|cluster_poses(pose,offsets))
        if w:rejected.append({'pose':pose,'witness':w})
        else:survivors.append(pose)
    return {'direction':direction,'color':color,'second':second,'vertex':z,
            'rejections':rejected,'survivors':survivors}


def pair_record(P,first,second,rules):
    offsets=forced_offsets(rules,1);home=cluster_poses((0,(0,0)),offsets)
    rejected=[];survivors=[]
    for a,b in product(first['survivors'],second['survivors']):
        w=reject_cluster(P,home|cluster_poses(a,offsets)|cluster_poses(b,offsets))
        if w:rejected.append({'poses':(a,b),'witness':w})
        else:survivors.append((a,b))
    return {'rejections':rejected,'survivors':survivors}


@lru_cache(maxsize=16)
def full_certificate(P):
    """Literal all-color coverage; no rule is used before it is established."""
    validate_parameters(P);W=(-P.L,0);N=(0,P.L);E=(P.L,0);S=(0,-P.L)
    first=corner_record(P,'west',0,())
    seconds=[corner_record(P,'west',c,(),True) for c in range(P.H)]
    pairs=[{'color':c,**pair_record(P,first,second,())} for c,second in enumerate(seconds)]
    if not all(p['survivors']==[((0,W),(0,W))] for p in pairs):
        raise ValueError('west contact certificate is incomplete')
    west={'first':first,'seconds':seconds,'pairs':pairs}
    north=[corner_record(P,'north',c,(W,)) for c in range(P.V)]
    if not all(c['survivors']==[(0,N)] for c in north):
        raise ValueError('north contact certificate is incomplete')
    east=[corner_record(P,'east',c,(W,N)) for c in range(P.H)]
    south=[corner_record(P,'south',c,(W,N)) for c in range(P.V)]
    pairs=[{'east_color':e,'south_color':s,**pair_record(P,east[e],south[s],(W,N))}
           for e,s in product(range(P.H),range(P.V))]
    if not all(p['survivors']==[((0,E),(0,S))] for p in pairs):
        raise ValueError('joint east/south contact certificate is incomplete')
    return {'format':'orthogonal14-core-cavity-v1','parameters':asdict(P),'complete':True,
            'order':['west_joint','north_single','east_south_joint'],
            'west':west,'north':north,'east':east,'south':south,'east_south':pairs}


def certificate_summary(cert):
    corners=[cert['west']['first'],*cert['west']['seconds'],*cert['north'],*cert['east'],*cert['south']]
    pairs=cert['west']['pairs']+cert['east_south']
    kinds=Counter(r['witness']['kind'] for case in corners+pairs for r in case['rejections'])
    return {'corner_cases':len(corners),'corner_rejections':sum(len(c['rejections']) for c in corners),
            'pair_cases':len(pairs),'pair_rejections':sum(len(c['rejections']) for c in pairs),
            'rejection_kinds':dict(sorted(kinds.items())),'order':cert['order']}


def compile_tiles(tiles,params=None):
    """Compile distinct literal (N,E,S,W) tuples, preserving input order."""
    tiles=[tuple(t) for t in tiles]
    if not tiles or any(len(t)!=4 for t in tiles) or len(set(tiles))!=len(tiles):
        raise ValueError('nonempty distinct Wang four-tuples required')
    hc=Counter(t[i] for t in tiles for i in (1,3));vc=Counter(t[i] for t in tiles for i in (0,2))
    h={x:i for i,x in enumerate(sorted(hc,key=lambda x:(-hc[x],repr(x))))}
    v={x:i for i,x in enumerate(sorted(vc,key=lambda x:(-vc[x],repr(x))))}
    P=params or default_parameters(len(h),len(v))
    if isinstance(P,dict):P=Parameters(**P)
    if (P.H,P.V)!=(len(h),len(v)):raise ValueError('palette does not match parameters')
    cert=full_certificate(P);out=[]
    for i,(n,e,s,w) in enumerate(tiles):
        codes=(v[n],h[e],v[s],h[w]);p=polygon(P,*codes)
        if len(p)!=14 or not all(cross(p[j-1],z,p[(j+1)%14]) for j,z in enumerate(p)):
            raise AssertionError('fourteen genuine sides required')
        area2=sum(a[0]*b[1]-b[0]*a[1] for a,b in zip(p,p[1:]+p[:1]))
        out.append({'index':i,'wang':(n,e,s,w),'profiles':codes,'vertices':p,'sides':14,'area':area2//2})
    keys={oriented_key(tuple(rotate(z,k) for z in p['vertices'])) for p in out for k in range(4)}
    if len(keys)!=4*len(out):raise ValueError('different oriented source types are congruent')
    bound=max(abs(x) for p in out for z in p['vertices'] for x in z)
    hmap=sorted(h.items(),key=lambda x:repr(x[0]));vmap=sorted(v.items(),key=lambda x:repr(x[0]))
    return {'variant':'endpoint14','parameters':asdict(P),'macro_spacing':P.L,
            'motion':'translations and rotations, no reflections','edge_to_edge_required':False,
            'color_map_horizontal':hmap,'color_map_vertical':vmap,
            'horizontal_color_map':hmap,'vertical_color_map':vmap,
            'polygons':out,'summary':{'shapes':len(out),'minimum_sides':14,'max_sides':14,
            'total_sides':14*len(out),'side_histogram':{'14':len(out)},
            'max_coordinate_absolute':bound,'coordinate_denominator':1,
            'signed_coordinate_bits':1+bound.bit_length(),
            'minimum_core_area':P.L**2-P.south_depth*(P.V-1)-P.east_depth*(P.H-1)},
            'certificate_summary':certificate_summary(cert)}


def convex_pair_matches(compiled,lengths):
    """All convex vertices with an ordered pair of complete genuine sides."""
    out=[]
    for item in compiled['polygons']:
        p=item['vertices']
        for j,b in enumerate(p):
            a=p[j-1];c=p[(j+1)%len(p)]
            pair=(abs(a[0]-b[0])+abs(a[1]-b[1]),abs(b[0]-c[0])+abs(b[1]-c[1]))
            if cross(a,b,c)>0 and pair==tuple(lengths):out.append((item['index'],j))
    return out


def east_contact(compiled,color):
    P=Parameters(**compiled['parameters']);code=dict(compiled['color_map_horizontal'])[color]
    lengths=(P.vertical_length+code,P.east_depth)
    expected=[(p['index'],4) for p in compiled['polygons'] if p['wang'][1]==color]
    found=convex_pair_matches(compiled,lengths)
    if found!=expected:raise ValueError('two-side event motif is not an exact east-color recognizer')
    return {'color':color,'lengths':lengths,'anchor':(P.L+P.east_depth,P.vertical_length+code),
            'incoming_direction':(0,1),'outgoing_direction':(-1,0),
            'patch_radius':max(lengths)+1,'matching_shape_indices':[i for i,j in found],
            'same_neighbor_on_both_sides':True,
            'recognizes':'east source color; contextual event use is separately proved'}


def northeast_contact(compiled,east_color,north_color):
    P=Parameters(**compiled['parameters']);e=dict(compiled['color_map_horizontal'])[east_color]
    n=dict(compiled['color_map_vertical'])[north_color]
    lengths=(P.L-P.vertical_length-e,P.L-P.horizontal_length-n)
    expected=[(p['index'],6) for p in compiled['polygons'] if p['wang'][1]==east_color and p['wang'][0]==north_color]
    found=convex_pair_matches(compiled,lengths)
    if found!=expected:raise ValueError('two-side root motif does not recognize exactly the selected color pair')
    return {'east_color':east_color,'north_color':north_color,'lengths':lengths,'anchor':(P.L,P.L),
            'incoming_direction':(0,1),'outgoing_direction':(-1,0),
            'patch_radius':max(lengths)+1,'matching_shape_indices':[i for i,j in found],
            'same_neighbor_on_both_sides':False,'recognizes':'ordered east/north source-color pair'}


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--out');p.add_argument('--h',type=int,default=8)
    p.add_argument('--v',type=int,default=6);a=p.parse_args();result=full_certificate(default_parameters(a.h,a.v))
    if a.out:
        with open(a.out,'w') as f:json.dump(result,f,sort_keys=True)
    print(json.dumps(certificate_summary(result),sort_keys=True))
