"""Twenty-side integer rectangular-profile compiler with exact contact witnesses.

Compiler outputs require a complete finite contact certificate. The universal
whole-plane use of those witnesses is proved in manuscripts/geometry-v2.md.
No baseline geometry file is modified. Coordinates and predicates are exact.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
import itertools
import json
from math import isqrt

Point=tuple[int,int]
Box=tuple[int,int,int,int]


def cross(a,b,c):
    return (b[0]-a[0])*(c[1]-b[1])-(b[1]-a[1])*(c[0]-b[0])


def rotate(p,k):
    x,y=p
    return ((x,y),(-y,x),(-x,-y),(y,-x))[k%4]


def translated(p,k,d):
    return tuple((rotate(z,k)[0]+d[0],rotate(z,k)[1]+d[1]) for z in p)


@dataclass(frozen=True)
class Parameters:
    horizontal_colors:int
    vertical_colors:int
    scale:int=0
    macro_span:int=0

    @property
    def M(self):return self.scale or max(1,(self.horizontal_colors+1)//2,self.vertical_colors-1)
    @property
    def L(self):return self.macro_span or 12*self.M
    @property
    def h_start(self):return 2*self.M
    @property
    def v_start(self):return 2*self.M
    @property
    def h_depth(self):return 3*self.M
    @property
    def v_depth(self):return 4*self.M
    @property
    def h_end(self):return 4*self.M
    @property
    def v_end(self):return 5*self.M


def validate_parameters(P):
    if min(P.horizontal_colors,P.vertical_colors,P.M)<1:
        raise ValueError('positive integer palette sizes and scale required')
    if P.L<=8*P.M+P.horizontal_colors-1 or P.L<=4*P.M+P.vertical_colors-1:
        raise ValueError('north and west dents require positive separation')
    area=P.L**2-P.h_depth*(P.vertical_colors-1)-P.v_depth*(P.horizontal_colors-1)
    if area<=max(P.h_depth*(P.vertical_colors-1),P.v_depth*(P.horizontal_colors-1)):
        raise ValueError('core too small to exclude extra seam tiles')


def polygon(params:Parameters,north:int,east:int,south:int,west:int):
    """CCW twenty-vertex formula; codes extend the fixed key width.

    N/S encode vertical Wang colors; E/W encode horizontal Wang colors.
    Widths stay positive even at code zero. Opposite profiles complement.
    """
    P=params;L=P.L;a=P.h_start;b=P.h_end;d=P.h_depth
    c=P.v_start;e=P.v_end;f=P.v_depth
    if not (0<=north<P.vertical_colors and 0<=south<P.vertical_colors
            and 0<=east<P.horizontal_colors and 0<=west<P.horizontal_colors):
        raise ValueError('color outside palette')
    return ((0,0),(a,0),(a,-d),(b+south,-d),(b+south,0),(L,0),
            (L,c),(L+f,c),(L+f,e+east),(L,e+east),(L,L),
            (b+north,L),(b+north,L-d),(a,L-d),(a,L),(0,L),
            (0,e+west),(f,e+west),(f,c),(0,c))


def rectangles(p):
    """Disjoint exact open rectangles whose closures cover an orthogonal P."""
    xs=sorted({x for x,y in p});out=[]
    for x0,x1 in zip(xs,xs[1:]):
        ys=sorted(a[1] for a,b in zip(p,p[1:]+p[:1])
                  if a[1]==b[1] and 2*min(a[0],b[0])<x0+x1<2*max(a[0],b[0]))
        assert len(ys)%2==0
        out.extend((x0,y0,x1,y1) for y0,y1 in zip(ys[::2],ys[1::2]))
    return tuple(out)


def pose_boxes(boxes,k,d):
    out=[]
    for x0,y0,x1,y1 in boxes:
        points=[rotate(z,k) for z in ((x0,y0),(x0,y1),(x1,y0),(x1,y1))]
        out.append((min(x for x,y in points)+d[0],min(y for x,y in points)+d[1],
                    max(x for x,y in points)+d[0],max(y for x,y in points)+d[1]))
    return tuple(out)


def overlap(A,B):
    for x0,y0,x1,y1 in A:
        for u0,v0,u1,v1 in B:
            a,b,c,d=max(x0,u0),max(y0,v0),min(x1,u1),min(y1,v1)
            if a<c and b<d:return a,b,c,d
    return None


def profile_bounds(params):
    P=params
    small=polygon(P,P.vertical_colors-1,0,0,P.horizontal_colors-1)
    large=polygon(P,0,P.horizontal_colors-1,P.vertical_colors-1,0)
    return rectangles(small),rectangles(large)


def convex_pool(params):
    P=params;out=set()
    for side,count in enumerate((P.vertical_colors,P.horizontal_colors,P.vertical_colors,P.horizontal_colors)):
        for color in range(count):
            codes=[0]*4;codes[side]=color;p=polygon(P,*codes)
            out|={v for i,v in enumerate(p) if cross(p[i-1],v,p[(i+1)%len(p)])>0}
    return out


def targets(params):
    P=params
    return {'west':((P.v_depth,P.v_start),(-P.L,0)),
            'north':((P.h_start,P.L-P.h_depth),(0,P.L)),
            'east':((P.L,P.v_start),(P.L,0)),
            'south':((P.h_start,0),(0,-P.L))}


def forced_offsets(rules,depth):
    seen={(0,0)};front={(0,0)}
    for step in range(depth):
        front={(x+dx,y+dy) for x,y in front for dx,dy in rules}-seen
        seen|=front
    return tuple(sorted(seen))


def test_lock(params,name,rules=(),depth=1,vertex=None):
    C,_=profile_bounds(params)
    z,expected=targets(params)[name];pool=convex_pool(params)
    if vertex is not None:z=vertex
    poses={(k,(z[0]-rotate(v,k)[0],z[1]-rotate(v,k)[1]))
           for k in range(4) for v in pool}
    offsets=forced_offsets(rules,depth)
    home={off:pose_boxes(C,0,off) for off in offsets}
    rejects=[];survivors=[]
    for k,shift in sorted(poses):
        rejection=None
        for a,A in home.items():
            if rejection:break
            for b in offsets:
                rb=rotate(b,k);other=(shift[0]+rb[0],shift[1]+rb[1])
                if k==0 and other==a:continue
                witness=overlap(A,pose_boxes(C,k,other))
                if witness:
                    rejection={'rotation':k,'shift':shift,'reason':'forced_core_overlap',
                               'home_offset':a,'other_offset':b,'overlap':witness}
                    break
        if rejection:rejects.append(rejection)
        else:survivors.append((k,shift))
    return {'lock':name,'reflex_vertex':z,'expected':(0,expected),'rules':rules,'depth':depth,
            'poses':len(poses),'survivors':survivors,'rejections':rejects,
            'proved':survivors==[(0,expected)]}


def joint_lock(params,name,rules=(),depth=1):
    """Use both reflex gaps of one tab or dent simultaneously."""
    P=params;C,E=profile_bounds(P);offsets=forced_offsets(rules,depth)
    first=test_lock(P,name,rules,depth)
    expected=first['expected'];cases=[]
    for color in range(P.horizontal_colors if name in ('east','west') else P.vertical_colors):
        vertex={'east':(P.L,P.v_end+color),'west':(P.v_depth,P.v_end+color),
                'south':(P.h_end+color,0),'north':(P.h_end+color,P.L-P.h_depth)}[name]
        second=test_lock(P,name,rules,depth,vertex=vertex)
        rejected=[];survivors=[]
        for left,right in itertools.product(first['survivors'],second['survivors']):
            if left==right:
                survivors.append((left,right));continue
            k1,d1=left;k2,d2=right;witness=None
            for a in offsets:
                if witness:break
                ra=rotate(a,k1);posa=(ra[0]+d1[0],ra[1]+d1[1]);A=pose_boxes(C,k1,posa)
                for b in offsets:
                    rb=rotate(b,k2);posb=(rb[0]+d2[0],rb[1]+d2[1])
                    if k1==k2 and posa==posb:continue
                    box=overlap(A,pose_boxes(C,k2,posb))
                    if box:
                        witness={'left':left,'right':right,'left_offset':a,
                                 'right_offset':b,'overlap':box};break
            if witness:rejected.append(witness)
            else:survivors.append((left,right))
        cases.append({'color':color,'second':second,'pair_rejections':rejected,
                      'pair_survivors':survivors,'proved':survivors==[(expected,expected)]})
    return {'lock':name,'first':first,'cases':cases,'proved':all(case['proved'] for case in cases)}


def search_locks(params,max_depth=2):
    validate_parameters(params)
    rules=[];stages=[];joint=[];order=[];unproved=set(targets(params))
    for stage in range(4):
        progress=False
        for name in ('west','north','east','south'):
            if name not in unproved:continue
            result=test_lock(params,name,tuple(rules),max_depth)
            if result['proved']:
                stages.append(result);order.append(('single',len(stages)-1))
            else:
                result=joint_lock(params,name,tuple(rules),max_depth)
                if not result['proved']:continue
                joint.append(result);order.append(('joint',len(joint)-1))
            unproved.remove(name);rules.append(targets(params)[name][1]);progress=True
        if not progress:break
    return {'params':vars(params),'stages':stages,'joint':joint,'order':order,'complete':not unproved,
            'remaining':{name:test_lock(params,name,tuple(rules),max_depth) for name in sorted(unproved)}}


def corner_certificate(params):
    if isinstance(params,dict):params=Parameters(**params)
    result=search_locks(params,1)
    if not result['complete']:
        raise ValueError('this palette/scale has no complete contact certificate')
    return result


def shape_key(p):
    keys=[]
    for k in range(4):
        q=[rotate(v,k) for v in p]
        x=min(a for a,b in q);y=min(b for a,b in q)
        q=[(a-x,b-y) for a,b in q]
        j=min(range(len(q)),key=lambda i:q[i])
        keys.append(tuple(q[j:]+q[:j]))
    return min(keys)


def oriented_key(p):
    x=min(a for a,b in p);y=min(b for a,b in p)
    q=[(a-x,b-y) for a,b in p];j=min(range(len(q)),key=lambda i:q[i])
    return tuple(q[j:]+q[:j])


def compile_tiles(tiles,params=None):
    """Compile literal (N,E,S,W) tuples, retaining their input order.

    The default finite parameters are deterministic from palette sizes. A
    successful exact contact certificate is required, not assumed for every
    possible palette. Explicit Parameters may be supplied for other sizes.
    """
    tiles=[tuple(t) for t in tiles]
    if not tiles or any(len(t)!=4 for t in tiles) or len(set(tiles))!=len(tiles):
        raise ValueError('nonempty distinct Wang four-tuples required')
    H=Counter(t[i] for t in tiles for i in (1,3))
    V=Counter(t[i] for t in tiles for i in (0,2))
    h={color:i for i,color in enumerate(sorted(H,key=lambda c:(-H[c],repr(c))))}
    v={color:i for i,color in enumerate(sorted(V,key=lambda c:(-V[c],repr(c))))}
    P=params or Parameters(len(H),len(V))
    if isinstance(P,dict):P=Parameters(**P)
    if (P.horizontal_colors,P.vertical_colors)!=(len(H),len(V)):
        raise ValueError('parameter palette differs from input palette')
    validate_parameters(P);cert=corner_certificate(P)
    out=[]
    for i,(n,e,s,w) in enumerate(tiles):
        codes=(v[n],h[e],v[s],h[w]);poly=polygon(P,*codes)
        area2=sum(a[0]*b[1]-b[0]*a[1] for a,b in zip(poly,poly[1:]+poly[:1]))
        assert len(poly)==20 and all(cross(poly[j-1],z,poly[(j+1)%20]) for j,z in enumerate(poly))
        if len({oriented_key(translated(poly,k,(0,0))) for k in range(4)})!=4:
            raise ValueError('self-rotation would make the oriented decoder ambiguous')
        out.append({'index':i,'wang':(n,e,s,w),'profiles':codes,'vertices':poly,
                    'sides':20,'area':area2//2})
    if len({shape_key(p['vertices']) for p in out})!=len(out):
        raise ValueError('congruent source types')
    bound=max(abs(x) for p in out for point in p['vertices'] for x in point)
    return {'variant':'profile20','parameters':vars(P),'scale':P.M,'macro_spacing':P.L,
            'motion':'translations and rotations, no reflections','edge_to_edge_required':False,
            'color_map_horizontal':sorted(h.items(),key=lambda x:repr(x[0])),
            'color_map_vertical':sorted(v.items(),key=lambda x:repr(x[0])),
            'polygons':out,'summary':{'shapes':len(out),'max_sides':20,'minimum_sides':20,
              'total_sides':20*len(out),'side_histogram':{'20':len(out)},
              'max_coordinate_absolute':bound,'coordinate_denominator':1,
              'signed_coordinate_bits':1+bound.bit_length(),
              'minimum_core_area':P.L**2-P.h_depth*(P.vertical_colors-1)-P.v_depth*(P.horizontal_colors-1)},
            'certificate_order':cert['order']}


def east_contact(compiled,color):
    """Exact geometric color recognizer, with no source-type uniqueness claim."""
    P=Parameters(**compiled['parameters']);h=dict(compiled['color_map_horizontal'])
    code=h[color];width=P.v_end-P.v_start+code;depth=P.v_depth
    expected=[p['index'] for p in compiled['polygons'] if p['wang'][1]==color]
    found=[]
    for item in compiled['polygons']:
        p=item['vertices']
        for i in range(20):
            a,b,c,d=(p[(i+j)%20] for j in range(4))
            lengths=tuple(abs(u[0]-v[0])+abs(u[1]-v[1]) for u,v in ((a,b),(b,c),(c,d)))
            if lengths==(depth,width,depth) and cross(a,b,c)>0 and cross(b,c,d)>0:
                found.append(item['index'])
    if found!=expected:raise AssertionError('contact is not an exact east-color recognizer')
    q=isqrt(depth*depth+width*width)
    radius=q+(q*q<depth*depth+width*width)+1
    return {'color':color,'depth':depth,'middle_length':width,'anchor':(P.L,P.v_start),
            'first_direction':(1,0),'middle_direction':(0,1),'patch_radius':radius,
            'matching_shape_indices':expected,'recognizes':'east source color; contextual type use is separately proved'}


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--h',type=int,default=15)
    p.add_argument('--v',type=int,default=6);p.add_argument('--scale',type=int,default=0)
    p.add_argument('--span',type=int,default=0)
    p.add_argument('--depth',type=int,default=2);p.add_argument('--out')
    a=p.parse_args();result=search_locks(Parameters(a.h,a.v,a.scale,a.span),a.depth)
    if a.out:
        with open(a.out,'w') as f:json.dump(result,f,sort_keys=True)
    print(json.dumps({'params':result['params'],'complete':result['complete'],
          'stages':[{k:v for k,v in s.items() if k!='rejections'} for s in result['stages']],
          'joint':[{'lock':s['lock'],'proved':s['proved'],'cases':len(s['cases']),
                    'failed':[{'color':c['color'],'survivors':c['pair_survivors']}
                              for c in s['cases'] if not c['proved']]} for s in result['joint']],
          'remaining':{k:{a:b for a,b in v.items() if a!='rejections'} for k,v in result['remaining'].items()}},sort_keys=True))
