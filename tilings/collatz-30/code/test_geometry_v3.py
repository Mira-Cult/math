"""Independent unit-cell checker for the endpoint14 finite certificate.

No producer rectangle decomposition, overlap predicate, cavity flood fill, or
forced-neighborhood routine is used in witness verification. The infinite
tiling argument remains an ordinary mathematical proof, not a unit test.
"""
from __future__ import annotations

import copy
from collections import Counter,deque
from itertools import product
import json
import unittest

from geometry_v3 import Parameters,default_parameters,full_certificate,compile_tiles,polygon,east_contact,northeast_contact


def turn(p,k):
    x,y=p
    for _ in range(k%4):x,y=-y,x
    return x,y


def pose(p):
    assert len(p)==2 and type(p[0]) is int and 0<=p[0]<4
    assert len(p[1])==2 and all(type(x) is int for x in p[1])
    return p[0],tuple(p[1])


def local_cell(cell,p):
    k,(a,b)=pose(p);x,y=cell
    x,y=turn((2*(x-a)+1,2*(y-b)+1),-k)
    return x//2,y//2


def inside(P,cell,codes):
    """Literal rectangle-transfer definition, independently of vertex scans."""
    x,y=cell;n,e,s,w=codes;L=P.L;d=P.south_depth;f=P.east_depth
    t=P.horizontal_length;u=P.vertical_length
    present=(0<=x<L and 0<=y<L) or (0<=x<t+s and -d<=y<0) or (L<=x<L+f and 0<=y<u+e)
    removed=(0<=x<t+n and L-d<=y<L) or (0<=x<f and 0<=y<u+w)
    return present and not removed


def member(P,cell,p,kind='core'):
    codes=(P.V-1,0,0,P.H-1) if kind=='core' else (0,P.H-1,P.V-1,0)
    return inside(P,local_cell(cell,p),codes)


def box_cells(b):
    a,b0,c,d=b
    assert all(type(z) is int for z in (a,b0,c,d)) and a<c and b0<d
    return {(x,y) for x in range(a,c) for y in range(b0,d)}


def neighborhood(p,rules):
    k,d=pose(p)
    out={(k,d)}
    for r in rules:
        a,b=turn(r,k);out.add((k,(d[0]+a,d[1]+b)))
    return out


def verify_witness(P,w,allowed):
    allowed={pose(p) for p in allowed}
    if w['kind']=='overlap':
        a,b=pose(w['a']),pose(w['b'])
        assert a in allowed and b in allowed and a!=b
        cells=box_cells(w['overlap'])
        assert all(member(P,c,a) and member(P,c,b) for c in cells)
        return
    assert w['kind']=='cavity'
    ps=[pose(p) for p in w['poses']]
    assert len(ps)==len(set(ps)) and set(ps)==allowed
    region=set();area=0
    for b in w['component']:
        cells=box_cells(b);assert not region&cells
        region|=cells;area+=len(cells)
    assert area==w['area'] and 0<area<P.L**2-P.south_depth*(P.V-1)-P.east_depth*(P.H-1)
    # Check the entire unit-cell region and its entire boundary. A gap through
    # a shared corner is also blocked, because mandatory cores are closed.
    for c in region:
        assert not any(member(P,c,p) for p in ps)
        x,y=c
        for q in ((x-1,y),(x+1,y),(x,y-1),(x,y+1)):
            assert q in region or any(member(P,q,p) for p in ps)
    todo=[next(iter(region))];seen=set(todo)
    while todo:
        x,y=todo.pop()
        for q in ((x-1,y),(x+1,y),(x,y-1),(x,y+1)):
            if q in region and q not in seen:seen.add(q);todo.append(q)
    assert seen==region
    missing=box_cells(w['unfilled']);assert missing<=region
    assert all(not any(member(P,c,p,'envelope') for p in ps) for c in missing)


def expected_pool(P):
    L=P.L;d=P.south_depth;f=P.east_depth;t=P.horizontal_length;u=P.vertical_length
    return {(0,-d),(L+f,0),(L,L),(0,L-d),(0,0)}|{
        (t+c,-d) for c in range(P.V)}|{(t+c,L) for c in range(P.V)}|{
        (L+f,u+c) for c in range(P.H)}|{(0,u+c) for c in range(P.H)}


def expected_vertex(P,direction,color,second):
    if direction=='west':return P.east_depth,(P.vertical_length+color if second else 0)
    if direction=='north':return P.horizontal_length+color,P.L-P.south_depth
    if direction=='south':return P.horizontal_length+color,0
    assert direction=='east';return P.L,P.vertical_length+color


def verify_corner(P,r,direction,color,rules,second=False):
    assert (r['direction'],r['color'],r['second'])==(direction,color,second)
    z=expected_vertex(P,direction,color,second);assert tuple(r['vertex'])==z
    universe={(k,(z[0]-turn(v,k)[0],z[1]-turn(v,k)[1])) for k in range(4) for v in expected_pool(P)}
    rejected=[pose(q['pose']) for q in r['rejections']];survivors=[pose(p) for p in r['survivors']]
    assert len(rejected)==len(set(rejected)) and len(survivors)==len(set(survivors))
    assert not set(rejected)&set(survivors) and set(rejected)|set(survivors)==universe
    home=neighborhood((0,(0,0)),rules)
    for q in r['rejections']:
        verify_witness(P,q['witness'],home|neighborhood(q['pose'],rules))
    return survivors


def verify_pair(P,r,A,B,rules):
    universe=set(product(A,B))
    rejected=[tuple(pose(p) for p in q['poses']) for q in r['rejections']]
    survivors=[tuple(pose(p) for p in pair) for pair in r['survivors']]
    assert len(rejected)==len(set(rejected)) and len(survivors)==len(set(survivors))
    assert not set(rejected)&set(survivors) and set(rejected)|set(survivors)==universe
    home=neighborhood((0,(0,0)),rules)
    for q in r['rejections']:
        a,b=q['poses']
        verify_witness(P,q['witness'],home|neighborhood(a,rules)|neighborhood(b,rules))
    return survivors


def verify_parameters(P):
    assert all(type(z) is int and z>0 for z in vars(P).values())
    L=P.L;d=P.south_depth;f=P.east_depth;t=P.horizontal_length;u=P.vertical_length
    assert 0<f<t and t+P.V-1<L and u+P.H-1<L-d and d!=f
    area=L*L-d*(P.V-1)-f*(P.H-1)
    assert area>max(d*(P.V-1),f*(P.H-1))


def verify_certificate(cert):
    P=Parameters(**cert['parameters']);L=P.L;W=(-L,0);N=(0,L);E=(L,0);S=(0,-L)
    verify_parameters(P)
    assert cert['format']=='orthogonal14-core-cavity-v1' and cert['complete'] is True
    assert cert['order']==['west_joint','north_single','east_south_joint']
    w=cert['west'];first=verify_corner(P,w['first'],'west',0,())
    assert len(w['seconds'])==len(w['pairs'])==P.H
    for c in range(P.H):
        second=verify_corner(P,w['seconds'][c],'west',c,(),True)
        r=w['pairs'][c];assert r['color']==c
        assert verify_pair(P,r,first,second,())==[((0,W),(0,W))]
    # Only now is the west offset admitted into any forced neighborhood.
    assert len(cert['north'])==P.V
    for c,r in enumerate(cert['north']):
        assert verify_corner(P,r,'north',c,(W,))==[(0,N)]
    assert len(cert['east'])==P.H and len(cert['south'])==P.V
    east=[verify_corner(P,r,'east',c,(W,N)) for c,r in enumerate(cert['east'])]
    south=[verify_corner(P,r,'south',c,(W,N)) for c,r in enumerate(cert['south'])]
    assert len(cert['east_south'])==P.H*P.V
    for (e,s),r in zip(product(range(P.H),range(P.V)),cert['east_south']):
        assert (r['east_color'],r['south_color'])==(e,s)
        assert verify_pair(P,r,east[e],south[s],(W,N))==[((0,E),(0,S))]
    return True


def simple_orthogonal(p):
    assert len(p)==14
    segments=list(zip(p,p[1:]+p[:1]))
    for i,(a,b) in enumerate(segments):
        assert a!=b and ((a[0]==b[0]) != (a[1]==b[1]))
        c=p[(i+2)%len(p)]
        assert (b[0]-a[0])*(c[1]-b[1])!=(b[1]-a[1])*(c[0]-b[0])
        for j,(c,d) in enumerate(segments):
            if j<=i or j in ((i-1)%14,(i+1)%14):continue
            if a[0]==b[0] and c[0]==d[0]:
                hit=a[0]==c[0] and max(min(a[1],b[1]),min(c[1],d[1]))<=min(max(a[1],b[1]),max(c[1],d[1]))
            elif a[1]==b[1] and c[1]==d[1]:
                hit=a[1]==c[1] and max(min(a[0],b[0]),min(c[0],d[0]))<=min(max(a[0],b[0]),max(c[0],d[0]))
            else:
                v0,v1,h0,h1=(a,b,c,d) if a[0]==b[0] else (c,d,a,b)
                hit=min(h0[0],h1[0])<=v0[0]<=max(h0[0],h1[0]) and min(v0[1],v1[1])<=h0[1]<=max(v0[1],v1[1])
            assert not hit


def periodic_core_check(P):
    cells={(x,y) for x in range(P.L+P.east_depth) for y in range(-P.south_depth,P.L)
           if inside(P,(x,y),(0,0,0,0))}
    residues={(x%P.L,y%P.L) for x,y in cells}
    assert len(cells)==len(residues)==P.L**2
    core={(x,y) for x,y in cells if inside(P,(x,y),(P.V-1,0,0,P.H-1))}
    missing=cells-core
    bands={(x,y) for x in range(P.horizontal_length,P.horizontal_length+P.V-1)
           for y in range(P.L-P.south_depth,P.L)}|{
           (x,y) for x in range(P.east_depth) for y in range(P.vertical_length,P.vertical_length+P.H-1)}
    assert missing==bands
    left=set(bands);sizes=[]
    while left:
        p=left.pop();todo=[p];n=1
        while todo:
            x,y=todo.pop()
            for q in (((x-1)%P.L,y),((x+1)%P.L,y),(x,(y-1)%P.L),(x,(y+1)%P.L)):
                if q in left:left.remove(q);todo.append(q);n+=1
        sizes.append(n)
    assert sorted(sizes)==sorted(z for z in (P.south_depth*(P.V-1),P.east_depth*(P.H-1)) if z)
    assert max(sizes,default=0)<len(core)


class GeometryV3Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cert=full_certificate(default_parameters(8,6))
        cls.control=full_certificate(default_parameters(10,5))

    def test_selected_literal_sorted_json_certificate(self):
        self.assertTrue(verify_certificate(json.loads(json.dumps(self.cert,sort_keys=True))))

    def test_retained_palette_certificate(self):
        self.assertTrue(verify_certificate(json.loads(json.dumps(self.control,sort_keys=True))))

    def test_literal_shapes_and_periodic_core(self):
        from spine_frame_v3 import SystemV3 as Thirty
        from scaffold_v3 import SystemV3 as ThirtyOne
        for system in (Thirty(),ThirtyOne()):
            c=compile_tiles([t.edges for t in system.tiles]);P=Parameters(**c['parameters'])
            periodic_core_check(P)
            for item in c['polygons']:
                p=item['vertices'];simple_orthogonal(p)
                self.assertEqual(len(p),14)
                for x in range(P.L+P.east_depth):
                    for y in range(-P.south_depth,P.L):
                        # Exact ray parity from the literal outline, independent
                        # of the producer's rectangle decomposition.
                        parity=sum(a[0]==b[0] and 2*a[0]>2*x+1 and min(2*a[1],2*b[1])<2*y+1<max(2*a[1],2*b[1])
                                   for a,b in zip(p,p[1:]+p[:1]))%2
                        self.assertEqual(bool(parity),inside(P,(x,y),item['profiles']))

    def test_two_genuine_side_observers(self):
        from spine_frame_v3 import SystemV3,parity
        s=SystemV3();c=compile_tiles([t.edges for t in s.tiles])
        root=northeast_contact(c,'h:bg',parity(1));event=east_contact(c,s.event_color)
        self.assertEqual(root['matching_shape_indices'],[s.root_index])
        self.assertIn(s.event_index,event['matching_shape_indices'])
        self.assertEqual(root['anchor'],(66,66))

    def test_missing_case_and_false_overlap_rejected(self):
        c=copy.deepcopy(self.cert);c['west']['first']['rejections'].pop()
        with self.assertRaises(AssertionError):verify_certificate(c)
        c=copy.deepcopy(self.cert)
        r=next(r for r in c['west']['first']['rejections'] if r['witness']['kind']=='overlap')
        r['witness']['overlap']=(0,0,1,1)
        with self.assertRaises(AssertionError):verify_certificate(c)

    def test_false_cavity_rejected(self):
        c=copy.deepcopy(self.cert)
        r=next(r for r in c['east_south'][0]['rejections'] if r['witness']['kind']=='cavity')
        r['witness']['unfilled']=(10000,10000,10001,10001)
        allowed=neighborhood((0,(0,0)),((-66,0),(0,66)))
        for p in r['poses']:allowed|=neighborhood(p,((-66,0),(0,66)))
        with self.assertRaises(AssertionError):verify_witness(Parameters(),r['witness'],allowed)

    def test_invalid_structural_parameters_rejected(self):
        for changes in ({'H':0},{'east_depth':19},{'horizontal_length':61},
                        {'vertical_length':41},{'south_depth':13}):
            c=copy.deepcopy(self.cert);c['parameters'].update(changes)
            with self.assertRaises(AssertionError):verify_parameters(Parameters(**c['parameters']))
            with self.assertRaises(AssertionError):verify_certificate(c)

    def test_nonintegral_certificate_geometry_rejected(self):
        for bad in ((0.5,(0,0)),(0,(0.5,0)),(4,(0,0)),('0',(0,0))):
            with self.assertRaises(AssertionError):pose(bad)
        with self.assertRaises(AssertionError):box_cells((0.0,0,1,1))


if __name__=='__main__':unittest.main()
