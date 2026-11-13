"""Independent checks of the rational-gate and quadratic-field compiler layer.

This does not test or establish the inherited arithmetic source theorem.
Usage: python check_circuit_layer.py CANDIDATE.py
"""
import argparse
import ast
import hashlib
import json
import runpy
from fractions import Fraction as F
from pathlib import Path

def value(node, env):
    if isinstance(node,ast.Name): return env[node.id]
    if isinstance(node,ast.Constant):
        assert isinstance(node.value,int)
        return F(node.value)
    if isinstance(node,ast.UnaryOp):
        assert isinstance(node.op,(ast.UAdd,ast.USub))
        return value(node.operand,env)*(1 if isinstance(node.op,ast.UAdd) else -1)
    assert isinstance(node,ast.BinOp)
    a,b=value(node.left,env),value(node.right,env)
    if isinstance(node.op,ast.Add):return a+b
    if isinstance(node.op,ast.Sub):return a-b
    if isinstance(node.op,ast.Mult):return a*b
    assert isinstance(node.op,ast.Pow) and b.denominator==1 and b>=0
    return a**int(b)

def degree(node):
    if isinstance(node,ast.Name):
        assert node.id.startswith('x') and node.id[1:].isdigit()
        return 1
    if isinstance(node,ast.Constant):
        assert isinstance(node.value,int)
        return 0
    if isinstance(node,ast.UnaryOp):
        assert isinstance(node.op,(ast.UAdd,ast.USub))
        return degree(node.operand)
    assert isinstance(node,ast.BinOp)
    if isinstance(node.op,(ast.Add,ast.Sub)):return max(degree(node.left),degree(node.right))
    if isinstance(node.op,ast.Mult):return degree(node.left)+degree(node.right)
    assert isinstance(node.op,ast.Pow)
    assert isinstance(node.right,ast.Constant) and isinstance(node.right.value,int) and node.right.value>=0
    return degree(node.left)*node.right.value

def fill(rows,env):
    for row in rows:
        t=ast.parse(row,mode='eval').body
        assert isinstance(t,ast.BinOp) and isinstance(t.op,ast.Sub)
        if isinstance(t.left,ast.Name) and t.left.id not in env:
            env[t.left.id]=value(t.right,env)
        else:
            assert isinstance(t.left,ast.BinOp) and isinstance(t.left.op,ast.Mult)
            assert isinstance(t.left.right,ast.Name) and t.left.right.id not in env
            assert isinstance(t.right,ast.Constant) and t.right.value==1
            env[t.left.right.id]=1/value(t.left.left,env)
        assert value(t,env)==0
    return env

def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[0],-a[1]
def mul(a,b):return a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def con(a):return a[0],-a[1]
def div(a,b):
    c=mul(a,con(b));d=b[0]**2-2*b[1]**2
    return c[0]/d,c[1]/d

def check(candidate):
    candidate=Path(candidate)
    text=candidate.read_text()
    marker='X=v();'
    assert marker in text
    layer=text[:text.index(marker)]
    count=0
    for coordinates in [(F(2,3),F(-5,7),F(3,11),F(7,13)),
                        (F(0),F(1),F(2),F(0)),
                        (F(-4),F(0),F(0),F(3,8))]:
        ns={};exec(layer,ns)
        K,v=ns['K'],ns['v']
        a=K(v(),v());b=K(v(),v())
        aa,bb=coordinates[:2],coordinates[2:]
        cases=[(a+b,add(aa,bb)),(a-b,add(aa,neg(bb))),
               (a*b,mul(aa,bb)),(a/b,div(aa,bb)),
               (a.c(),con(aa)),(a**0,(F(1),F(0))),
               (a**3,mul(mul(aa,aa),aa)),
               (3+a,add((F(3),F(0)),aa)),
               (3-a,add((F(3),F(0)),neg(aa))),
               (3*a,mul((F(3),F(0)),aa)),
               (3/b,div((F(3),F(0)),bb))]
        norm=a.norm()
        env=fill(ns['E'],dict(zip(('x0','x1','x2','x3'),coordinates)))
        for actual,expected in cases:
            actual=(value(ast.parse(str(actual.x),mode='eval').body,env),
                    value(ast.parse(str(actual.y),mode='eval').body,env))
            assert actual==expected
            count+=1
        assert value(ast.parse(str(norm),mode='eval').body,env)==aa[0]**2-2*aa[1]**2
        count+=1
    ns={};exec(layer,ns)
    ns['S'](1)/0
    try:
        fill(ns['E'],{})
    except ZeroDivisionError:
        pass
    else:
        raise AssertionError('Zero denominator was not rejected')
    full=runpy.run_path(str(candidate))
    ds=[degree(ast.parse(row,mode='eval').body) for row in full['E']]
    assert full['polynomial']=='+'.join('('+row+')**2' for row in full['E'])
    return {
        'candidate':str(candidate),
        'sha256':hashlib.sha256(candidate.read_bytes()).hexdigest(),
        'bytes':len(candidate.read_bytes()),
        'exact_field_cases_passed':count,
        'zero_denominator_guard_checked':True,
        'all_output_residuals_integer_polynomials':True,
        'variables':full['n'],
        'residuals':len(full['E']),
        'maximum_residual_degree':max(ds),
        'polynomial_degree_bound':2*max(ds),
        'output_characters':len(full['polynomial']),
        'input_coordinate':'x0',
        'scope':'Compiler layer only; no claim of finite testing for arithmetic characterization.'
    }

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('candidate',type=Path)
    args=p.parse_args()
    print(json.dumps(check(args.candidate),indent=2))
