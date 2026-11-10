"""Independent finite mathematical reference for the PA266 architecture phase.

No producer arithmetic or path evaluator is imported. This computes finite
records only; it does not evaluate infinite observer acceptance.
"""
from __future__ import annotations
from math import isqrt


def pair(a,b):
    s=a+b
    return s*(s+1)//2+b


def unpair(z):
    s=(isqrt(8*z+1)-1)//2
    b=z-s*(s+1)//2
    return s-b,b


def bit(container,index):
    return 0 if index>=container.bit_length() else (container>>index)&1


def list_code(values):
    code=0
    for value in reversed(values):code=1+pair(value,code)
    return code


def list_values(code):
    values=[]
    while code:
        value,tail=unpair(code-1)
        assert tail<code
        values.append(value);code=tail
    return values


def address(stage,schedule='legacy'):
    if schedule=='sentinel':
        formula,z=unpair(stage);values=list_values(z+1)
        return len(values),formula,values
    rank_minus_one,tail=unpair(stage);formula,tail=unpair(tail)
    values=[]
    for _ in range(rank_minus_one+1):
        value,tail=unpair(tail);values.append(value)
    return rank_minus_one+1,formula,values


def stage_for(rank,formula,values,schedule='legacy'):
    assert rank>0 and len(values)==rank
    if schedule=='sentinel':return pair(formula,list_code(values)-1)
    tail=0
    for value in reversed(values):tail=pair(value,tail)
    return pair(rank-1,pair(formula,tail))


def constructor(formula,syntax):
    if syntax=='head_cantor':
        tag,payload=unpair(formula)
        if tag==0:return 'atom',payload
        if tag==1:return 'qe',payload
        return 'nand',(tag-2,payload)
    if syntax=='nand_qe':
        payload,tag=divmod(formula,3)
        if tag==0:return 'atom',payload
        if tag==2:return 'qe',payload
        return 'nand',unpair(payload)
    if syntax=='cantor':
        tag,payload=unpair(formula)
        return ('atom',payload) if tag==0 else ('H',(tag-1,payload))
    payload,tag=divmod(formula,2)
    return ('atom',payload) if tag==0 else ('H',unpair(payload))


def atom_value(payload,values,atoms):
    def get(i):return values[i] if i<len(values) else 0
    if atoms=='head':i,j=payload+1,0
    else:
        a,b=unpair(payload)
        if atoms=='ordered':i,j=a+b,a
        elif atoms=='strict':i,j=a+b+1,a
        elif atoms=='younger':i,j=a,a+b+1
        else:i,j=a,b
    return bit(get(i),get(j))


def path(formula,values,moves,negative,syntax='parity',atoms='full',atom_slot=False):
    cursor=0
    while True:
        tag,payload=constructor(formula,syntax)
        if tag=='atom':
            if atom_slot and cursor==len(moves):return True
            return bool(atom_value(payload,values,atoms)) != negative
        if cursor==len(moves):return True
        move=moves[cursor];cursor+=1
        old_formula=formula
        if tag=='qe':
            formula=payload;values=[move]+values
        elif tag=='nand':
            formula=payload[0] if move==0 else payload[1]
        else:
            formula=payload[0] if move==0 else payload[1]
            values=[max(move-1,0)]+values
        assert formula<old_formula
        negative=not negative


def record(rank,formula,coordinates,*,prefix='numeric',syntax='parity',atoms='full',atom_slot=False):
    assert rank>0 and len(coordinates)==rank
    if prefix=='unary':
        C=coordinates[0];y=0;cursor=1
        while True:
            if cursor==rank:return 0
            decision=coordinates[cursor];cursor+=1
            if decision==0:break
            y+=1
            if cursor==rank:return 0
            cursor+=1  # ignored existential field after a grow
    else:
        if rank<2:return 0
        C,y=coordinates[:2];cursor=2
        if prefix=='guarded':
            if rank<formula+4 or y>rank-formula-4:return 0
        elif prefix=='spent':
            cursor+=2*pair(y,0)
            if cursor>rank:return 0
        elif y>rank-2:return 0
    negative=not bool(bit(C,y))
    if negative:
        if cursor==rank:return 0
        cursor+=1
    value=path(formula,[y],coordinates[cursor:],negative,syntax,atoms,atom_slot)
    return int(not value)


def frame(rank,formula,coordinates,value):
    result=[]
    for field in [rank,formula,*coordinates,value]:result.extend([1]*field+[0])
    return result
