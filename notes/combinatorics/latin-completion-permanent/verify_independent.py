#!/usr/bin/env python3
"""Independent exact tests of the public Latin-completion matrix generator.

Usage: python verify_independent.py PATH/TO/construct.py
No generator or original audit code is reused in either counting oracle.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import product, permutations
from pathlib import Path
import argparse,hashlib,importlib.util,json,sys


def permanent(matrix):
    """Generic weighted permanent, dynamically expanding a minimum-degree vertex."""
    n=len(matrix)
    row=[sum(1<<j for j,x in enumerate(r) if x) for r in matrix]
    col=[sum(1<<i for i in range(n) if matrix[i][j]) for j in range(n)]
    @lru_cache(None)
    def expand(rows,columns):
        if not rows:return 1
        best=(n+1,0,0,0)
        todo=rows
        while todo:
            bit=todo&-todo;i=bit.bit_length()-1;todo-=bit
            neighbors=row[i]&columns
            if neighbors.bit_count()<best[0]:best=(neighbors.bit_count(),0,i,neighbors)
        todo=columns
        while todo:
            bit=todo&-todo;j=bit.bit_length()-1;todo-=bit
            neighbors=col[j]&rows
            if neighbors.bit_count()<best[0]:best=(neighbors.bit_count(),1,j,neighbors)
        degree,side,v,neighbors=best
        if not degree:return 0
        result=0
        while neighbors:
            bit=neighbors&-neighbors;w=bit.bit_length()-1;neighbors-=bit
            i,j=(v,w) if side==0 else (w,v)
            result+=matrix[i][j]*expand(rows^(1<<i),columns^(1<<j))
        return result
    return expand((1<<n)-1,(1<<n)-1)


def latin_completions(grid):
    """Count row-permutation tuples with distinct symbols in every column."""
    n=len(grid)
    rows=[[p for p in permutations(range(n))
           if all(clue is None or clue==value for clue,value in zip(row,p))
           and all(all(grid[k][j] is None or k==i or grid[k][j]!=p[j]
                       for k in range(n)) for j in range(n))]
          for i,row in enumerate(grid)]
    return sum(all(len({square[i][j] for i in range(n)})==n for j in range(n))
               for square in product(*rows))


def all_latin(n):
    return tuple(square for square in product(tuple(permutations(range(n))),repeat=n)
                 if all(len({square[i][j] for i in range(n)})==n for j in range(n)))


def matches(grid,square):
    return all(x is None or x==y for r,s in zip(grid,square) for x,y in zip(r,s))


def check(module,grid,expected):
    snapshot=[r[:] for r in grid]
    result=module.construct(grid)
    assert grid==snapshot,'Input mutated'
    assert 1<=result.order<=len(grid)**3+2*len(grid)**2
    assert len(result.entries)<=5*len(grid)**3+len(grid)**2
    assert all(0<=i<result.order and 0<=j<result.order for i,j in result.entries)
    assert set(result.entries.values())<={Fraction(-1),Fraction(1,2),Fraction(1)}
    encoded=result.as_json()
    assert encoded['entries']==sorted(encoded['entries'])
    assert {(i,j):Fraction(value) for i,j,value in encoded['entries']}==result.entries
    if result.metadata['outcome']=='residual':
        h,t=result.metadata['h'],result.metadata['t']
        assert result.order==t+2*h
        assert len(result.entries)==5*t+h
        assert sum(x==1 for x in result.entries.values())==4*t
        assert sum(x==-1 for x in result.entries.values())==t
        assert sum(x==Fraction(1,2) for x in result.entries.values())==h
        assert all(len(block['symbols'])>=2 for block in result.metadata['blocks'])
    obtained=permanent(result.dense())
    assert obtained==expected,(grid,result.metadata,expected,obtained)
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('generator',type=Path);args=parser.parse_args()
    spec=importlib.util.spec_from_file_location('reviewed_construct',args.generator)
    module=importlib.util.module_from_spec(spec);sys.modules[spec.name]=module;spec.loader.exec_module(module)
    report={'generator_sha256':hashlib.sha256(args.generator.read_bytes()).hexdigest(),
            'reviewer_verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'arithmetic':'exact integers and rational fractions',
            'permanent_method':'dynamic minimum-degree row/column expansion with memoization',
            'latin_method':'independent enumeration of row permutations with column uniqueness'}
    malformed=[None,{},[],[[]],[[None,None]],[[None],[None]],[[1]],[[True]],[[False]],[[0.0]],[["0"]],[[-1]],[[None,0],[1,2]],[[None,0],(1,None)]]
    for grid in malformed:
        try:module.construct(grid)
        except ValueError:pass
        else:raise AssertionError(('malformed input accepted',grid))
    report['malformed_inputs_rejected']=len(malformed)
    report['exhaustive']=[]
    for n in (1,2,3):
        squares=all_latin(n);counts={'zero':0,'one':0,'residual':0};max_dimension=0;total=0
        for values in product((None,*range(n)),repeat=n*n):
            grid=[list(values[i*n:(i+1)*n]) for i in range(n)]
            expected=sum(matches(grid,s) for s in squares)
            result=check(module,grid,expected)
            counts[result.metadata['outcome']]+=1;total+=1;max_dimension=max(max_dimension,result.order)
        report['exhaustive'].append({'n':n,'grids':total,'outcomes':counts,'max_dimension':max_dimension,'latin_squares':len(squares)})
        print(json.dumps({'progress':report['exhaustive'][-1]}),file=sys.stderr,flush=True)
    larger=[]
    for n in range(4,8):
        for delta in range(1,n):
            grid=[[(i+j)%n if i not in (0,delta) else None for j in range(n)] for i in range(n)]
            expected=latin_completions(grid);result=check(module,grid,expected)
            larger.append({'n':n,'missing_rows':[0,delta],'order':result.order,'count':expected})
    report['larger_two_row_hole_cases']=larger
    # Nontrivial cancellation must produce zero even though all external requirements have support.
    # The exhaustive small grids already include all such examples, if any occur at n<=3.
    report['status']='passed'
    report['total_completion_permanent_comparisons']=sum(x['grids'] for x in report['exhaustive'])+len(larger)
    report['skipped_well_formed_test_inputs']=0
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
