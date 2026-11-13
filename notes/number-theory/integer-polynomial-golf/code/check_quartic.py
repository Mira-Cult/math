"""Compare a generated polynomial with pinned upstream JSON coefficient tables.

Usage: python check_exact_payload.py CANDIDATE.py UPSTREAM_CLONE
No code from the upstream repository or the payload builder is imported.
"""
import argparse
import hashlib
import json
import runpy
from collections import defaultdict
from pathlib import Path

SOURCE_COMMIT = 'fa09c9c6c97982c13265e7088d95cdb61b3e90cf'
ROW_SHA = '84c1130856dfda7d3a489f3077d7bc378cd8e594198dd8f3c03fe50463606a93'
POLY_SHA = '727244236b25c1b1b54f6cc615433f6259440d28215b632de9d60bd4e50e2523'

def canonical(terms, A):
    out = defaultdict(int)
    for term in terms:
        out[tuple(term['monomial'])] += int(term['coefficient'])*A**term['parameterPower']
    return {m:c for m,c in out.items() if c}

def verify_payload(candidate, source_root):
    candidate = Path(candidate)
    source = Path(source_root)/'computation/quartic/family262_v21'
    row_path = source/'quadratic-family262-v21.json'
    poly_path = source/'polynomial-family262-v21.json'
    assert hashlib.sha256(row_path.read_bytes()).hexdigest() == ROW_SHA, 'Unpinned row table'
    assert hashlib.sha256(poly_path.read_bytes()).hexdigest() == POLY_SHA, 'Unpinned polynomial table'
    rows = json.loads(row_path.read_text())
    poly = json.loads(poly_path.read_text())
    A = 149**19365
    namespace = runpy.run_path(str(candidate))
    expected = canonical(poly['terms'], A)
    assert namespace['P'] == expected, 'Expanded polynomial differs from pinned upstream table'
    rows_checked = 0
    if 'R' in namespace or 'r' in namespace:
        actual_rows = namespace.get('R',namespace.get('r'))
        assert len(actual_rows) == len(rows['residuals']) == 234
        for k,(row,source_row) in enumerate(zip(actual_rows,rows['residuals'])):
            actual = defaultdict(int)
            for coefficient,monomial in row:
                actual[tuple(monomial)] += coefficient
            actual = {m:c for m,c in actual.items() if c}
            assert actual == canonical(source_row['terms'], A), f'Row {k+1} differs'
            rows_checked += 1
    if 'b' in namespace and hasattr(namespace['b'],'__next__'):
        assert list(namespace['b']) == [], 'Unconsumed payload bytes'
    assert max(map(len,expected)) == 4
    used = set(v for monomial in expected for v in monomial)
    assert used == set(range(1,263))
    assert rows['inputCoordinate'] == poly['inputCoordinate'] == 1
    assert len(expected) == 3494
    assert max(map(abs,expected.values())) == 149**38730+1
    return {
        'candidate':str(candidate),
        'candidate_sha256':hashlib.sha256(candidate.read_bytes()).hexdigest(),
        'candidate_characters':len(candidate.read_text()),
        'candidate_bytes':len(candidate.read_bytes()),
        'source_commit':SOURCE_COMMIT,
        'source_quadratic_sha256':ROW_SHA,
        'source_polynomial_sha256':POLY_SHA,
        'rows_identical':rows_checked,
        'polynomial_identical':True,
        'total_variables':262,
        'input_coordinate':1,
        'degree':4,
        'monomials':3494,
        'maximum_coefficient':'149^38730+1',
        'maximum_coefficient_bit_length':max(map(abs,expected.values())).bit_length(),
        'arithmetic_scope':'Algebraic identity only; integer-projection property retains upstream premises.'
    }

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidate', type=Path)
    parser.add_argument('source_root', type=Path)
    args = parser.parse_args()
    print(json.dumps(verify_payload(args.candidate,args.source_root),indent=2))
