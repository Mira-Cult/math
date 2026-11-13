"""Author checks using separate finite-field arithmetic; not an arithmetic theorem certificate."""
import ast
import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = HERE / 'generate.py'
spec = importlib.util.spec_from_file_location('golf', source)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)

definitions = []
defined = set()
for residual in m.E:
    gate = re.fullmatch(r'x(\d+)-\((.*)\)', residual)
    inverse = re.fullmatch(r'\((.*)\)\*x(\d+)-1', residual)
    if gate:
        idx, expression = int(gate[1]), gate[2]
        definitions.append(('gate', idx, ast.parse(expression, mode='eval').body))
        defined.add(idx)
    elif inverse:
        expression, idx = inverse[1], int(inverse[2])
        definitions.append(('inverse', idx, ast.parse(expression, mode='eval').body))
        defined.add(idx)
    else:
        assert re.fullmatch(r'x\d+', residual)
        definitions.append(('zero', int(residual[1:]), None))
free = sorted(set(range(m.n)) - defined)
assert len(free) == 54


def run(p):
    def fadd(u, v): return ((u[0]+v[0]) % p, (u[1]+v[1]) % p)
    def fneg(u): return (-u[0] % p, -u[1] % p)
    def fsub(u, v): return fadd(u, fneg(v))
    def fmul(u, v): return ((u[0]*v[0]+2*u[1]*v[1]) % p,
                           (u[0]*v[1]+u[1]*v[0]) % p)
    def fpow(u, n):
        result = (1, 0)
        while n:
            if n & 1: result = fmul(result, u)
            u = fmul(u, u)
            n //= 2
        return result
    def finv(u):
        inverse = pow((u[0]*u[0]-2*u[1]*u[1]) % p, -1, p)
        return (u[0]*inverse % p, -u[1]*inverse % p)
    def fdiv(u, v): return fmul(u, finv(v))
    def conj(u): return (u[0], -u[1] % p)
    def norm(u): return (u[0]*u[0]-2*u[1]*u[1]) % p
    D = (11, -6 % p)
    def ecadd(A, B):
        if A is None: return B
        if B is None: return A
        x, y = A; u, v = B
        if x == u:
            if y == fneg(v): return None
            slope = fdiv(fsub(fmul((3, 0), fmul(x, x)), D), fmul((2, 0), y))
        else:
            slope = fdiv(fsub(v, y), fsub(u, x))
        X = fsub(fsub(fmul(slope, slope), x), u)
        return X, fsub(fmul(slope, fsub(x, X)), y)
    def ecmul(A, n):
        result = None
        while n:
            if n & 1: result = ecadd(result, A)
            A = ecadd(A, A)
            n //= 2
        return result
    def ecsub(A, B): return ecadd(A, (B[0], fneg(B[1])))
    def formal(A): return fdiv(fneg(A[0]), A[1])
    R0 = ((1, 1), (0, 2))
    P = ecmul(R0, 2)
    labels, h, X, lam = [2963, 5, 7, 11], 17, 3, 100000
    lifts = [ecmul(R0, n) for n in labels + [h*n for n in labels] + [h]]
    freevalues = [X]
    for A in lifts: freevalues.extend(A[0]+A[1])
    freevalues.extend([2, 3, 4, 5])  # arbitrary scalar-pole witnesses
    freevalues.append(lam)
    freevalues.extend([2, 3, 4, 5]*3)  # arbitrary comparison-pole witnesses
    assert len(freevalues) == len(free)
    values = dict(zip(free, freevalues))

    def evaluate(node):
        if isinstance(node, ast.Constant): return node.value % p
        if isinstance(node, ast.Name): return values[int(node.id[1:])]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -evaluate(node.operand) % p
        assert isinstance(node, ast.BinOp)
        a = evaluate(node.left)
        if isinstance(node.op, ast.Pow):
            return pow(a, ast.literal_eval(node.right), p)
        b = evaluate(node.right)
        if isinstance(node.op, ast.Add): return (a+b) % p
        if isinstance(node.op, ast.Sub): return (a-b) % p
        if isinstance(node.op, ast.Mult): return a*b % p
        raise AssertionError(ast.dump(node))

    zero_values = []
    for kind, idx, expr in definitions:
        if kind == 'zero': zero_values.append(values[idx])
        elif kind == 'gate': values[idx] = evaluate(expr)
        else: values[idx] = pow(evaluate(expr), -1, p)
    assert zero_values[:18] == [0]*18  # nine free elliptic lifts
    assert len(zero_values) == 26
    # Pole witnesses were deliberately arbitrary. Their eight final equations
    # are not asserted true; checking them finitely would not prove realization.
    for residual in m.E:
        if not re.fullmatch(r'x\d+', residual):
            assert evaluate(ast.parse(residual, mode='eval').body) == 0

    def scalar(symbol): return values[int(symbol[1:])]
    def field(symbol): return scalar(symbol.x), scalar(symbol.y)
    Q = [ecmul(P, n) for n in labels]
    U = [ecmul(P, h*n) for n in labels]
    H = ecmul(P, h)
    V = [ecsub(H, P)] + [ecsub(u, q) for u, q in zip(U, Q)]
    assert [(field(a), field(b)) for a, b in m.Q] == Q
    assert [(field(a), field(b)) for a, b in m.U] == U
    assert (field(m.H[0]), field(m.H[1])) == H
    assert [(field(a), field(b)) for a, b in m.V] == V
    beta = 51*X*X+2504
    r = beta*(beta-1)*(beta-2401)*(32*beta+343)*(2*beta-1) % p
    R = pow(149, 19365, p)*r*pow(1+22201*r, -1, p) % p
    assert scalar(m.R) == R
    Z = fdiv(formal(ecsub(Q[1], P)), formal(H))
    assert field(m.Z) == Z
    assert scalar(m.F) == norm(finv(H[0]))
    L = [fdiv(formal(u), formal(H)) for u in U]
    C = [fsub(l, conj(fdiv(formal(v), formal(V[0])))) for l, v in zip(L, V[1:])]
    assert [field(l) for l in m.L] == L
    assert [field(c) for c in m.C] == C
    a, b, c, d = L
    bm2 = fsub(b, (2, 0))
    G = fsub(fadd(fsub(fmul(c, c), fmul(fmul(b, bm2), fmul(c, d))),
                       fmul(fmul(bm2, bm2), fmul(d, d))), (1, 0))
    fs = [finv(u[0]) for u in [H]+U] + [conj(finv(v[0])) for v in V]
    cs = C+[fsub(a, (beta, 0)), G]
    assert [field(f) for f in m.fs] == fs
    assert [field(c) for c in m.cs] == cs
    T = (0, 0)
    for q in Q: T = fadd(T, q[0])
    assert field(m.T) == T
    t = (T[0]+T[1])**2*lam % p
    theta = [0, -pow(2, -1, p), -1, pow(2399, -1, p), -32*pow(407, -1, p)]
    f = 1
    for a in theta: f = f*(t-a)*(t-2+a) % p
    q = (pow(t-1, 10, p)*pow(f, -1, p)-1) % p
    W = (1, 0)
    for group, k in [(fs, 3), (cs, 5)]:
        for a in group:
            W = fmul(W, fadd((1, 0), fmul(fpow(a, 2), (pow(q, k, p), 0))))
    assert scalar(m.q) == q and field(m.W) == W
    assert scalar(m.tau) == norm(W)*pow(2*W[0], -1, p) % p
    return {'prime': p, 'gate_residuals_checked': len(m.E)-26,
            'curve_component_residuals_checked': 18,
            'point_and_scalar_and_comparison_outputs': 'match independent arithmetic',
            'pole_realization': 'not tested or claimed'}


def degree(node):
    if isinstance(node, ast.Constant):
        assert isinstance(node.value, int)
        return 0
    if isinstance(node, ast.Name):
        assert re.fullmatch(r'x\d+', node.id)
        return 1
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub): return degree(node.operand)
    assert isinstance(node, ast.BinOp)
    if isinstance(node.op, ast.Pow):
        exponent = ast.literal_eval(node.right)
        assert isinstance(exponent, int) and exponent >= 0
        return degree(node.left)*exponent
    a, b = degree(node.left), degree(node.right)
    if isinstance(node.op, (ast.Add, ast.Sub)): return max(a, b)
    assert isinstance(node.op, ast.Mult)
    return a+b

degrees = [degree(ast.parse(r, mode='eval').body) for r in m.E]
assert max(degrees) == 2 and degrees.count(2) == 1588
report = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'source_ascii_bytes': len(source.read_bytes()), 'variables': m.n,
          'residuals': len(m.E), 'polynomial_expression_bytes': len(m.polynomial),
          'max_residual_degree': 2, 'polynomial_degree': 4,
          'free_coordinates': len(free), 'modular_checks': [run(p) for p in [1000003,1000037]],
          'scope': 'Finite algebraic compiler/circuit checks, not the inherited arithmetic premises.'}
print(json.dumps(report, indent=2))
