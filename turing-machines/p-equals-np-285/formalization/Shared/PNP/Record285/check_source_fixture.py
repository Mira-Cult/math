"""Compare finite Lean controller checkpoints with the selected Python AST.

This instruments the original source immediately before its comparison-failure
branch. It checks a finite prefix and does not prove the source translation.
Run from any directory after building the Lean Source module.
"""
import ast
import hashlib
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
EXPECTED_SHA = '6a546f803146da357997fd7a19f98b07d3b74f1f720202fbf9a8b3bbffbf9af8'
LIMIT = 140

class InsertCheckpoint(ast.NodeTransformer):
    def __init__(self):
        self.matches = 0

    def visit_If(self, node):
        node = self.generic_visit(node)
        if (isinstance(node.test, ast.Name) and node.test.id == 'expected'
                and len(node.body) == 1 and isinstance(node.body[0], ast.Break)
                and not node.orelse):
            self.matches += 1
            args = [ast.Name(id=name, ctx=ast.Load()) for name in
                    ('program', 'exponent', 'n', 'radix', 'remaining', 'expected')]
            call = ast.Expr(value=ast.Call(func=ast.Name(id='_checkpoint', ctx=ast.Load()),
                                           args=args, keywords=[]))
            return [ast.copy_location(call, node), node]
        return node

source = (HERE / 'selected_source.py').read_bytes()
assert hashlib.sha256(source).hexdigest() == EXPECTED_SHA
transform = InsertCheckpoint()
tree = transform.visit(ast.parse(source, filename='selected_source.py'))
assert transform.matches == 1
ast.fix_missing_locations(tree)
actual = []

def checkpoint(program, exponent, n, radix, remaining, expected):
    actual.append((program, exponent, n, radix, remaining, bool(expected)))
    if len(actual) == LIMIT:
        raise StopIteration

namespace = {'beep': lambda: None, '_checkpoint': checkpoint}
exec(compile(tree, 'selected_source.py', 'exec'), namespace)
try:
    namespace['main']()
except StopIteration:
    pass
assert len(actual) == LIMIT

env = os.environ.copy()
env.setdefault('LEAN_PATH', str(REPO / '.lake/build/lib/lean'))
result = subprocess.run(['lean', str(HERE / 'SourceFixtures.lean')], cwd=REPO,
                        env=env, text=True, capture_output=True, check=True)
lean_trace = ast.literal_eval(result.stdout.replace('true', 'True').replace('false', 'False'))
assert len(lean_trace) >= LIMIT
for index, (source_row, lean_row) in enumerate(zip(actual, lean_trace)):
    if index == LIMIT:
        break
    assert source_row == lean_row, (index, source_row, lean_row)
print(f'{LIMIT} bounded-comparison checkpoints agree with the selected Python source')
