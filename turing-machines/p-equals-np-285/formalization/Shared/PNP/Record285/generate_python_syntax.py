#!/usr/bin/env python3
"""Generate an untrusted typed syntax listing of the frozen Python source.

Lean checks that the listing renders back to the entire exact file. This tool
uses CPython's parser to propose the tree and is not a proof of Python semantics.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
raw = (here / 'selected_source.py').read_bytes()
if hashlib.sha256(raw).hexdigest() != '6a546f803146da357997fd7a19f98b07d3b74f1f720202fbf9a8b3bbffbf9af8':
    raise ValueError('unexpected source bytes')
text = raw.decode('ascii')
lines = text.splitlines(keepends=True)
tree = ast.parse(text)
funcs = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
if len(funcs) != 2 or [n.name for n in funcs] != ['accept', 'main']:
    raise ValueError('unexpected source functions')

def string(x):
    return json.dumps(x, ensure_ascii=True)

def expr(n):
    if isinstance(n, ast.Name): return f'.name {string(n.id)}'
    if isinstance(n, ast.Constant):
        if n.value is True: return '.truth'
        if type(n.value) is int and n.value >= 0: return f'.num {n.value}'
    if isinstance(n, ast.BinOp):
        op = {ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul',ast.FloorDiv:'div',
              ast.Mod:'mod',ast.Pow:'pow'}.get(type(n.op))
        if op: return f'.binary .{op} ({expr(n.left)}) ({expr(n.right)})'
    if isinstance(n, ast.Compare) and len(n.ops)==1 and isinstance(n.ops[0],ast.Eq):
        return f'.binary .eq ({expr(n.left)}) ({expr(n.comparators[0])})'
    raise ValueError(f'unsupported expression: {ast.dump(n)}')

def name(n):
    if not isinstance(n,ast.Name): raise ValueError('non-name assignment')
    return n.id

def liststr(xs):
    return '[' + ', '.join(xs) + ']'

out = []
def emit(stmt):
    i = stmt.col_offset
    if isinstance(stmt, ast.While):
        if stmt.orelse: raise ValueError('while/else unsupported')
        out.append(f'.while_ {i} ({expr(stmt.test)})')
        for child in stmt.body: emit(child)
    elif isinstance(stmt, ast.If):
        out.append(f'.if_ {i} ({expr(stmt.test)})')
        for child in stmt.body: emit(child)
        if stmt.orelse:
            out.append(f'.else_ {i}')
            for child in stmt.orelse: emit(child)
    elif isinstance(stmt, ast.Assign) and len(stmt.targets)==1:
        target = stmt.targets[0]
        if isinstance(target,ast.Tuple) and isinstance(stmt.value,ast.Tuple):
            out.append(f'.assignMany {i} {liststr([string(name(x)) for x in target.elts])} '
                       f'{liststr(["("+expr(x)+")" for x in stmt.value.elts])}')
        else:
            out.append(f'.assign {i} {string(name(target))} ({expr(stmt.value)})')
    elif isinstance(stmt,ast.AugAssign):
        op = {ast.Add:'+',ast.Sub:'-',ast.Mult:'*',ast.FloorDiv:'//'}.get(type(stmt.op))
        if op is None: raise ValueError('unsupported augmented assignment')
        out.append(f'.aug {i} {string(name(stmt.target))} {string(op)} ({expr(stmt.value)})')
    elif isinstance(stmt,ast.Break): out.append(f'.break_ {i}')
    elif isinstance(stmt,ast.Return): out.append(f'.return_ {i} ({expr(stmt.value)})')
    elif isinstance(stmt,ast.Expr) and isinstance(stmt.value,ast.Call):
        call = stmt.value
        if call.args or call.keywords: raise ValueError('unsupported call arguments')
        out.append(f'.call {i} {string(name(call.func))}')
    else: raise ValueError(f'unsupported statement: {ast.dump(stmt)}')

prefix = ''.join(lines[:funcs[0].lineno-1])
for index, func in enumerate(funcs):
    if index: out.append('.blank')
    out.append(f'.function {string(func.name)} {liststr([string(x.arg) for x in func.args.args])}')
    for stmt in func.body: emit(stmt)
source_lines = lines[funcs[0].lineno-1:]
if len(source_lines) != len(out): raise ValueError('syntax/source line count differs')
chunks = [(out[i:i+5], ''.join(source_lines[i:i+5])) for i in range(0,len(out),5)]
data = ['import Shared.PNP.Record285.PythonSyntax', '',
    '/-! Untrusted syntax proposal generated from the frozen Python source. -/',
    'namespace Shared.PNP.Record285.PythonSyntax', '',
    f'def sourceHeader : String := {string(prefix)}', '']
for i,(entries,_) in enumerate(chunks):
    data.extend([f'def lines{i} : List Line := [',
                 ',\n'.join('  ' + x for x in entries),']',''])
data.append(f'def linesFrom{len(chunks)} : List Line := []')
for i in reversed(range(len(chunks))):
    data.append(f'def linesFrom{i} : List Line := lines{i} ++ linesFrom{i+1}')
data.extend(['', 'def sourceLines : List Line := linesFrom0',
    'def renderedSource : String := sourceHeader ++ renderLines sourceLines',
    'def literalSource : String := include_str "selected_source.py"', '',
    'end Shared.PNP.Record285.PythonSyntax', ''])

def char(c):
    if c == '\n': return "'\\n'"
    if c == "'": return "'\\\''"
    if c == '\\': return "'\\\\'"
    if 32 <= ord(c) <= 126: return "'"+c+"'"
    raise ValueError(f'unexpected character {c!r}')

def chars(s): return '[' + ','.join(char(c) for c in s) + ']'

cert = ['import Shared.PNP.Record285.PythonSyntaxData', '',
    '/-! Exact text binding; the generator is not trusted. This certifies',
    'syntax rendering, not Python execution semantics. -/',
    'set_option maxRecDepth 131072', 'set_option maxHeartbeats 0',
    'namespace Shared.PNP.Record285.PythonSyntax', '',
    'theorem render_append (a b : List Line) :',
    '    renderLines (a ++ b) = renderLines a ++ renderLines b := by',
    '  simp [renderLines, List.map_append, String.join_append]', '',
    f'def literalChars : List Char := {chars(text)}',
    'theorem literal_chars : literalSource = String.ofList literalChars := by rfl',
    f'def headerChars : List Char := {chars(prefix)}',
    'theorem header_chars : sourceHeader = String.ofList headerChars := by rfl', '']
for i,(_,chunk) in enumerate(chunks):
    cert.extend([f'def chars{i} : List Char := {chars(chunk)}',
                 f'theorem chunk{i} : renderLines lines{i} = String.ofList chars{i} := by decide',''])
cert.extend([f'def charsFrom{len(chunks)} : List Char := []',
             f'theorem segment{len(chunks)} : renderLines linesFrom{len(chunks)} = String.ofList charsFrom{len(chunks)} := by rfl'])
for i in reversed(range(len(chunks))):
    cert.extend([f'def charsFrom{i} : List Char := chars{i} ++ charsFrom{i+1}',
        f'theorem segment{i} : renderLines linesFrom{i} = String.ofList charsFrom{i} := by',
        f'  simp only [linesFrom{i}, charsFrom{i}, render_append, chunk{i}, segment{i+1}, String.ofList_append]', ''])
cert.extend(['theorem chars_concat : literalChars = headerChars ++ charsFrom0 := by rfl', '',
    'theorem literal_source_is_rendered : literalSource = renderedSource := by',
    '  rw [literal_chars,chars_concat,String.ofList_append,←header_chars,←segment0]',
    '  rfl', '', 'end Shared.PNP.Record285.PythonSyntax', ''])

for path,contents in [(here / 'PythonSyntaxData.lean', '\n'.join(data)),
                      (here / 'PythonSyntaxCertificate.lean', '\n'.join(cert))]:
    if args.check:
        if path.read_text() != contents: raise ValueError(f'generated syntax differs: {path.name}')
    else:
        path.write_text(contents)
print(f'{len(out)} typed lines; {len(raw)} source bytes')
