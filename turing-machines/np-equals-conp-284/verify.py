#!/usr/bin/env python3
"""Check source identity, closed local imports, pins, and the exact finite table.

This is not a Lean kernel check and proves no unbounded execution claim.
Requires Python 3.11 or newer and only its standard library.
"""
from __future__ import annotations
import ast
import hashlib
import json
from pathlib import Path
import re
import tomllib

ROOT = Path(__file__).resolve().parent
FORM = ROOT / 'formalization'
PIN = '6108c93565701e64775a3f1cbf9627d35c4c30e3'
TABLE_SHA256 = '0c924f63d3cdd89f97078aef409010fa868b189466ab186a17e105f81e9279aa'
ENDPOINT = 'Shared.Beeping.NPcoNP.Bootstrap284AlignedFromBlank'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def uncomment(text):
    """Remove nested Lean comments while preserving quoted literal contents."""
    out = []; i = depth = 0; quoted = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else:
                if text[i] == '\n': out.append('\n')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i+1 < len(text):
                out.append(text[i+1]); i += 2; continue
            if text[i] == '"': quoted = False
            i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            newline = text.find('\n', i)
            i = len(text) if newline < 0 else newline
        else:
            if text[i] == '"': quoted = True
            out.append(text[i]); i += 1
    require(depth == 0, 'Unterminated Lean comment')
    return ''.join(out)


def source_files():
    inventory = json.loads((ROOT / 'SOURCE-MANIFEST.json').read_text())
    require(inventory['source_commit'] == PIN, 'Unexpected source commit')
    seen = set()
    for entry in inventory['files']:
        path = entry['release_path']
        require(path not in seen, 'Duplicate manifest path: ' + path)
        seen.add(path)
        file = ROOT / path
        require(file.is_file() and not file.is_symlink(), 'Missing source: ' + path)
        data = file.read_bytes()
        require(len(data) == entry['bytes'], 'Length mismatch: ' + path)
        require(hashlib.sha256(data).hexdigest() == entry['sha256'], 'SHA-256 mismatch: ' + path)
        git_blob = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(git_blob == entry['git_blob'], 'Git blob mismatch: ' + path)
    return len(seen)


def lean_closure():
    expected = json.loads((ROOT / 'IMPORT-CLOSURE.json').read_text())
    todo = [ENDPOINT]; seen = set(); external = set(); includes = set()
    while todo:
        module = todo.pop()
        if module in seen: continue
        seen.add(module)
        path = Path(*module.split('.')).with_suffix('.lean')
        file = FORM / path
        require(file.is_file(), 'Missing local import: ' + str(path))
        text = uncomment(file.read_text())
        for line in re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)', text, re.M):
            for imp in line.split():
                if imp.startswith('Shared.') or imp == 'Shared': todo.append(imp)
                else:
                    require(imp.split('.')[0] in {'Mathlib', 'FormalConjecturesForMathlib', 'Lean', 'Std', 'Init'},
                            'Unexpected external import: ' + imp)
                    external.add(imp)
        for name in re.findall(r'include_str\s+"([^"\n]+)"', text):
            included = (file.parent / name).resolve()
            require(included.is_relative_to(FORM) and included.is_file(), 'Missing literal include: ' + name)
            includes.add(included.relative_to(FORM).as_posix())
    local = sorted(m.replace('.', '/') + '.lean' for m in seen)
    require(local == expected['local_lean_files'], 'Import closure changed')
    require(sorted(external) == expected['external_modules'], 'External import list changed')
    require(sorted(includes) == expected['literal_includes'], 'Literal include list changed')
    actual = sorted(p.relative_to(FORM).as_posix() for p in (FORM/'Shared').rglob('*.lean'))
    require(actual == local, 'Unexpected or omitted project Lean source')
    require((FORM/'Shared.lean').read_text() == 'import '+ENDPOINT+'\n', 'Unexpected public umbrella')
    return len(seen), len(external)


def table():
    data = (ROOT/'events.tm').read_bytes()
    require(hashlib.sha256(data).hexdigest() == TABLE_SHA256, 'Wrong machine digest')
    require(data == (FORM/'Shared/Beeping/NPcoNP/Inputs/selected284-events.tm').read_bytes(), 'Embedded table differs')
    headers = {}; rows = []
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! '):
            key, value = line[3:].split(maxsplit=1)
            require(key not in headers, 'Duplicate header')
            headers[key] = value
        elif line and not line.startswith('#'):
            q, read, write, direction, target, flag = line.split()
            q, read, write, target, flag = map(int, (q,read,write,target,flag))
            require(direction in ('L','R') and write in (0,1) and flag in (0,1) and 0 <= target < 284,
                    'Invalid table row')
            rows.append((q,read,write,direction,target,flag))
    require(headers == {'format':'beeper-events-v1','states':'284','start':'0','blank':'0','head':'0'}, 'Wrong table headers')
    require([(r[0],r[1]) for r in rows] == [(q,b) for q in range(284) for b in (0,1)], 'Rows not complete and ordered')
    require([r for r in rows if r[-1]] == [(99,1,0,'L',1,1)], 'Wrong event row')
    lean = (FORM/'Shared/Beeping/NPcoNP/Table284Data.lean').read_text()
    chunk = lean.split('def data : RawMachine := ',1)[1].split('\n\nend ',1)[0].strip()
    parsed = ast.literal_eval(re.sub(r'\bfalse\b','False',re.sub(r'\btrue\b','True',chunk)))
    require(parsed[0] == (0,(False,0)) and len(parsed[1]) == 284, 'Wrong numeric Lean header')
    literal = []
    for q,pair in enumerate(parsed[1]):
        for b,(w,(right,(target,flag))) in enumerate(pair):
            literal.append((q,b,int(w),'R' if right else 'L',target,int(flag)))
    require(rows == literal, 'Table differs from numeric Lean machine')
    return len(rows)


def pins():
    require((FORM/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1', 'Wrong Lean version')
    lake = tomllib.loads((FORM/'lakefile.toml').read_text())
    lock = json.loads((FORM/'lake-manifest.json').read_text())
    direct = {p['name']:(p['git'],p['rev']) for p in lake['require']}
    expected = {'mathlib':('https://github.com/leanprover-community/mathlib4.git','0df444a360eaa60ab8c11dca51a86af692955474'),
                'formal_conjectures':('https://github.com/google-deepmind/formal-conjectures.git','5a2fb85045c86e4a184b15ce7531ba199a3c4580')}
    require(direct == expected, 'Wrong direct dependency pins')
    require(len(lock['packages']) == 10, 'Unexpected locked package count')
    for p in lock['packages']:
        require(p['type'] == 'git' and re.fullmatch('[0-9a-f]{40}',p['rev']), 'Unpinned package')
        require(p['url'].startswith('https://github.com/'), 'Non-public dependency destination')
        if p['name'] in direct: require((p['url'],p['rev']) == direct[p['name']], 'Lock mismatch')
    return len(lock['packages'])


def companion():
    inputs=FORM/'Shared/Beeping/NPcoNP/Inputs'
    raw=(ROOT/'companion.tm').read_bytes()
    require(raw==(inputs/'selected285-exit.tm').read_bytes(),'Embedded companion differs')
    require(hashlib.sha256(raw).hexdigest()=='5b2e39f9df0b872c0854273df7f2b7f050fdce525363538dea5c9dfabdcad868','Wrong companion hash')
    quotient=json.loads((inputs/'selected284-event-quotient.json').read_text())
    mapping=quotient['mapping']
    require(len(mapping)==285 and set(mapping)==set(range(284)) and mapping[0]==0,'Wrong quotient map')
    target={}
    for line in (ROOT/'events.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,n,event=line.split()
            target[int(q),int(b)]=(int(w),d,int(n),int(event))
    headers={};seen=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! '):
            key,value=line[3:].split(maxsplit=1)
            require(key not in headers,'Duplicate companion header')
            headers[key]=value
        elif line and not line.startswith('#'):
            q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
            require(0<=q<285 and b in (0,1) and w in (0,1) and 0<=n<285 and d in ('L','R'),'Invalid companion row')
            require((w,d,mapping[n],int(n==1))==target[mapping[q],b],'Companion quotient mismatch')
            seen.append((q,b))
    require(headers=={'format':'beeper-v1','states':'285','start':'0','beep':'1','blank':'0','head':'0'},'Wrong companion headers')
    require(seen==[(q,b) for q in range(285) for b in (0,1)],'Companion rows not complete and ordered')
    return len(seen)


def main():
    n = source_files(); m, e = lean_closure(); rows = table(); packages = pins(); other = companion()
    print(f'PASS: {n} unchanged upstream source/data files; {m} local Lean modules; {e} external import modules; {rows} literal rows; {other} companion quotient rows; {packages} locked packages.')
    print('No Lean kernel replay or infinite-run claim follows from these finite checks.')


if __name__ == '__main__':
    main()
