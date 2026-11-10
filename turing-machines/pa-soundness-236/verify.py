#!/usr/bin/env python3
"""Finite source/format checks. This does not decide omega-acceptance."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
PINS = {
    'machine.tm': (236, 'bcf4a1fd22e9959a4145688d05ec20591d97967050ad1a16beeb22a187edaedc'),
    'raw.tm': (237, 'e73b3c7fbcbbc4614e4ee33a6e33cacfb3b8e2dc32822591db2afdfedf01a9e8'),
}

def check(ok, message):
    if not ok:
        raise ValueError(message)


def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def parse_table(name):
    n, digest = PINS[name]
    data = (ROOT / name).read_bytes()
    check(hashlib.sha256(data).hexdigest() == digest, name + ': hash')
    check(data == (ROOT / 'formalization/bindings/m236' / name).read_bytes(), name + ': embedded copy')
    lines = data.decode('ascii').splitlines()
    check(lines[:5] == ['#! format bit-events-v1', f'#! states {n}', '#! start 0', '#! blank 0', '#! head 0'], name + ': header')
    check(len(lines) == 5 + 2*n, name + ': row count')
    rows = []
    for i, line in enumerate(lines[5:]):
        parts = line.split()
        check(len(parts) == 6, name + ': six columns')
        q, rd, wr, direction, target, event = parts
        check(q == str(i//2) and rd == str(i%2), name + ': row order')
        check(wr in ('0','1') and direction in ('L','R') and event in ('-','0','1'), name + ': row alphabet')
        check(target.isdigit() and 0 <= int(target) < n, name + ': target')
        rows.append((int(wr), direction, int(target), event))
    return rows


def check_manifest():
    manifest = json.loads((ROOT / 'SOURCE-MANIFEST.json').read_text())
    paths = set()
    for entry in manifest['files']:
        p = entry['path']
        check(p not in paths and '..' not in Path(p).parts, 'manifest path')
        paths.add(p)
        data = (ROOT / p).read_bytes()
        check(len(data) == entry['size'], p + ': length')
        check(hashlib.sha256(data).hexdigest() == entry['sha256'], p + ': SHA-256')
        check(git_blob(data) == entry['git_blob'], p + ': Git blob')
    print(f"Verified {len(paths)} byte-identical upstream files")


def check_lean_closure():
    lean = ROOT / 'formalization/lean'
    files = list(lean.rglob('*.lean'))
    imports = includes = 0
    for p in files:
        source = p.read_text()
        for module in re.findall(r'^import\s+([\w.]+)', source, re.M):
            if module.split('.')[0] in ('PASoundness', 'Shared'):
                check((lean / (module.replace('.', '/') + '.lean')).is_file(), str(p) + ': missing ' + module)
                imports += 1
        for line in source.splitlines():
            if not re.match(r'^def \w+ : String := include_str ', line):
                continue
            names = re.findall(r'"([^"]+)"', line.split('include_str', 1)[1])
            check(names and (p.parent.joinpath(*names)).is_file(), str(p) + ': literal include')
            includes += 1
    check(includes == 4, 'unexpected include_str inventory')
    check((lean / 'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.33.1', 'Lean toolchain')
    lock = json.loads((lean / 'lake-manifest.json').read_text())
    check(len(lock['packages']) == 9, 'dependency count')
    check(next(x['rev'] for x in lock['packages'] if x['name'] == 'mathlib') == '0df444a360eaa60ab8c11dca51a86af692955474', 'mathlib pin')
    check(all(re.fullmatch('[0-9a-f]{40}', x['rev']) for x in lock['packages']), 'unpinned package')
    print(f'Local import/include closure: {len(files)} Lean modules, {imports} local imports, {includes} literal includes')


def decode(bits):
    """Small independent finite-prefix parser for documented controls."""
    ones = 0
    fields = []
    target = None
    records = {}
    for bit in bits:
        check(bit in (0,1), 'non-bit')
        if bit:
            ones += 1
            continue
        number, ones = ones, 0
        fields.append(number)
        if target is None:
            if number == 0:
                return True, False, records
            target = number + 3
        if len(fields) == target:
            n, p, *tail = fields
            xs, value = tuple(tail[:-1]), tail[-1]
            key = n, p, xs
            if value not in (0,1) or (key in records and records[key] != value):
                return True, False, records
            records[key] = value
            fields, target = [], None
    return False, not fields and ones == 0, records


def check_controls():
    z = [1,0,0,0,0]
    one = [1,0,0,0,1,0]
    check(decode(z) == (False, True, {(1,0,(0,)):0}), 'zero frame')
    check(decode(z+z) == decode(z), 'equal duplicate')
    check(decode(z+one)[0], 'conflict')
    check(decode([0])[0], 'zero rank')
    check(not decode([1])[1], 'unfinished unary field')
    check(decode([]) == (False, True, {}), 'silence has no records')
    check(all(not decode(z[:i])[2] for i in range(len(z))), 'proper prefix is unfinished')
    print('Finite parser controls passed; no inference of infinite coverage or strategies')


def main():
    check_manifest()
    selected, raw = parse_table('machine.tm'), parse_table('raw.tm')
    marks = {(i//2,i%2):r[3] for i,r in enumerate(selected) if r[3] != '-'}
    check(marks == {(134,0):'1',(136,0):'1',(137,1):'0',(146,0):'0'}, 'output labels')
    mapping = json.loads((ROOT / 'formalization/bindings/m236/quotient.json').read_text())['quotient']['state_map']
    check(len(mapping) == 237 and mapping[0] == 0 and set(mapping) == set(range(236)), 'quotient map')
    for i, (write, direction, target, event) in enumerate(raw):
        check(selected[2*mapping[i//2]+i%2] == (write,direction,mapping[target],event), f'quotient row {i}')
    print('Literal tables: 472/474 rows; all 474 output-coloured quotient equations passed')
    check_lean_closure()
    check_controls()
    print('Finite verification PASS. This is not a Lean rebuild or a proof of omega-acceptance.')

if __name__ == '__main__':
    main()
