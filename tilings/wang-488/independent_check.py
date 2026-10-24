"""Independent finite audit of the pinned K215/488-tile data; no compiler imports."""
import argparse
from pathlib import Path
from hashlib import sha256
import json

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('machine', type=Path, help='Pinned primary k215.tm input')
parser.add_argument('--data-dir', type=Path, default=Path(__file__).resolve().parent)
parser.add_argument('--output', type=Path, help='Optional JSON result path')
args = parser.parse_args()
SRC = args.data_dir
EXPECTED = {
    'k215.tm': 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
    'k215_diagonal_488.tsv': '371ebc4063c47ba3491d99c6884faa43633d3ea2600411d9eee9b4a020207017',
    'k215_window_certificate.json': 'b2f347a7bdb17320ad32a6d18347bf1a2d987b8ab5f966aa8bac9397eab7a62a',
}
for name, digest in EXPECTED.items():
    path = args.machine if name == 'k215.tm' else SRC / name
    assert sha256(path.read_bytes()).hexdigest() == digest, name

machine = {}
for line in args.machine.read_text().splitlines():
    if not line.strip() or line.lstrip().startswith('#'):
        continue
    q, a, b, direction, target = line.split()
    q, a, b, target = map(int, (q, a, b, target))
    assert (q, a) not in machine
    assert a in (0, 1) and b in (0, 1) and direction in ('L', 'R')
    machine[q, a] = (target, b, direction)
assert set(machine) == {(q, a) for q in range(215) for a in (0, 1)}
assert [(k, v) for k, v in machine.items() if v[0] == 215] == [((68, 1), (215, 1, 'R'))]
assert all(0 <= v[0] <= 215 for v in machine.values())

cert = json.loads((SRC / 'k215_window_certificate.json').read_text())
assert cert['radius'] == 1 and cert['start_state'] == 0 and cert['blank'] == 0
states = set(map(tuple, cert['states']))
assert len(states) == len(cert['states']) == 1173
assert (0, 0, 'start') in states
for q, word, incoming in states:
    assert isinstance(q, int) and 0 <= q <= 215
    assert isinstance(word, int) and 0 <= word < 8
    assert incoming in ('start', 'L', 'R')
    left, center, right = word % 2, (word // 2) % 2, word // 4
    if (q, center) not in machine:
        continue
    target, write, direction = machine[q, center]
    for bit in (0, 1):
        new = write + 2 * right + 4 * bit if direction == 'R' else bit + 2 * left + 4 * write
        assert (target, new, direction) in states

allowed = {(q, d, (word // 2) % 2) for q, word, d in states if d in ('L', 'R')}
allowed.add((0, 'R', 0))
working = set(range(215))
trimmed = {k: v for k, v in machine.items() if v[0] in working}
entered = {(v[0], v[2]) for v in trimmed.values()} | {(0, 'R')}
assert len(entered) == 243
impossible = {(q, d, a) for q, d in entered for a in (0, 1) if (q, a) in trimmed} - allowed
assert impossible == {(10, 'L', 1), (11, 'L', 1), (35, 'L', 1), (42, 'L', 0), (134, 'L', 0)}

fixed = {106: 0, 14: 0, 39: 0, 56: 0, 24: 0, 49: 0, 82: 1, 79: 1}
predecessor_report = {}
for intermediate, bit in fixed.items():
    predecessors = {k: v for k, v in machine.items() if v[0] == intermediate}
    assert intermediate != 0 and predecessors
    assert all(v[1:] == (bit, 'R') for v in predecessors.values())
    predecessor_report[str(intermediate)] = {'forced_previous_write': bit, 'all_predecessors': sorted(predecessors)}
for target, _, forbidden_bit in impossible:
    predecessors = {k: v for k, v in machine.items() if v[0] == target and v[2] == 'L'}
    assert predecessors and all(k[0] in fixed and fixed[k[0]] == 1 - forbidden_bit for k in predecessors)

symbol = lambda bit: f'sym:{bit}'
head = lambda q: f'head:{q}'
symbols = {(symbol(a), symbol(b), symbol(b), symbol(a)) for a in (0, 1) for b in (0, 1)}
seed = ('wall:start', 'init:R', 'bottom', 'sym:0')
boundaries = {seed, ('sym:0', 'init:R', 'bottom', 'init:R'), ('wall', 'head:0', 'wall:start', 'sym:0'), ('wall', 'sym:0', 'wall', 'sym:0')}
instructions = set()
for (q, a), (target, write, move) in trimmed.items():
    n, e = (symbol(write), head(target)) if move == 'R' else (head(target), symbol(write))
    if (q, 'R') in entered and (q, 'R', a) in allowed:
        instructions.add((n, e, symbol(a), head(q)))
    if (q, 'L') in entered and (q, 'L', a) in allowed:
        instructions.add((n, e, head(q), symbol(a)))
expected_tiles = tuple(sorted(instructions | symbols | boundaries))
assert (len(instructions), len(symbols), len(boundaries), len(expected_tiles)) == (480, 4, 4, 488)
actual, marked = [], []
for line in (SRC / 'k215_diagonal_488.tsv').read_text().splitlines()[1:]:
    index, is_seed, *tile = line.split('\t')
    assert int(index) == len(actual) and is_seed in ('0', '1') and len(tile) == 4
    actual.append(tuple(tile))
    if is_seed == '1':
        marked.append(int(index))
assert tuple(actual) == expected_tiles and marked == [487] and actual[487] == seed
assert len({(t[2], t[3]) for t in instructions | symbols}) == 484
assert [t for t in actual if t[3] == 'init:R'] == [('sym:0', 'init:R', 'bottom', 'init:R')]
assert [t for t in actual if t[2] == 'wall:start'] == [('wall', 'head:0', 'wall:start', 'sym:0')]
assert [t for t in actual if t[2] == 'wall'] == [('wall', 'sym:0', 'wall', 'sym:0')]
assert all(t[0] != 'bottom' for t in actual)
assert ('sym:0',) * 4 in actual

report = {
    'verdict': 'pass', 'source_hashes': EXPECTED, 'machine_rows': len(machine),
    'abstract_configurations': len(states), 'closure_checked_against_original_table': True,
    'independent_direct_predecessor_proof_data': predecessor_report,
    'omitted_inputs': sorted(impossible), 'tiles': len(actual), 'seed_index': marked[0],
    'instruction_tiles': len(instructions), 'symbol_tiles': len(symbols), 'boundary_tiles': len(boundaries),
    'edge_colors': len({edge for tile in actual for edge in tile}),
    'literal_tile_list_matches_reconstruction': True,
    'southwest_core_determinism_checked': True, 'boundary_forcing_checked': True,
    'whole_plane_periodic_tile_index': actual.index(('sym:0',) * 4),
}
if args.output:
    args.output.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
