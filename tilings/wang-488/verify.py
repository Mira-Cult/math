"""Independent literal Wang constraints versus ordinary TM simulation.

Finite checks supplement README.md; they do not prove nonhalting.
The Wang solver sees tile tuples, not a TM table. No dependencies required.
"""
import argparse
import hashlib
import json
from itertools import product
from pathlib import Path
from random import Random

from tm_to_wang import (compile_diagonal, compile_rows, read_machine, read_tiles,
                        trim_dead_targets, write_tiles)
from window_invariant import allowed_inputs, build_certificate, check_certificate


def ordinary_history(machine, steps, tape=None):
    tape, q, position, result = dict(tape or {}), 0, 0, []
    for t in range(steps):
        read = tape.get(position, 0)
        instruction = machine.get((q, read))
        result.append((t, position, q, read, instruction))
        if instruction is None:
            break
        target, written, direction = instruction
        tape[position] = written
        position += 1 if direction == 'R' else -1
        q = target
    return result


def literal_history(tiles, steps, tape=None):
    """Solve antidiagonals from tile edges, retaining O(steps) memory.

    Nonblank axis inputs exercise the core separately from the blank wrapper.
    """
    tape = dict(tape or {})
    by_inputs = {}
    for tile in tiles:
        if all(edge.startswith(('sym:', 'head:')) for edge in tile):
            key = tile[2], tile[3]
            assert key not in by_inputs, 'Nondeterministic southwest input'
            by_inputs[key] = tile
    previous_north, previous_east, result = {}, {}, []
    for diagonal in range(2, steps + 2):
        next_north, next_east, heads = {}, {}, []
        for x in range(1, diagonal):
            y = diagonal - x
            south = f'sym:{tape.get(x - 1, 0)}' if y == 1 else previous_north[x]
            west = (('head:0' if y == 1 else f'sym:{tape.get(1 - y, 0)}')
                    if x == 1 else previous_east[x - 1])
            entering = [edge for edge in (south, west) if edge.startswith('head:')]
            assert len(entering) <= 1, 'Two incoming heads'
            tile = by_inputs.get((south, west))
            if entering:
                q = int(entering[0].split(':')[1])
                read_edge = west if south.startswith('head:') else south
                read = int(read_edge.split(':')[1])
                if tile is None:
                    instruction = None
                elif tile[1].startswith('head:'):
                    instruction = int(tile[1].split(':')[1]), int(tile[0].split(':')[1]), 'R'
                else:
                    instruction = int(tile[0].split(':')[1]), int(tile[1].split(':')[1]), 'L'
                heads.append((diagonal - 2, x - y, q, read, instruction))
            if tile is None:
                assert entering, 'Missing background tile'
                return result + heads
            next_north[x], next_east[x] = tile[0], tile[1]
        assert len(heads) == 1, f'Expected one head, found {len(heads)}'
        result.extend(heads)
        previous_north, previous_east = next_north, next_east
    return result


def check_wrapper(tiles, seed):
    """Check local forcing premises on the actual supplied tile tuples."""
    assert seed == ('wall:start', 'init:R', 'bottom', 'sym:0')
    assert [t for t in tiles if t[3] == 'init:R'] == [
        ('sym:0', 'init:R', 'bottom', 'init:R')]
    assert [t for t in tiles if t[2] == 'wall:start'] == [
        ('wall', 'head:0', 'wall:start', 'sym:0')]
    assert [t for t in tiles if t[2] == 'wall'] == [
        ('wall', 'sym:0', 'wall', 'sym:0')]
    assert all(t[0] != 'bottom' for t in tiles)
    assert ('sym:0',) * 4 in tiles


def run_generic_checks():
    options = [None] + list(product(range(2), (0, 1), ('L', 'R')))
    keys = list(product(range(2), (0, 1)))
    count = 0
    for values in product(options, repeat=4):
        machine = {k: v for k, v in zip(keys, values) if v is not None}
        tiles, seed = compile_diagonal(machine)
        check_wrapper(tiles, seed)
        assert literal_history(tiles, 12) == ordinary_history(machine, 12)
        cert = build_certificate(machine, 1)
        check_certificate(machine, cert)
        reduced, _ = compile_diagonal(machine, trim=True, allowed_incoming=allowed_inputs(cert))
        assert literal_history(reduced, 12) == ordinary_history(trim_dead_targets(machine), 12)
        count += 1
    rng = Random(20261024)
    for trial in range(2000):
        states = rng.randrange(1, 8)
        machine = {(q, a): (rng.randrange(states), rng.randrange(2), rng.choice(('L', 'R')))
                   for q in range(states) for a in (0, 1) if rng.randrange(10)}
        tape = {position: rng.randrange(2) for position in range(-12, 13)}
        tiles, _ = compile_diagonal(machine)
        assert literal_history(tiles, 40, tape) == ordinary_history(machine, 40, tape)
    cert = build_certificate({(0, 0): (0, 0, 'R')}, start=1)
    try:
        check_certificate({(0, 0): (0, 0, 'R')}, cert)
    except ValueError:
        pass
    else:
        raise AssertionError('Accepted the wrong initial state')
    cert = build_certificate({(0, 0): (0, 0, 'R')})
    cert['states'] = [s for s in cert['states'] if s != [0, 0, 'R']]
    try:
        check_certificate({(0, 0): (0, 0, 'R')}, cert)
    except ValueError:
        pass
    else:
        raise AssertionError('Accepted an unclosed invariant')
    return {'all_partial_two_state_machines': count, 'steps_each': 12,
            'both_original_and_pruned_compilers': True,
            'random_nonblank_machines': 2000, 'random_steps_each': 40,
            'random_seed': 20261024, 'certificate_negative_controls': 2,
            'mismatches': 0}


def audit_source(path, output_dir):
    path, output_dir = Path(path), Path(output_dir)
    name, machine = path.stem, read_machine(path)
    cert = build_certificate(machine, 1)
    check_certificate(machine, cert)
    allowed = allowed_inputs(cert)
    variants = {
        'baseline': compile_rows(machine),
        'payload': compile_rows(machine, share_actions=True),
        'payload_trimmed': compile_rows(machine, share_actions=True, trim=True),
        'diagonal': compile_diagonal(machine),
        'diagonal_trimmed': compile_diagonal(machine, trim=True),
        'diagonal_pruned': compile_diagonal(machine, trim=True, allowed_incoming=allowed),
    }
    full, _ = variants['diagonal_trimmed']
    reduced, seed = variants['diagonal_pruned']
    check_wrapper(reduced, seed)
    assert set(reduced) <= set(full)
    assert literal_history(variants['diagonal'][0], 1000) == ordinary_history(machine, 1000)
    assert literal_history(reduced, 1000) == ordinary_history(trim_dead_targets(machine), 1000)
    file_records = {}
    for label in ('diagonal_trimmed', 'diagonal_pruned'):
        tiles, marked = variants[label]
        output = output_dir / f'{name}_diagonal_{len(tiles)}.tsv'
        write_tiles(output, tiles, marked)
        loaded, loaded_seed = read_tiles(output)
        assert (loaded, loaded_seed) == (tiles, marked)
        file_records[output.name] = hashlib.sha256(output.read_bytes()).hexdigest()
    cert_file = output_dir / f'{name}_window_certificate.json'
    cert_file.write_text(json.dumps(cert, indent=2) + '\n')
    blocked = []
    for tile in set(full) - set(reduced):
        if tile[3].startswith('head:'):
            blocked.append([int(tile[3].split(':')[1]), 'R', int(tile[2].split(':')[1])])
        else:
            blocked.append([int(tile[2].split(':')[1]), 'L', int(tile[3].split(':')[1])])
    return {'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'working_states': len({q for q, a in machine}), 'transition_rows': len(machine),
            'counts': {k: len(v[0]) for k, v in variants.items()},
            'abstract_states': len(cert['states']), 'blocked_incoming': sorted(blocked),
            'literal_tile_steps_checked': 1000, 'tile_files': file_records,
            'certificate_sha256': hashlib.sha256(cert_file.read_bytes()).hexdigest(),
            'unrestricted_plane_periodic_witness': ['sym:0'] * 4}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--k215')
    parser.add_argument('--k230')
    parser.add_argument('--output', default='results.json')
    args = parser.parse_args()
    result = {'scope': 'seed-constrained half-plane', 'generic_checks': run_generic_checks()}
    for name in ('k215', 'k230'):
        path = getattr(args, name)
        if path:
            result[name] = audit_source(path, Path(args.output).resolve().parent)
    Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
