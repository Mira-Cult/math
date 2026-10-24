"""Dependency-free compilers for a SEED-CONSTRAINED Wang half-plane.

Tiles are oriented (north, east, south, west); rotations are forbidden.
Every compiler returns a finite tile tuple and the distinguished seed tuple.
None of these sets has unprovable *unrestricted* plane tileability: a blank
background tile alone tiles the plane. See README.md.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from itertools import product
from pathlib import Path

Machine = dict[tuple[int, int], tuple[int, int, str]]
Tile = tuple[str, str, str, str]


def read_machine(path: str | Path) -> Machine:
    machine = {}
    for number, raw in enumerate(Path(path).read_text().splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        q, a, b, direction, target = line.split()
        q, a, b, target = map(int, (q, a, b, target))
        if direction not in ('L', 'R') or a not in (0, 1) or b not in (0, 1):
            raise ValueError(f'Invalid binary transition on line {number}')
        if (q, a) in machine:
            raise ValueError(f'Duplicate state/read pair on line {number}')
        machine[q, a] = target, b, direction
    return machine


def trim_dead_targets(machine: Machine) -> Machine:
    """Omit steps into states with no outgoing steps; preserve infinite runs.

This can advance the first undefined instruction by one TM step. It is not
claimed to preserve the finite halting time or the final written tape.
"""
    live = {q for q, _ in machine}
    return {key: value for key, value in machine.items() if value[0] in live}


def symbol(a: int) -> str:
    return f'sym:{a}'


def head(q: int) -> str:
    return f'head:{q}'


def compile_rows(machine: Machine, *, start=0, share_actions=False, trim=False):
    """The conventional action/merge encoding, optionally sharing payloads."""
    m = trim_dead_targets(machine) if trim else machine

    def marked(q, a):
        if not share_actions:
            return f'head:{q}:{a}'
        if (q, a) not in m:
            return 'dead'
        target, b, direction = m[q, a]
        return f'payload:{target}:{b}:{direction}'

    tiles = {(symbol(a), 'neutral', symbol(a), 'neutral') for a in (0, 1)}
    entered = set()
    for (q, a), (target, b, direction) in m.items():
        transfer = f'transfer:{direction}:{target}'
        if direction == 'R':
            tiles.add((symbol(b), transfer, marked(q, a), 'neutral'))
        else:
            tiles.add((symbol(b), 'neutral', marked(q, a), transfer))
        entered.add((target, direction))
    for target, direction in entered:
        transfer = f'transfer:{direction}:{target}'
        for a in (0, 1):
            if direction == 'R':
                tiles.add((marked(target, a), 'neutral', symbol(a), transfer))
            else:
                tiles.add((marked(target, a), transfer, symbol(a), 'neutral'))
    seed = (marked(start, 0), 'init:R', 'bottom', 'init:L')
    tiles.update((seed, (symbol(0), 'init:L', 'bottom', 'init:L'),
                  (symbol(0), 'init:R', 'bottom', 'init:R')))
    return tuple(sorted(tiles)), seed


def compile_diagonal(machine: Machine, *, start=0, trim=False,
                     allowed_incoming: set[tuple[int, str, int]] | None = None):
    """A north/east head path with tape symbols carried by four wire tiles.

R incoming means the head arrives at a west edge; L means a south edge.
An optional allowed_incoming set MUST be justified by an inductive invariant
for the original blank-tape machine. The CLI obtains it only from a checked
finite-window certificate, never from bounded simulation.
"""
    m = trim_dead_targets(machine) if trim else machine
    entered = {(q, direction) for q, _, direction in m.values()}
    entered.add((start, 'R'))
    tiles = {(symbol(a), symbol(b), symbol(b), symbol(a))
             for a, b in product((0, 1), repeat=2)}
    allowed = None if allowed_incoming is None else set(allowed_incoming)
    if allowed is not None:
        allowed.add((start, 'R', 0))
    for (q, a), (target, b, direction) in m.items():
        north, east = ((symbol(b), head(target)) if direction == 'R'
                       else (head(target), symbol(b)))
        if (q, 'R') in entered and (allowed is None or (q, 'R', a) in allowed):
            tiles.add((north, east, symbol(a), head(q)))
        if (q, 'L') in entered and (allowed is None or (q, 'L', a) in allowed):
            tiles.add((north, east, head(q), symbol(a)))
    # Only the right bottom ray needs initialization. The fixed vertical wall
    # supplies the left blank tape; everything west of it is irrelevant.
    seed = ('wall:start', 'init:R', 'bottom', symbol(0))
    tiles.update((seed,
                  (symbol(0), 'init:R', 'bottom', 'init:R'),
                  ('wall', head(start), 'wall:start', symbol(0)),
                  ('wall', symbol(0), 'wall', symbol(0))))
    return tuple(sorted(tiles)), seed


def write_tiles(path: str | Path, tiles: tuple[Tile, ...], seed: Tile):
    lines = ['index\tseed\tnorth\teast\tsouth\twest']
    for index, tile in enumerate(tiles):
        lines.append('\t'.join((str(index), str(int(tile == seed)), *tile)))
    Path(path).write_text('\n'.join(lines) + '\n')


def read_tiles(path: str | Path):
    tiles, seeds = [], []
    for line in Path(path).read_text().splitlines()[1:]:
        index, marked, *colors = line.split('\t')
        if int(index) != len(tiles) or len(colors) != 4:
            raise ValueError('Malformed tile list')
        tile = tuple(colors)
        tiles.append(tile)
        if marked == '1':
            seeds.append(tile)
    if len(seeds) != 1 or len(set(tiles)) != len(tiles):
        raise ValueError('Expected distinct tiles and exactly one seed')
    return tuple(tiles), seeds[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('machine')
    parser.add_argument('output')
    parser.add_argument('--mode', choices=('baseline', 'payload', 'diagonal'), default='diagonal')
    parser.add_argument('--trim-halt', action='store_true', help='Omit transitions into a dead state')
    parser.add_argument('--prune-radius', type=int, help='Use a checked blank-tape window invariant')
    parser.add_argument('--certificate', help='Where to save the pruning certificate')
    args = parser.parse_args()
    m = read_machine(args.machine)
    allowed = None
    if args.prune_radius is not None:
        if args.mode != 'diagonal' or not args.certificate:
            parser.error('Pruning requires diagonal mode and --certificate')
        from window_invariant import build_certificate, check_certificate, allowed_inputs
        cert = build_certificate(m, args.prune_radius)
        check_certificate(m, cert)
        Path(args.certificate).write_text(json.dumps(cert, indent=2) + '\n')
        allowed = allowed_inputs(cert)
    if args.mode == 'diagonal':
        tiles, seed = compile_diagonal(m, trim=args.trim_halt, allowed_incoming=allowed)
    else:
        tiles, seed = compile_rows(m, share_actions=args.mode == 'payload', trim=args.trim_halt)
    write_tiles(args.output, tiles, seed)
    print(json.dumps({'mode': args.mode, 'tiles': len(tiles), 'seed_index': tiles.index(seed),
                      'source_sha256': hashlib.sha256(Path(args.machine).read_bytes()).hexdigest(),
                      'tiles_sha256': hashlib.sha256(Path(args.output).read_bytes()).hexdigest(),
                      'scope': 'seed-constrained half-plane Z x N'}, indent=2))


if __name__ == '__main__':
    main()
