"""Third-pass carry relations and exact infinite-stream prefix utilities.

The reviewed v2 source is preserved. StreamReverseTransducer exposes exactly
its same 26 digit types without requiring a final carry at a finite cutoff.
HalfValueTransducer is a separate 24-type relation: target n=2*k+1, active
v=2*a+p, with active parity p supplied by the source spine. Its four parity
interfaces are charged separately; this module claims no polygon upper bound.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import itertools
import json

from arithmetic_v2 import ReverseTransducer, Tile, decode, reverse_step


def rational_bits(numerator, denominator=1):
    """Exact binary stream for a rational with odd positive denominator.

    Integer orthogonal tiling geometry does not execute this helper. It is a
    reproducible source of witness prefixes, including nonstandard examples.
    """
    value = Fraction(numerator, denominator)
    numerator, denominator = value.numerator, value.denominator
    if denominator % 2 == 0:
        raise ValueError('an odd denominator is required for an integral binary stream')
    while True:
        bit = numerator % 2
        yield bit
        numerator = (numerator-denominator*bit)//2


def pair_prefix(saved, active, length):
    """Finite prefix of two compatible binary residue streams."""
    if length < 1:
        raise ValueError('positive prefix length required')
    saved, active = Fraction(saved), Fraction(active)
    return tuple(itertools.islice(zip(rational_bits(saved), rational_bits(active)), length))


def prefix_path(transducer, mode, bottom):
    """Read an exact finite prefix without a final-carry condition.

    None means a local transition is absent. The output for a fixed mode and
    input prefix is unique. This function never decides infinite extension or R.
    """
    if mode not in transducer.starts or not bottom:
        return None
    state = transducer.starts[mode]
    states, output = [state], []
    for pair in bottom:
        choices = [t for t in transducer.tiles if t.west == state and t.south == tuple(pair)]
        if not choices:
            return None
        if len(choices) != 1:
            raise AssertionError('input prefix does not determine a unique next tile')
        tile = choices[0]
        output.append(tile.north)
        state = tile.east
        states.append(state)
    return {'mode': mode, 'input': tuple(map(tuple, bottom)),
            'output': tuple(output), 'states': tuple(states)}


class StreamReverseTransducer(ReverseTransducer):
    """The unchanged 26-type reverse relation read on right-infinite rows."""

    def __init__(self):
        super().__init__(odd_inputs=True, merge_odd_reset=True)
        assert len(self.tiles) == 26 and len(self.state_members) == 8
        assert all(len(raw) == 1 for raw in self.state_members.values())

    def prefix(self, mode, bottom):
        row = prefix_path(self, mode, bottom)
        if row is not None:
            row['event'] = (row['states'][0] == self.starts['CHOICE']
                            and row['states'][1] in self.reset_carry_states)
        return row


def encode_halves(target_half, active_half, width):
    if min(target_half, active_half) < 0 or width < 1:
        raise ValueError('nonnegative half-values and positive width required')
    if max(target_half, active_half).bit_length() > width:
        raise ValueError('half-values do not fit the finite width')
    return tuple(((target_half >> i) & 1, (active_half >> i) & 1) for i in range(width))


class HalfValueTransducer:
    """Literal 24-type carry alphabet with four paid parity interfaces."""

    def __init__(self):
        raw = (('D', 0), ('D', 1), ('M', 0), ('M', 1), ('M', 2), ('R', 0), ('R', 1))
        ids = {q: i for i, q in enumerate(raw)}
        self.state_members = {ids[q]: (q,) for q in raw}
        self.spine_modes = {
            'DOUBLE0': {'south_parity': 0, 'north_parity': 0, 'start': ids['D', 0]},
            'DOUBLE1': {'south_parity': 1, 'north_parity': 0, 'start': ids['D', 1]},
            'PREIMAGE': {'south_parity': 0, 'north_parity': 1, 'start': ids['M', 2]},
            'RESET': {'south_parity': 1, 'north_parity': 1, 'start': ids['R', 1]},
        }
        self.starts = {m: data['start'] for m, data in self.spine_modes.items()}
        self.finals = frozenset(ids[q] for q in (('D', 0), ('M', 0), ('R', 0)))
        out = set()
        for kind, carry in raw:
            for k, a, kp, ap in itertools.product((0, 1), repeat=4):
                after = None
                if kind == 'D' and kp == k and ap == carry:
                    after = a
                elif kind == 'M' and kp == k:
                    num = 3*ap+carry-a
                    if num % 2 == 0 and num//2 in (0, 1, 2):
                        after = num//2
                elif kind == 'R' and a == k and ap == 0 and kp == (k+carry) % 2:
                    after = (k+carry)//2
                if after is not None:
                    out.add(Tile((kp, ap), ids[kind, after], (k, a), ids[kind, carry]))
        self.tiles = tuple(sorted(out))
        assert len(self.tiles) == 24
        self.mode_counts = {kind: sum(raw[t.west][0] == kind for t in self.tiles)
                            for kind in ('D', 'M', 'R')}
        assert self.mode_counts == {'D': 8, 'M': 12, 'R': 4}
        self.reset_carry_states = frozenset((ids['R', 0], ids['R', 1]))
        self.event_start = ids['R', 1]

    def prefix(self, mode, bottom):
        row = prefix_path(self, mode, bottom)
        if row is not None:
            row.update(event=mode == 'RESET', **self.spine_modes[mode])
        return row

    def path(self, mode, bottom, top):
        if not bottom or len(bottom) != len(top):
            return None
        row = self.prefix(mode, bottom)
        if row is None or row['output'] != tuple(map(tuple, top)):
            return None
        return row['states'] if row['states'][-1] in self.finals else None

    def certificate(self, target, active, width, *, branch):
        after_target, after_active, event = reverse_step(target, active, branch)
        mode = ('DOUBLE'+str(active % 2)) if branch == 'double' else branch.upper()
        bottom = encode_halves((target-1)//2, active//2, width)
        top = encode_halves((after_target-1)//2, after_active//2, width)
        path = self.path(mode, bottom, top)
        if path is None:
            raise AssertionError('finite half-value operation has no carry path')
        data = self.spine_modes[mode]
        assert (data['south_parity'], data['north_parity']) == (active % 2, after_active % 2)
        return {'mode': mode, 'branch': branch, 'event': event,
                'south_parity': data['south_parity'], 'north_parity': data['north_parity'],
                'input': [list(p) for p in bottom], 'output': [list(p) for p in top],
                'states': list(path)}

    def manifest(self):
        return {
            'variant': 'inverse Collatz half-values with a paid parity spine',
            'target_encoding': 'n=2*k+1', 'active_encoding': 'v=2*a+p',
            'root_values': {'k': 0, 'a': 0, 'p': 1},
            'spine_modes': self.spine_modes, 'starts': self.starts,
            'finals': sorted(self.finals), 'event_start': self.event_start,
            'states': {str(i): [list(q) for q in qs] for i, qs in self.state_members.items()},
            'tiles': [t.as_dict() for t in self.tiles],
            'digit_tile_count': len(self.tiles), 'mode_counts': self.mode_counts,
            'horizontal_carry_colors': 7, 'vertical_bitpair_colors': 4,
            'additional_parity_colors': 2, 'required_spine_types': 4,
            'growth_columns': 1,
            'scope': 'finite-word and infinite-stream arithmetic only; frame and geometry charged separately',
        }

    def digest(self):
        data = (json.dumps(self.manifest(), sort_keys=True, separators=(',', ':'))+'\n').encode()
        return hashlib.sha256(data).hexdigest()


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', action='store_true')
    args = parser.parse_args()
    t = HalfValueTransducer()
    if args.manifest:
        print(json.dumps(t.manifest(), sort_keys=True, indent=2))
    else:
        print(json.dumps({'digit_types': len(t.tiles), 'mode_counts': t.mode_counts,
                          'carry_colors': len(t.state_members), 'spine_modes': t.spine_modes,
                          'finals': sorted(t.finals), 'manifest_sha256': t.digest()}, sort_keys=True))


if __name__ == '__main__':
    main()
