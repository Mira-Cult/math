"""Thirty source types with half-values and a paid active-parity spine.

ROOT forces the all-zero half-value row with parity1, representing target1 and
active1. Every rooted row is a full infinite bit stream. Recurrent certified
resets force all accepted rows to have finite support; quiet nonstandard runs
are legal and are deliberately not accepted.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json

from arithmetic_v2 import reversed_target_path
from arithmetic_v3 import HalfValueTransducer, pair_prefix


@dataclass(frozen=True)
class WangTile:
    name: str
    north: str
    east: str
    south: str
    west: str

    @property
    def edges(self):
        return self.north, self.east, self.south, self.west


def bits(pair):
    return 'v:bits:' + ''.join(map(str, pair))


def carry(q):
    return f'h:carry:{q}'


def parity(p):
    if p not in (0, 1):
        raise ValueError(p)
    return f'v:parity:{p}'


class SystemV3:
    def __init__(self):
        self.transducer = HalfValueTransducer()
        out = []

        def add(name, n, e, s, w):
            out.append(WangTile(name, n, e, s, w))

        for i, t in enumerate(self.transducer.tiles):
            add(f'digit:{i}', bits(t.north), carry(t.east), bits(t.south), carry(t.west))
        for mode, data in sorted(self.transducer.spine_modes.items()):
            add('spine:' + mode, parity(data['north_parity']), carry(data['start']),
                parity(data['south_parity']), 'h:bg')
        zero = bits((0, 0))
        add('background', zero, 'h:bg', zero, 'h:bg')
        add('ROOT', parity(1), 'h:bg', zero, 'h:bg')
        self.tiles = tuple(out)
        self.by_name = {t.name: t for t in self.tiles}
        self.by_edges = {t.edges: t for t in self.tiles}
        assert len(self.by_edges) == len(self.tiles)
        self.root_index = next(i for i, t in enumerate(self.tiles) if t.name == 'ROOT')
        self.event_index = next(i for i, t in enumerate(self.tiles) if t.name == 'spine:RESET')
        self.event_color = carry(self.transducer.event_start)
        assert [t.name for t in self.tiles if t.name.startswith('spine:')
                and t.east == self.event_color] == ['spine:RESET']

    def manifest(self):
        return {
            'model': 'completed unseeded source; grounded recurrence is separate',
            'arithmetic': 'inverse Collatz half-values and parity spine',
            'row_model': 'infinite LSB-first bit streams; accepted rows have finite support',
            'encoding': {'target': 'n=2*k+1', 'active': 'v=2*a+p'},
            'initial_stream': '(k,a)=(0,0) at every digit, spine parity p=1',
            'tile_count': len(self.tiles),
            'horizontal_colors': len({c for t in self.tiles for c in (t.east, t.west)}),
            'vertical_colors': len({c for t in self.tiles for c in (t.north, t.south)}),
            'tiles': [{'name': t.name, 'edges': t.edges} for t in self.tiles],
            'root_index': self.root_index, 'event_spine_index': self.event_index,
            'root_context': {'north': parity(1), 'east': 'h:bg'},
            'event_column_offset': 0, 'event_east_color': self.event_color,
            'event_scope': 'RESET spine in this intrinsic ROOT column; not arbitrary carry recurrence',
            'transducer_manifest_sha256': self.transducer.digest(),
            'nonaccepting_exception': 'rooted nonstandard active streams cannot precede a later reset',
        }

    def digest(self):
        return hashlib.sha256((json.dumps(self.manifest(), sort_keys=True,
                                        separators=(',', ':'))+'\n').encode()).hexdigest()

    def frame_checks(self):
        digits = {t.name for t in self.tiles if t.name.startswith('digit:')}
        spines = {'spine:' + m for m in self.transducer.spine_modes}
        data = {bits(p) for p in ((0, 0), (0, 1), (1, 0), (1, 1))}
        ps = {parity(0), parity(1)}
        assert {t.name for t in self.tiles if t.west.startswith('h:carry:')} == digits
        assert {t.name for t in self.tiles if t.west == 'h:bg'} == {'ROOT', 'background', *spines}
        assert all(t.east.startswith('h:carry:') for t in self.tiles if t.name in digits)
        assert {t.name for t in self.tiles if t.south in ps} == spines
        assert {t.name for t in self.tiles if t.north in ps} == {'ROOT', *spines}
        assert {t.name for t in self.tiles if t.west == 'h:bg' and t.north in data} == {'background'}
        assert {t.name for t in self.tiles if t.east == 'h:bg' and t.north == parity(1)} == {'ROOT'}
        assert self.by_name['ROOT'].edges == (parity(1), 'h:bg', bits((0, 0)), 'h:bg')
        assert self.by_name['background'].edges == (bits((0, 0)), 'h:bg', bits((0, 0)), 'h:bg')
        return True

    def zero_tail_tile(self, final):
        z = bits((0, 0))
        return self.by_edges[(z, carry(final), z, carry(final))]


def accepted_rows(system):
    """Conditional witness policy, with no time, value or starting-target cutoff."""
    target = 1
    time = 0
    while True:
        path = reversed_target_path(target)
        for old, new in zip(path, path[1:]):
            branch = 'double' if new == 2*old else 'preimage'
            row = system.transducer.certificate(target, old, time+2, branch=branch)
            row.update(time=time, width=time+2)
            yield row
            time += 1
        row = system.transducer.certificate(target, target, time+2, branch='reset')
        row.update(time=time, width=time+2)
        yield row
        target += 2
        time += 1


def quiet_rows(system):
    active = 1
    time = 0
    while True:
        row = system.transducer.certificate(1, active, time+2, branch='double')
        row.update(time=time, width=time+2)
        yield row
        active *= 2
        time += 1


class WitnessTiling:
    """Whole-plane constructor: quiet is total, accepted is total under Collatz."""
    def __init__(self, system=None, *, policy='quiet'):
        self.system = system or SystemV3()
        if policy not in ('quiet', 'accepted'):
            raise ValueError(policy)
        self.policy = policy
        self.rows = []
        self.generator = (quiet_rows if policy == 'quiet' else accepted_rows)(self.system)

    def row(self, y):
        if y < 1:
            raise ValueError('arithmetic row indices are positive relative to an actual ROOT')
        while len(self.rows) < y:
            r = next(self.generator)
            assert len(r['input']) == len(r['output']) == len(self.rows)+2
            assert r['input'][-1] == [0, 0]
            if self.rows:
                assert r['input'] == self.rows[-1]['output'] + [[0, 0]]
                assert r['south_parity'] == self.rows[-1]['north_parity']
            else:
                assert r['south_parity'] == 1
                assert r['input'] == [[0, 0], [0, 0]]
            self.system.zero_tail_tile(r['states'][-1])
            self.rows.append(r)
        return self.rows[y-1]

    def tile_at(self, x, y):
        s = self.system
        if x < 0 or y < 0:
            return s.by_name['background']
        if y == 0:
            return s.by_name['ROOT'] if x == 0 else s.by_name['background']
        r = self.row(y)
        if x == 0:
            return s.by_name['spine:' + r['mode']]
        if x > len(r['input']):
            return s.zero_tail_tile(r['states'][-1])
        i = x-1
        return s.by_edges[(bits(r['output'][i]), carry(r['states'][i+1]),
                           bits(r['input'][i]), carry(r['states'][i]))]

    def check_window(self, x0, x1, y0, y1):
        checked = 0
        for y in range(y0, y1+1):
            for x in range(x0, x1+1):
                tile = self.tile_at(x, y)
                assert tile.east == self.tile_at(x+1, y).west, (x, y, 'east')
                assert tile.north == self.tile_at(x, y+1).south, (x, y, 'north')
                checked += 2
        return checked


class NonstandardWitnessTiling(WitnessTiling):
    """Completed silent example: full active values1,2,1/3,2/3,4/3,... ."""
    def __init__(self, system=None):
        self.system = system or SystemV3()
        self.policy = 'nonstandard-silent'

    @staticmethod
    def specification(y):
        if y == 1:
            old, new, mode = Fraction(1), Fraction(2), 'DOUBLE1'
        elif y == 2:
            old, new, mode = Fraction(2), Fraction(1, 3), 'PREIMAGE'
        elif y >= 3:
            old, new = Fraction(1 << (y-3), 3), Fraction(1 << (y-2), 3)
            mode = 'DOUBLE' + str(old.numerator % 2)
        else:
            raise ValueError(y)
        p, pp = old.numerator % 2, new.numerator % 2
        return (old-p)/2, (new-pp)/2, p, pp, mode

    def tile_at(self, x, y):
        s = self.system
        if x < 0 or y < 0:
            return s.by_name['background']
        if y == 0:
            return s.by_name['ROOT'] if x == 0 else s.by_name['background']
        old, new, p, pp, mode = self.specification(y)
        if x == 0:
            tile = s.by_name['spine:' + mode]
            assert (tile.south, tile.north) == (parity(p), parity(pp))
            return tile
        low = pair_prefix(0, old, x)
        row = s.transducer.prefix(mode, low)
        assert row is not None
        assert row['output'] == pair_prefix(0, new, x)
        i = x-1
        return s.by_edges[(bits(row['output'][i]), carry(row['states'][i+1]),
                           bits(row['input'][i]), carry(row['states'][i]))]


if __name__ == '__main__':
    s = SystemV3()
    s.frame_checks()
    out = s.manifest()
    out['source_sha256'] = s.digest()
    print(json.dumps(out, sort_keys=True, indent=2))
