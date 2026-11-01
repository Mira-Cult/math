"""Thirty-one source types with intrinsic initialization and infinite zero tails.

This is a separate source from the reviewed finite-width v2 frame. Every rooted
row is an infinite bit stream. Infinitely recurring certified resets force every
accepted row to represent standard positive integers; legal silent rows may be
nonstandard. The observer still recognizes only fixed geometric contacts.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json

from arithmetic_v2 import ReverseTransducer, accepted_reverse_rows, quiet_reverse_rows


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


class SystemV3:
    def __init__(self):
        self.transducer = ReverseTransducer()
        out = []

        def add(name, n, e, s, w):
            out.append(WangTile(name, n, e, s, w))

        for i, t in enumerate(self.transducer.tiles):
            add(f'digit:{i}', bits(t.north), carry(t.east), bits(t.south), carry(t.west))
        for mode, q in sorted(self.transducer.starts.items()):
            add('spine:' + mode, 'v:spine', carry(q), 'v:spine', 'h:bg')
        zero = bits((0, 0))
        add('background', zero, 'h:bg', zero, 'h:bg')
        add('ROOT', 'v:spine', 'h:initial', zero, 'h:bg')
        add('initial:one', bits((1, 1)), 'h:bg', zero, 'h:initial')
        self.tiles = tuple(out)
        self.by_name = {t.name: t for t in self.tiles}
        self.by_edges = {t.edges: t for t in self.tiles}
        assert len(self.by_edges) == len(self.tiles)
        event_first = self.transducer.event_first_tiles
        colors = {self.transducer.tiles[i].east for i in event_first}
        assert len(colors) == 1
        self.event_carry = next(iter(colors))
        self.event_color = carry(self.event_carry)
        starts = set(self.transducer.starts.values())
        detected = {i for i, t in enumerate(self.transducer.tiles)
                    if t.west in starts and t.east == self.event_carry}
        assert detected == set(event_first)
        self.event_first_indices = tuple(sorted(detected))

    def manifest(self):
        return {
            'model': 'completed unseeded source; grounded recurrence is separate',
            'arithmetic': 'inverse Collatz with equality-certified reset',
            'row_model': 'infinite LSB-first bit streams; accepted rows have finite support',
            'initial_stream': '(1,1),(0,0),(0,0),...',
            'tile_count': len(self.tiles),
            'horizontal_colors': len({c for t in self.tiles for c in (t.east, t.west)}),
            'vertical_colors': len({c for t in self.tiles for c in (t.north, t.south)}),
            'tiles': [{'name': t.name, 'edges': t.edges} for t in self.tiles],
            'root': 'ROOT', 'event_column_offset': 1,
            'event_east_color': self.event_color,
            'event_first_digit_indices': self.event_first_indices,
            'event_scope': 'first digit above this intrinsic ROOT; later-column copies do not count',
            'transducer_manifest_sha256': self.transducer.digest(),
            'nonaccepting_exception': 'rooted nonstandard active streams cannot precede a later reset',
        }

    def digest(self):
        return hashlib.sha256((json.dumps(self.manifest(), sort_keys=True,
                                        separators=(',', ':'))+'\n').encode()).hexdigest()

    def frame_checks(self):
        digits = {t.name for t in self.tiles if t.name.startswith('digit:')}
        spines = {'spine:' + m for m in self.transducer.starts}
        assert {t.name for t in self.tiles if t.west.startswith('h:carry:')} == digits
        assert {t.name for t in self.tiles if t.west == 'h:bg'} == {
            'background', 'ROOT', *spines}
        assert {t.name for t in self.tiles if t.west == 'h:initial'} == {'initial:one'}
        assert {t.name for t in self.tiles if t.east == 'h:initial'} == {'ROOT'}
        assert {t.name for t in self.tiles if t.south == 'v:spine'} == spines
        assert {t.name for t in self.tiles if t.north == 'v:spine'} == {'ROOT', *spines}
        assert all(t.east.startswith('h:carry:') for t in self.tiles if t.name in digits)
        data = {bits(p) for p in ((0, 0), (0, 1), (1, 0), (1, 1))}
        assert {t.name for t in self.tiles if t.west == 'h:bg' and t.north in data} == {'background'}
        assert self.by_name['initial:one'].east == 'h:bg'
        assert self.by_name['initial:one'].north == bits((1, 1))
        assert self.by_name['background'].north == bits((0, 0))
        # These tests deliberately do not assert that only BG has north 00.
        assert any(t.name in digits and t.north == bits((0, 0)) for t in self.tiles)
        return True

    def closed_pair_families(self):
        """Literal mutually exclusive forced pairs, valid even in rootless arrays.

        A later polygon fusion may replace these disjoint pairs by their unions.
        No statement about side counts is made by this source-only method.
        """
        families = []
        for label, edge in [('root', 'h:initial'), ('choice', carry(self.transducer.starts['CHOICE']))]:
            left = [i for i, t in enumerate(self.tiles) if t.east == edge]
            right = [i for i, t in enumerate(self.tiles) if t.west == edge]
            assert len(left) == 1 and right
            families.append({'name': label, 'left': left[0], 'rights': right,
                             'interface': edge})
        participants = [f['left'] for f in families] + [i for f in families for i in f['rights']]
        assert len(set(participants)) == len(participants)
        return families

    def zero_tail_tile(self, final):
        z = bits((0, 0))
        return self.by_edges[(z, carry(final), z, carry(final))]


class WitnessTiling:
    """Completed standard-stream witness; accepted policy is conditionally total.

    The finite row certificates are extended by their exact zero self-loop, so
    tile_at is defined at every integer site once the requested row is available.
    Quiet policy is unconditional. Accepted policy may be partial if Collatz fails.
    """
    def __init__(self, system=None, *, policy='quiet'):
        self.system = system or SystemV3()
        if policy not in ('quiet', 'accepted'):
            raise ValueError(policy)
        self.policy = policy
        self.rows = []
        maker = quiet_reverse_rows if policy == 'quiet' else accepted_reverse_rows
        self.generator = maker()

    def row(self, y):
        if y < 1:
            raise ValueError('logical arithmetic rows have positive root-relative height')
        while len(self.rows) < y:
            r = next(self.generator)
            assert len(r['input']) == len(r['output']) == len(self.rows)+2
            assert r['input'][-1] == [0, 0]
            if self.rows:
                assert r['input'] == self.rows[-1]['output'] + [[0, 0]]
            assert r['states'][-1] in self.system.transducer.finals
            self.system.zero_tail_tile(r['states'][-1])
            self.rows.append(r)
        return self.rows[y-1]

    def tile_at(self, x, y):
        s = self.system
        if x < 0 or y < 0:
            return s.by_name['background']
        if y == 0:
            return s.by_name['ROOT'] if x == 0 else s.by_name['initial:one'] if x == 1 else s.by_name['background']
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
                t = self.tile_at(x, y)
                assert t.east == self.tile_at(x+1, y).west, (x, y, 'east')
                assert t.north == self.tile_at(x, y+1).south, (x, y, 'north')
                checked += 2
        return checked


def residue_bits(value, width):
    """Exact finite prefixes of a rational 2-adic stream with odd denominator."""
    value = Fraction(value)
    if width < 0 or value.denominator % 2 == 0:
        raise ValueError('nonnegative width and odd denominator required')
    modulus = 1 << width
    residue = value.numerator * pow(value.denominator, -1, modulus) % modulus
    return tuple((residue >> i) & 1 for i in range(width))


class NonstandardWitnessTiling(WitnessTiling):
    """Actual completed silent exception: target1, active1,2,1/3,2/3,4/3,... .

    Fractions are used only to emit the exact residue-stream counterexample.
    This constructor is not an observer, accepted witness or finite integer run.
    """
    def __init__(self, system=None):
        self.system = system or SystemV3()
        self.policy = 'nonstandard-silent'

    @staticmethod
    def specification(y):
        if y == 1:
            return Fraction(1), Fraction(2), 'DOUBLE'
        if y == 2:
            return Fraction(2), Fraction(1, 3), 'CHOICE'
        if y >= 3:
            return Fraction(1 << (y-3), 3), Fraction(1 << (y-2), 3), 'DOUBLE'
        raise ValueError(y)

    def tile_at(self, x, y):
        s = self.system
        if x < 0 or y < 0:
            return s.by_name['background']
        if y == 0:
            return s.by_name['ROOT'] if x == 0 else s.by_name['initial:one'] if x == 1 else s.by_name['background']
        old, new, mode = self.specification(y)
        if x == 0:
            return s.by_name['spine:' + mode]
        low, high = residue_bits(old, x), residue_bits(new, x)
        q = s.transducer.starts[mode]
        for i in range(x):
            saved = int(i == 0)
            letter = saved, low[i], saved, high[i]
            q_next = s.transducer.edges[q, letter]
            tile = s.by_edges[(bits((saved, high[i])), carry(q_next),
                               bits((saved, low[i])), carry(q))]
            q = q_next
        return tile


if __name__ == '__main__':
    s = SystemV3()
    s.frame_checks()
    out = s.manifest()
    out['source_sha256'] = s.digest()
    out['closed_pair_families'] = s.closed_pair_families()
    print(json.dumps(out, indent=2, sort_keys=True))
