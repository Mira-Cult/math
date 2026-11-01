"""Finite-word, stream-prefix and mutation checks for third-pass arithmetic."""
from fractions import Fraction
from itertools import product
import random
import unittest

from arithmetic_v2 import ReverseTransducer, accepted_reverse_rows, decode, reverse_step
from arithmetic_v3 import (HalfValueTransducer, StreamReverseTransducer,
                           encode_halves, pair_prefix)


class ArithmeticV3Tests(unittest.TestCase):
    def test_literal_alphabets_and_paid_interfaces(self):
        stream, old = StreamReverseTransducer(), ReverseTransducer()
        self.assertEqual((stream.tiles, stream.starts, stream.finals),
                         (old.tiles, old.starts, old.finals))
        self.assertTrue(all(len(qs) == 1 for qs in stream.state_members.values()))
        h = HalfValueTransducer()
        self.assertEqual((len(h.tiles), len(h.state_members)), (24, 7))
        self.assertEqual(h.mode_counts, {'D': 8, 'M': 12, 'R': 4})
        self.assertEqual(h.starts, {'DOUBLE0': 0, 'DOUBLE1': 1, 'PREIMAGE': 4, 'RESET': 6})
        self.assertEqual(h.finals, {0, 2, 5})
        self.assertEqual(h.digest(), 'c5c561c6d3c07ec9684e59736f3b04050408b3160c59750be3be233a66788ce9')
        self.assertEqual(len(h.spine_modes), 4)
        for q in h.finals:
            self.assertEqual(sum(t.west == t.east == q and t.north == t.south == (0, 0)
                                 for t in h.tiles), 1)

    def test_complete_finite_word_relation(self):
        t = HalfValueTransducer()
        cases = 0
        for width in range(1, 5):
            limit = 1 << width
            words = {(h, a): encode_halves(h, a, width)
                     for h, a in product(range(limit), repeat=2)}
            for (h, a), bottom in words.items():
                for mode in t.starts:
                    if mode.startswith('DOUBLE'):
                        expected = h, 2*a+int(mode[-1])
                    elif mode == 'PREIMAGE':
                        expected = (h, (a-2)//3) if a >= 2 and (a-2) % 3 == 0 else None
                    else:
                        expected = (h+1, 0) if a == h else None
                    if expected is not None and max(expected) >= limit:
                        expected = None
                    for pair, top in words.items():
                        self.assertEqual(t.path(mode, bottom, top) is not None, pair == expected,
                                         (width, h, a, mode, pair, expected))
                        cases += 1
        self.assertEqual(cases, 279616)

    def test_standard_certificates_and_parity(self):
        t = HalfValueTransducer()
        for n in range(1, 32, 2):
            for v in range(1, 96):
                branches = ['double']
                if v >= 4 and v % 6 == 4:
                    branches.append('preimage')
                if v == n:
                    branches.append('reset')
                for branch in branches:
                    width = max(n, v).bit_length()+1
                    row = t.certificate(n, v, width, branch=branch)
                    h, a = decode(row['input']); hp, ap = decode(row['output'])
                    self.assertEqual((2*h+1, 2*a+row['south_parity']), (n, v))
                    expected = reverse_step(n, v, branch)
                    self.assertEqual((2*hp+1, 2*ap+row['north_parity'], row['event']), expected)
        for n, v, branch in ((2, 2, 'double'), (1, 0, 'double'), (1, 1, 'preimage'),
                             (1, 2, 'preimage'), (1, 7, 'preimage'), (7, 5, 'reset')):
            with self.assertRaises(ValueError):
                t.certificate(n, v, 8, branch=branch)

    def test_unchanged_stream_relation_on_rational_prefixes(self):
        t = StreamReverseTransducer()
        for n in range(1, 16, 2):
            for v in range(1, 32):
                for length in (1, 2, 7, 31):
                    bottom = pair_prefix(n, v, length)
                    double = t.prefix('DOUBLE', bottom)
                    self.assertEqual(double['output'], pair_prefix(n, 2*v, length))
                    self.assertFalse(double['event'])
                    if v % 2 == 0:
                        pre = t.prefix('CHOICE', bottom)
                        self.assertEqual(pre['output'], pair_prefix(n, Fraction(v-1, 3), length))
                        self.assertFalse(pre['event'])
            reset = t.prefix('CHOICE', pair_prefix(n, n, 64))
            self.assertEqual(reset['output'], pair_prefix(n+2, 1, 64))
            self.assertTrue(reset['event'])
        self.assertTrue(t.prefix('CHOICE', pair_prefix(1, 5, 2))['event'])
        self.assertIsNone(t.prefix('CHOICE', pair_prefix(1, 5, 3)))

    def test_half_stream_equations_and_spine_parities(self):
        t = HalfValueTransducer()
        values = [Fraction(v) for v in (1, 2, 4, 7, 16)]
        values += [Fraction(1, 3), Fraction(2, 3), Fraction(-1, 9), Fraction(-2, 9)]
        for n, v in product((1, 3, 17), values):
            parity = v.numerator % 2
            half = (v-parity)/2
            choices = [('DOUBLE'+str(parity), n, 2*v, 0)]
            if parity == 0:
                choices.append(('PREIMAGE', n, (v-1)/3, 1))
            if v == n:
                choices.append(('RESET', n+2, Fraction(1), 1))
            for mode, np, vp, pp in choices:
                self.assertEqual(t.spine_modes[mode]['south_parity'], parity)
                self.assertEqual(t.spine_modes[mode]['north_parity'], pp)
                for length in (1, 2, 7, 31, 80):
                    row = t.prefix(mode, pair_prefix((n-1)//2, half, length))
                    self.assertEqual(row['output'], pair_prefix((np-1)//2, (vp-pp)/2, length))

    def test_actual_nonstandard_excursion(self):
        t, half = StreamReverseTransducer(), HalfValueTransducer()
        first = t.prefix('DOUBLE', pair_prefix(1, 1, 96))
        self.assertEqual(first['output'], pair_prefix(1, 2, 96))
        second = t.prefix('CHOICE', first['output'])
        self.assertEqual(second['output'], pair_prefix(1, Fraction(1, 3), 96))
        self.assertFalse(second['event'])
        for j in range(25):
            value = Fraction(1 << j, 3)
            self.assertEqual(value.denominator, 3)
            row = t.prefix('DOUBLE', pair_prefix(1, value, 96))
            self.assertEqual(row['output'], pair_prefix(1, 2*value, 96))
            choice = t.prefix('CHOICE', pair_prefix(1, value, 96))
            self.assertTrue(choice is None or not choice['event'])
            p = value.numerator % 2
            if p == 1:
                self.assertIsNone(half.prefix('RESET', pair_prefix(0, (value-p)/2, 96)))
            else:
                self.assertNotEqual(half.spine_modes['RESET']['south_parity'], p)

    def test_counterfeit_copy_reset_parity_and_termination(self):
        t = HalfValueTransducer()
        row = t.certificate(7, 7, 4, branch='reset')
        bottom = row['input']
        for h, a in ((5, 0), (4, 1), (3, 0)):
            self.assertIsNone(t.path('RESET', bottom, encode_halves(h, a, 4)))
        self.assertIsNone(t.prefix('RESET', encode_halves(3, 2, 4)))
        pre = t.certificate(1, 4, 3, branch='preimage')
        self.assertIsNone(t.path('PREIMAGE', pre['input'], encode_halves(1, 0, 3)))
        double = t.certificate(1, 3, 3, branch='double')
        self.assertIsNone(t.path('DOUBLE0', double['input'], double['output']))
        short = encode_halves(3, 3, 2)
        partial = t.prefix('RESET', short)
        self.assertEqual(decode(partial['output']), (0, 0))
        self.assertEqual(partial['states'][-1], 6)
        self.assertIsNone(t.path('RESET', short, partial['output']))
        full = t.prefix('RESET', tuple(short)+((0, 0),))
        self.assertEqual(decode(full['output']), (4, 0))
        self.assertEqual(full['states'][-1], 5)

    def test_conditional_standard_prefix_has_finite_zero_tails(self):
        t = HalfValueTransducer()
        events = []
        for time, old in enumerate(accepted_reverse_rows()):
            if time == 500:
                break
            n, v = decode(old['input'])
            row = t.certificate(n, v, time+1, branch=old['branch'])
            self.assertEqual(row['event'], old['event'])
            if row['event']:
                events.append(n)
            long = t.prefix(row['mode'], tuple(map(tuple, row['input']))+((0, 0),)*16)
            self.assertEqual(long['output'], tuple(map(tuple, row['output']))+((0, 0),)*16)
            self.assertEqual(len(set(long['states'][-17:])), 1)
        self.assertEqual(events, list(range(1, 2*len(events), 2)))

    def test_seeded_large_standard_carries(self):
        t = HalfValueTransducer()
        rng = random.Random(20261101)
        for _ in range(256):
            n = rng.getrandbits(128) | 1
            odd = rng.getrandbits(128) | 1
            for v, branch in ((odd, 'double'), (3*odd+1, 'preimage'), (n, 'reset')):
                width = max(n, v).bit_length()+1
                row = t.certificate(n, v, width, branch=branch)
                self.assertIn(row['states'][-1], t.finals)
                self.assertEqual(t.prefix(row['mode'], row['input'])['output'],
                                 tuple(map(tuple, row['output'])))


if __name__ == '__main__':
    unittest.main(verbosity=2)
