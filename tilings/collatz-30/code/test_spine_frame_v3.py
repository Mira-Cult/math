"""Finite tests of the 30-type parity-spine source and its completed witnesses."""
from fractions import Fraction
import unittest

from arithmetic_v2 import decode
from arithmetic_v3 import pair_prefix
from spine_frame_v3 import SystemV3, WitnessTiling, NonstandardWitnessTiling, bits, carry, parity


def integers(row, output=False):
    k, a = decode(row['output' if output else 'input'])
    p = row['north_parity' if output else 'south_parity']
    return 2*k+1, 2*a+p


class ParityFrameTests(unittest.TestCase):
    def test_literal_source_and_root_context(self):
        s = SystemV3()
        self.assertTrue(s.frame_checks())
        self.assertEqual((len(s.tiles), s.manifest()['horizontal_colors'],
                          s.manifest()['vertical_colors']), (30, 8, 6))
        self.assertEqual((s.root_index, s.event_index), (29, 27))
        actual = {t.name.removeprefix('spine:'): t.edges for t in s.tiles if t.name.startswith('spine:')}
        self.assertEqual(actual, {
            'DOUBLE0': (parity(0), carry(0), parity(0), 'h:bg'),
            'DOUBLE1': (parity(0), carry(1), parity(1), 'h:bg'),
            'PREIMAGE': (parity(1), carry(4), parity(0), 'h:bg'),
            'RESET': (parity(1), carry(6), parity(1), 'h:bg')})
        self.assertEqual([t.name for t in s.tiles if t.north == parity(1) and t.east == 'h:bg'], ['ROOT'])

    def test_all_initial_tail_forcing_cases(self):
        s = SystemV3()
        lower = [t for t in s.tiles if t.west == 'h:bg']
        upper = [t for t in s.tiles if t.west.startswith('h:carry:')]
        pairs = [(a, b) for a in lower for b in upper if a.north == b.south]
        self.assertTrue(pairs)
        self.assertEqual({a.name for a, _ in pairs}, {'background'})
        self.assertTrue(all(b.name.startswith('digit:') for _, b in pairs))
        self.assertEqual(s.by_name['ROOT'].east, 'h:bg')
        for final in s.transducer.finals:
            self.assertEqual(s.zero_tail_tile(final).edges,
                             (bits((0, 0)), carry(final), bits((0, 0)), carry(final)))

    def test_completed_quiet_and_accepted_windows(self):
        for policy in ('quiet', 'accepted'):
            t = WitnessTiling(policy=policy)
            self.assertEqual(t.check_window(-2, 95, -2, 48), 9996)
            for y in range(1, 50):
                row = t.row(y)
                self.assertEqual(t.tile_at(0, y).east == t.system.event_color, row['event'])
                tail = t.tile_at(10**6, y)
                self.assertEqual(tail.north, bits((0, 0)))
                self.assertEqual(tail.south, bits((0, 0)))
                self.assertEqual(tail.east, tail.west)
            if policy == 'quiet':
                self.assertFalse(any(r['event'] for r in t.rows))

    def test_accepted_full_integer_certificates(self):
        t = WitnessTiling(policy='accepted')
        expected = (1, 1)
        events = []
        for y in range(1, 200):
            row = t.row(y)
            self.assertEqual(integers(row), expected)
            n, v = integers(row, True)
            if row['event']:
                self.assertEqual(expected[0], expected[1])
                self.assertEqual((n, v), (expected[0]+2, 1))
                events.append(expected[0])
            else:
                self.assertEqual(n, expected[0])
                self.assertEqual(v//2 if v % 2 == 0 else 3*v+1, expected[1])
            expected = n, v
        self.assertEqual(events, list(range(1, 2*len(events), 2)))

    def test_actual_completed_nonstandard_exception(self):
        t = NonstandardWitnessTiling()
        self.assertEqual(t.check_window(-2, 64, -2, 18), 2814)
        for y in range(1, 25):
            self.assertNotEqual(t.tile_at(0, y).east, t.system.event_color)
        old, new, p, pp, mode = t.specification(2)
        self.assertEqual((old, new, p, pp, mode),
                         (Fraction(1), Fraction(-1, 3), 0, 1, 'PREIMAGE'))
        for k in range(128):
            self.assertNotEqual(Fraction(1 << k, 3), 1)

    def test_counterfeit_spine_event_has_no_full_row(self):
        s = SystemV3()
        # Saved target3 but active7: parity and the first equality bit agree.
        bottom = pair_prefix(1, 3, 4)
        one = s.transducer.prefix('RESET', bottom[:1])
        self.assertIsNotNone(one)
        self.assertIsNone(s.transducer.prefix('RESET', bottom[:2]))
        # In the actual nonstandard example, active1/3 has half-value -1/3;
        # it cannot reset target1 even at the first equality bit.
        self.assertIsNone(s.transducer.prefix('RESET', pair_prefix(0, Fraction(-1, 3), 4)))

    def test_rootless_background_and_event_context(self):
        s = SystemV3()
        bg = s.by_name['background']
        self.assertEqual((bg.north, bg.east), (bg.south, bg.west))
        self.assertFalse(bg.north == parity(1) and bg.east == 'h:bg')
        matched = [t.name for t in s.tiles if t.east == s.event_color]
        self.assertIn('spine:RESET', matched)
        self.assertGreater(len(matched), 1)
        self.assertEqual([name for name in matched if name.startswith('spine:')], ['spine:RESET'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
