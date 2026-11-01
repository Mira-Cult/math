"""Finite evidence for the 31-type infinite-stream source; no recurrence decision."""
from fractions import Fraction
import unittest

from arithmetic_v2 import decode
from scaffold_v3 import (SystemV3, WitnessTiling, NonstandardWitnessTiling,
                         bits, carry, residue_bits)


class StreamFrameTests(unittest.TestCase):
    def test_literal_source_and_initial_tail_forcing(self):
        s = SystemV3()
        self.assertTrue(s.frame_checks())
        self.assertEqual((len(s.tiles), s.manifest()['horizontal_colors'],
                          s.manifest()['vertical_colors']), (31, 10, 5))
        self.assertFalse(any(t.name.startswith('frontier') for t in s.tiles))
        lower = [t for t in s.tiles if t.west == 'h:bg']
        upper = [t for t in s.tiles if t.west.startswith('h:carry:')]
        compatible = [(a, b) for a in lower for b in upper if a.north == b.south]
        self.assertTrue(compatible)
        self.assertEqual({a.name for a, _ in compatible}, {'background'})
        self.assertTrue(all(b.name.startswith('digit:') for _, b in compatible))
        for q in s.transducer.finals:
            t = s.zero_tail_tile(q)
            self.assertEqual(t.north, bits((0, 0)))
            self.assertEqual(t.edges, (bits((0, 0)), carry(q), bits((0, 0)), carry(q)))

    def test_closed_pair_universes(self):
        s = SystemV3()
        families = s.closed_pair_families()
        self.assertEqual(families, [
            {'name': 'root', 'left': 29, 'rights': [30], 'interface': 'h:initial'},
            {'name': 'choice', 'left': 26, 'rights': [19, 22], 'interface': 'h:carry:0'}])
        removed = {i for f in families for i in [f['left'], *f['rights']]}
        replacements = sum(len(f['rights']) for f in families)
        self.assertEqual((len(removed), replacements, len(s.tiles)-len(removed)+replacements), (5, 3, 29))

    def test_completed_standard_constructors(self):
        for policy in ('quiet', 'accepted'):
            t = WitnessTiling(policy=policy)
            self.assertEqual(t.check_window(-2, 95, -2, 48), 9996)
            for y in range(1, 50):
                row = t.row(y)
                self.assertEqual(t.tile_at(1, y).east == t.system.event_color, row['event'])
                tail = t.tile_at(10**6, y)
                self.assertEqual(tail.north, bits((0, 0)))
                self.assertEqual(tail.south, bits((0, 0)))
                self.assertEqual(tail.east, tail.west)
            if policy == 'quiet':
                self.assertFalse(any(r['event'] for r in t.rows))

    def test_conditional_constructor_inverse_certificates(self):
        t = WitnessTiling(policy='accepted')
        old = (1, 1)
        targets = []
        for y in range(1, 200):
            row = t.row(y)
            self.assertEqual(decode(row['input']), old)
            n, v = decode(row['output'])
            if row['event']:
                self.assertEqual(old[0], old[1])
                self.assertEqual((n, v), (old[0]+2, 1))
                targets.append(old[0])
            else:
                self.assertEqual(n, old[0])
                self.assertEqual(v//2 if v % 2 == 0 else 3*v+1, old[1])
            old = n, v
        self.assertEqual(targets, list(range(1, 2*len(targets), 2)))

    def test_actual_completed_nonstandard_exception(self):
        t = NonstandardWitnessTiling()
        self.assertEqual(t.check_window(-2, 64, -2, 18), 2814)
        for y in range(1, 25):
            self.assertNotEqual(t.tile_at(1, y).east, t.system.event_color)
        for width in range(1, 100):
            prefix = residue_bits(Fraction(1, 3), width)
            value = sum(b << i for i, b in enumerate(prefix))
            self.assertEqual((3*value-1) % (1 << width), 0)
        # Exact nonacceptance invariant: subsequent values are 2^k/3 and cannot
        # equal the saved target1. Finite windows only check emitted interfaces.
        for k in range(128):
            self.assertNotEqual(Fraction(1 << k, 3), 1)

    def test_nonstandard_value_cannot_counterfeit_reset(self):
        s = SystemV3()
        old = residue_bits(Fraction(1, 3), 8)
        output = residue_bits(1, 8)
        new_saved = residue_bits(3, 8)
        q = s.transducer.starts['CHOICE']
        accepted = 0
        for i in range(8):
            letter = int(i == 0), old[i], new_saved[i], output[i]
            if (q, letter) not in s.transducer.edges:
                break
            q = s.transducer.edges[q, letter]
            accepted += 1
        self.assertEqual(accepted, 1)  # first-bit event motif alone is insufficient

    def test_event_context_and_rootless_background(self):
        s = SystemV3()
        self.assertEqual(s.event_first_indices, (19,))
        self.assertEqual([i for i, t in enumerate(s.transducer.tiles)
                          if t.east == s.event_carry], [0, 19])
        self.assertNotIn(s.transducer.tiles[0].west, s.transducer.starts.values())
        bg = s.by_name['background']
        self.assertEqual((bg.north, bg.east), (bg.south, bg.west))
        self.assertNotEqual(bg.east, 'h:initial')
        # A coordinate supplied by a harness does not make this array rooted.
        self.assertNotEqual(bg.name, 'ROOT')


if __name__ == '__main__':
    unittest.main(verbosity=2)
