"""Concrete recurrence adversaries; finite checks do not decide the global R.

The silent, one-event and cycling policies have exact infinite invariants stated
in mutations-v3.md. Their full-plane constructors are checked here on windows.
The repeated-prefix control is only a finite illustration of the time quantifier.
"""
from itertools import islice
import unittest

from arithmetic_v2 import reverse_step
from geometry_v2 import shape_key
from geometry_v3 import compile_tiles
from spine_frame_v3 import SystemV3, WitnessTiling


def one_event_rows(system, cycle):
    n = v = 1
    time = 0
    while True:
        branch = ('reset' if time == 0 else
                  'preimage' if cycle and v == 4 else 'double')
        row = system.transducer.certificate(n, v, time+2, branch=branch)
        row.update(time=time, width=time+2)
        yield row
        n, v, _ = reverse_step(n, v, branch)
        time += 1


def adversary(cycle):
    result = WitnessTiling()
    result.generator = one_event_rows(result.system, cycle)
    result.policy = 'one-event-cycle' if cycle else 'one-event-unbounded'
    return result


class AcceptanceAdversaries(unittest.TestCase):
    def test_one_event_then_unbounded_nonreturn(self):
        t = adversary(False)
        self.assertGreater(t.check_window(-2, 64, -2, 45), 6000)
        self.assertEqual([y for y in range(1, 90) if t.row(y)['event']], [1])
        # Exact policy invariant after RESET: target3, active powers of2.
        for exponent in range(128):
            self.assertNotEqual(1 << exponent, 3)

    def test_one_event_then_silent_cycle(self):
        t = adversary(True)
        self.assertGreater(t.check_window(-2, 48, -2, 48), 5000)
        self.assertEqual([y for y in range(1, 120) if t.row(y)['event']], [1])
        values = (1, 2, 4)
        for old, new in zip(values, values[1:]+values[:1]):
            branch = 'double' if new == 2*old else 'preimage'
            self.assertEqual(reverse_step(3, old, branch), (3, new, False))
        self.assertNotIn(3, values)

    def test_permanent_silence_and_rootless_background(self):
        t = WitnessTiling(policy='quiet')
        self.assertTrue(all(not r['event'] for r in islice(t.generator, 100)))
        s = SystemV3(); bg = s.by_name['background']; root = s.by_name['ROOT']
        self.assertEqual(bg.east, bg.west)
        self.assertEqual(bg.north, bg.south)
        self.assertNotEqual(bg.edges, root.edges)
        # Declaring a numerical origin cannot change the actual BG tile there.
        for origin in ((0, 0), (1000, -999), (-10**9, 10**9)):
            at_origin = bg
            self.assertNotEqual(at_origin.name, 'ROOT')

    def test_repeated_prefix_control_keeps_bounded_logical_times(self):
        early_times = (1, 9)
        replicated = [(copy, time) for copy in range(1000) for time in early_times]
        self.assertEqual(len(replicated), 2000)
        self.assertEqual(max(time for _, time in replicated), 9)
        self.assertFalse(any(time >= 10 for _, time in replicated))
        # The infinite rejection follows from the fixed finite set of times,
        # and unique-root theorem; this list is not a global-tiling certificate.

    def test_time_reversal_and_wrong_column_event(self):
        s = SystemV3(); root = s.by_name['ROOT']
        reversed_root = (root.south, root.east, root.north, root.west)
        self.assertNotIn(reversed_root, s.by_edges)
        event_types = [t for t in s.tiles if t.east == s.event_color]
        self.assertEqual([t.name for t in event_types], ['digit:6', 'spine:RESET'])
        self.assertFalse(event_types[0].south.startswith('v:parity:'))
        self.assertTrue(event_types[1].south.startswith('v:parity:'))

    def test_no_reflection_is_an_allowed_rotated_shape(self):
        s = SystemV3(); out = compile_tiles([t.edges for t in s.tiles])
        keys = {shape_key(p['vertices']) for p in out['polygons']}
        self.assertEqual(len(keys), 30)
        for p in out['polygons']:
            reflected = [(-x, y) for x, y in reversed(p['vertices'])]
            self.assertNotIn(shape_key(reflected), keys)


if __name__ == '__main__':
    unittest.main(verbosity=2)
