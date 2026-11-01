"""Smaller direct ordinary-Collatz row alphabets with certified resets.

Reviewed v1 files are untouched. The reduction allows the genuine Collatz
step 1 -> 4 instead of resetting immediately. Accepted tilings must still have
infinitely many certified resets. Optionally enumerate only odd saved inputs,
which suffice for full positive Collatz. This module is a finite-row layer;
complete geometry/frame/observer integration is separately counted.
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
import itertools
import json

LETTERS = tuple(itertools.product((0, 1), repeat=4))


def encode(saved, active, width):
    if min(saved, active) < 1 or max(saved, active).bit_length() > width:
        raise ValueError("positive pair does not fit finite width")
    return tuple(((saved >> i) & 1, (active >> i) & 1) for i in range(width))


def decode(word):
    if not word or any(len(p) != 2 or any(b not in (0, 1) for b in p) for p in word):
        raise ValueError("nonempty finite binary pair word required")
    return tuple(sum(p[j] << i for i, p in enumerate(word)) for j in (0, 1))


def step(saved, active, *, odd_inputs=True, reset_at_one=True):
    if min(saved, active) < 1 or (odd_inputs and saved % 2 == 0):
        raise ValueError("positive active and correctly enumerated saved input required")
    if active == 1 and reset_at_one:
        nxt = saved + (2 if odd_inputs else 1)
        return nxt, nxt, True
    return saved, 3 * active + 1 if active % 2 else active // 2, False


@dataclass(frozen=True, order=True)
class Tile:
    north: tuple[int, int]
    east: int
    south: tuple[int, int]
    west: int

    def as_dict(self):
        return dict(north=list(self.north), east=self.east,
                    south=list(self.south), west=self.west)


class Transducer:
    """Literal finite carry automaton, with a minimized right-language quotient."""

    def __init__(self, *, odd_inputs=True, merge_odd_reset=False, minimize=True):
        self.odd_inputs = odd_inputs
        self.merge_odd_reset = merge_odd_reset
        self.raw_starts = ({"EVEN": ("E", 0), "CHOICE": ("U",)} if merge_odd_reset
                           else {"EVEN": ("E", 0), "ODD": ("M0",), "RESET": ("R0",)})
        queue = deque(self.raw_starts.values())
        states = set(queue)
        edges = {}
        while queue:
            q = queue.popleft()
            for a in LETTERS:
                target = self.transition(q, a)
                if target is not None:
                    edges[q, a] = target
                    if target not in states:
                        states.add(target)
                        queue.append(target)
        live = {q for q in states if self.accept(q)}
        while True:
            larger = live | {q for (q, _), t in edges.items() if t in live}
            if larger == live:
                break
            live = larger
        states = sorted(live, key=repr)
        edges = {(q, a): t for (q, a), t in edges.items() if q in live and t in live}
        self.raw_state_count, self.raw_tile_count = len(states), len(edges)
        partition = {q: int(self.accept(q)) for q in states}
        if minimize:
            while True:
                sig = {q: (self.accept(q), tuple(partition.get(edges.get((q, a)), -1)
                                                for a in LETTERS)) for q in states}
                names = {s: i for i, s in enumerate(sorted(set(sig.values())))}
                new = {q: names[sig[q]] for q in states}
                stable = all((partition[q] == partition[t]) == (new[q] == new[t])
                             for q in states for t in states)
                partition = new
                if stable:
                    break
        else:
            partition = {q: i for i, q in enumerate(states)}
        self.state_members = {i: tuple(q for q in states if partition[q] == i)
                              for i in sorted(set(partition.values()))}
        self.starts = {m: partition[q] for m, q in self.raw_starts.items()}
        self.finals = frozenset(partition[q] for q in states if self.accept(q))
        self.edges = {(partition[q], a): partition[t] for (q, a), t in edges.items()}
        self.tiles = tuple(sorted({Tile((a[2], a[3]), t, (a[0], a[1]), q)
                                   for (q, a), t in self.edges.items()}))
        self.reset_carry_states = frozenset(partition[q] for q in states if q[0] == "R")
        reset_start = self.starts["CHOICE" if merge_odd_reset else "RESET"]
        self.event_first_tiles = tuple(i for i, t in enumerate(self.tiles)
                                      if t.west == reset_start and t.east in self.reset_carry_states)

    @staticmethod
    def accept(q):
        return q in (("E", 0), ("M", 0), ("R", 0))

    def transition(self, q, a):
        s, v, sp, vp = a
        kind = q[0]
        if kind == "E":
            num = v + q[1] - 2 * vp
            if sp != s or num % 2 or num // 2 not in (-1, 0):
                return None
            return "E", num // 2
        if kind == "M0":
            if v != 1 or sp != s or vp != 0 or (self.odd_inputs and s != 1):
                return None
            return "M", 2
        if kind == "M":
            num = 3 * v + q[1] - vp
            if sp != s or num % 2 or num // 2 not in (0, 1, 2):
                return None
            return "M", num // 2
        if kind == "R0":
            if self.odd_inputs:
                return ("R", 1) if (s, v, sp, vp) == (1, 1, 1, 1) else None
            return ("R", s) if v == 1 and sp == vp == 1-s else None
        if kind == "R":
            carry = q[1]
            if v != 0 or sp != vp or sp != (s + carry) % 2:
                return None
            return "R", (s + carry) // 2
        if kind == "U":
            left = self.transition(("M0",), a)
            right = self.transition(("R0",), a)
            if left is not None and right is not None:
                raise AssertionError("merged first letters must be disjoint")
            return left if left is not None else right
        raise AssertionError(q)

    def path(self, mode, bottom, top):
        if mode not in self.starts or not bottom or len(bottom) != len(top):
            return None
        q = self.starts[mode]
        out = [q]
        for low, high in zip(bottom, top):
            if len(low) != 2 or len(high) != 2:
                return None
            a = tuple(low) + tuple(high)
            if (q, a) not in self.edges:
                return None
            q = self.edges[q, a]
            out.append(q)
        return tuple(out) if q in self.finals else None

    def accepted_modes(self, bottom, top):
        return tuple(m for m in self.starts if self.path(m, bottom, top) is not None)

    def certificate(self, saved, active, width, *, reset_at_one=True):
        sp, vp, event = step(saved, active, odd_inputs=self.odd_inputs, reset_at_one=reset_at_one)
        bottom, top = encode(saved, active, width), encode(sp, vp, width)
        modes = self.accepted_modes(bottom, top)
        if len(modes) != 1:
            raise AssertionError((saved, active, modes))
        mode = modes[0]
        path = self.path(mode, bottom, top)
        if self.merge_odd_reset:
            detected = path[0] == self.starts["CHOICE"] and path[1] in self.reset_carry_states
        else:
            detected = mode == "RESET"
        if detected != event:
            raise AssertionError("event detection disagrees with the literal initial tile")
        return dict(mode=mode, event=event, input=[list(p) for p in bottom],
                    output=[list(p) for p in top], states=list(path))

    def manifest(self):
        return {"variant": "ordinary-Collatz optional reset",
                "odd_inputs_only": self.odd_inputs,
                "saved_successor": 2 if self.odd_inputs else 1,
                "merged_odd_reset_start": self.merge_odd_reset,
                "starts": self.starts, "finals": sorted(self.finals),
                "reset_carry_states": sorted(self.reset_carry_states),
                "event_first_tile_indices": list(self.event_first_tiles),
                "states": {str(i): [list(q) for q in qs] for i, qs in self.state_members.items()},
                "tiles": [t.as_dict() for t in self.tiles],
                "digit_tile_count": len(self.tiles), "horizontal_colors": len(self.state_members),
                "vertical_colors": 4, "raw_state_count": self.raw_state_count,
                "raw_tile_count": self.raw_tile_count,
                "scope": "finite row relation; full-plane frame, geometry and observer costs are separate"}

    def digest(self):
        return hashlib.sha256(json.dumps(self.manifest(), sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def reverse_step(saved, active, branch, *, odd_inputs=True):
    """Exact inverse Collatz edge or equality-certified target advancement."""
    if min(saved, active) < 1 or (odd_inputs and saved % 2 == 0):
        raise ValueError("positive active and correctly enumerated target required")
    if branch == "double":
        return saved, 2 * active, False
    if branch == "preimage":
        if (active - 1) % 3:
            raise ValueError("no integral odd Collatz predecessor")
        value = (active - 1) // 3
        if value < 1 or value % 2 != 1:
            raise ValueError("odd positive predecessor required")
        return saved, value, False
    if branch == "reset" and active == saved:
        return saved + (2 if odd_inputs else 1), 1, True
    raise ValueError("reset requires equality of active value and saved target")


class ReverseTransducer(Transducer):
    """Same local-cost family with inverse edges, target equality, and g=1."""

    def __init__(self, *, odd_inputs=True, merge_odd_reset=True, minimize=True):
        super().__init__(odd_inputs=odd_inputs, merge_odd_reset=merge_odd_reset, minimize=minimize)
        rename = {"EVEN": "DOUBLE", "ODD": "PREIMAGE"}
        self.starts = {rename.get(k, k): v for k, v in self.starts.items()}
        self.raw_starts = {rename.get(k, k): v for k, v in self.raw_starts.items()}

    def transition(self, q, a):
        s, v, sp, vp = a
        kind = q[0]
        if kind == "E":
            # 2*old_value = new_value, with unsigned carry0/1.
            if sp != s or vp != q[1]:
                return None
            return "E", v
        if kind == "M0":
            # 3*new_value+1 = old_value; new value must start with bit1.
            if v != 0 or vp != 1 or sp != s or (self.odd_inputs and s != 1):
                return None
            return "M", 2
        if kind == "M":
            num = 3 * vp + q[1] - v
            if sp != s or num % 2 or num // 2 not in (0, 1, 2):
                return None
            return "M", num // 2
        if kind == "R0":
            if self.odd_inputs:
                return ("R", 1) if (s, v, sp, vp) == (1, 1, 1, 1) else None
            return ("R", s) if v == s and vp == 1 and sp == 1-s else None
        if kind == "R":
            carry = q[1]
            if v != s or vp != 0 or sp != (s + carry) % 2:
                return None
            return "R", (s + carry) // 2
        if kind == "U":
            left = self.transition(("M0",), a)
            right = self.transition(("R0",), a)
            if left is not None and right is not None:
                raise AssertionError("reverse merged first letters must be disjoint")
            return left if left is not None else right
        raise AssertionError(q)

    @staticmethod
    def accept(q):
        return q in (("E", 0), ("M", 0), ("R", 0))

    def certificate(self, saved, active, width, *, branch=None):
        if branch is None:
            branch = "reset" if active == saved else "double"
        sp, vp, event = reverse_step(saved, active, branch, odd_inputs=self.odd_inputs)
        bottom, top = encode(saved, active, width), encode(sp, vp, width)
        modes = self.accepted_modes(bottom, top)
        if len(modes) != 1:
            raise AssertionError((saved, active, branch, modes))
        mode = modes[0]
        path = self.path(mode, bottom, top)
        if self.merge_odd_reset:
            detected = path[0] == self.starts["CHOICE"] and path[1] in self.reset_carry_states
        else:
            detected = mode == "RESET"
        if detected != event:
            raise AssertionError("reverse first-tile event mismatch")
        return dict(mode=mode, branch=branch, event=event, input=[list(p) for p in bottom],
                    output=[list(p) for p in top], states=list(path))

    def manifest(self):
        out = super().manifest()
        out["variant"] = "inverse Collatz edges and equality-certified target reset"
        out["reset_relation"] = "(n,n) -> (n+successor,1)"
        out["growth_columns"] = 1
        return out


def reversed_target_path(target):
    """Return 1-to-target genuine inverse edges if the forward trajectory returns.

    No time, magnitude, or starting-value cutoff exists. This function is partial
    if the target does not reach1; it belongs to the conditional completeness
    constructor, not to local recognition or arithmetic checking.
    """
    if target < 1:
        raise ValueError(target)
    values = [target]
    while values[-1] != 1:
        x = values[-1]
        values.append(3*x+1 if x % 2 else x//2)
    return tuple(reversed(values))


def accepted_reverse_rows(*, odd_inputs=True, merge_odd_reset=True):
    """Conditional complete witness generator: total if all enumerated targets return."""
    transducer = ReverseTransducer(odd_inputs=odd_inputs, merge_odd_reset=merge_odd_reset)
    target = 1
    time = 0
    while True:
        path = reversed_target_path(target)
        for old, new in zip(path, path[1:]):
            branch = "double" if new == 2 * old else "preimage"
            if reverse_step(target, old, branch, odd_inputs=odd_inputs)[1] != new:
                raise AssertionError("not a genuine inverse edge")
            row = transducer.certificate(target, old, time+2, branch=branch)
            row.update(time=time, width=time+2)
            yield row
            time += 1
        row = transducer.certificate(target, target, time+2, branch="reset")
        row.update(time=time, width=time+2)
        yield row
        time += 1
        target += 2 if odd_inputs else 1


def quiet_reverse_rows(*, odd_inputs=True, merge_odd_reset=True):
    """Unconditionally total silent rooted witness: double forever, never reset."""
    transducer = ReverseTransducer(odd_inputs=odd_inputs, merge_odd_reset=merge_odd_reset)
    active = 1
    time = 0
    while True:
        row = transducer.certificate(1, active, time+2, branch="double")
        row.update(time=time, width=time+2)
        yield row
        active *= 2
        time += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all-inputs", action="store_true")
    parser.add_argument("--merge-start", action="store_true")
    parser.add_argument("--reverse", action="store_true")
    parser.add_argument("--manifest", action="store_true")
    args = parser.parse_args()
    cls = ReverseTransducer if args.reverse else Transducer
    t = cls(odd_inputs=not args.all_inputs, merge_odd_reset=args.merge_start)
    if args.manifest:
        out = t.manifest()
    else:
        out = {k: t.manifest()[k] for k in ("odd_inputs_only", "merged_odd_reset_start",
              "digit_tile_count", "horizontal_colors", "vertical_colors", "starts", "finals",
              "event_first_tile_indices")}
        out["manifest_sha256"] = t.digest()
    print(json.dumps(out, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
