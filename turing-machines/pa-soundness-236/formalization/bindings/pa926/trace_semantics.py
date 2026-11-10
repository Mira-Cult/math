"""Theory-independent *finite-prefix* utilities for the omega soundness observer.

This module does not decide omega acceptance.  In particular, neither a clean
finite prefix nor a completed finite coverage window establishes soundness.

Event values are None (silent transition), 0, and 1.  A frame consists of the
unary words u(n), u(p), u(x_1), ..., u(x_n), u(b), where u(k)=1**k followed
by 0, n >= 1, and b in {0,1}.  Equal duplicates are permitted; conflicts
are permanently fatal.  All addresses must occur in an accepted infinite
trace, including those whose correct value is zero.
"""

from dataclasses import dataclass, field
from math import isqrt
from typing import Iterable, Iterator, Optional

Address = tuple[int, int, tuple[int, ...]]
Event = Optional[int]


def pair(a: int, b: int) -> int:
    """Cantor's bijection N^2 -> N, oriented with b in the low position."""
    if a < 0 or b < 0:
        raise ValueError("natural arguments required")
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(z: int) -> tuple[int, int]:
    """Independent integer-square-root inverse, without floating point."""
    if z < 0:
        raise ValueError("natural argument required")
    w = (isqrt(8 * z + 1) - 1) // 2
    b = z - w * (w + 1) // 2
    return w - b, b


def scheduled_address(stage: int) -> Address:
    """One stage of a fair schedule with infinitely repeated addresses.

    Residual list-tail data are deliberately ignored.  Consequently each
    address is served at the infinitely many stages returned by
    stage_for_address(address, tail), tail=0,1,... .
    """
    a, rest = unpair(stage)
    n = a + 1
    p, rest = unpair(rest)
    values = []
    for _ in range(n):
        value, rest = unpair(rest)
        values.append(value)
    return n, p, tuple(values)


def stage_for_address(address: Address, tail: int = 0) -> int:
    n, p, values = address
    if n < 1 or len(values) != n or p < 0 or tail < 0:
        raise ValueError("malformed address")
    rest = tail
    for value in reversed(values):
        rest = pair(value, rest)
    return pair(n - 1, pair(p, rest))


def unary(value: int) -> Iterator[int]:
    if value < 0:
        raise ValueError("natural field required")
    yield from (1 for _ in range(value))
    yield 0


def frame(address: Address, bit: int) -> Iterator[int]:
    n, p, values = address
    if n < 1 or p < 0 or len(values) != n or any(x < 0 for x in values):
        raise ValueError("malformed address")
    if bit not in (0, 1):
        raise ValueError("Boolean bit required")
    for value in (n, p, *values, bit):
        yield from unary(value)


@dataclass
class PrefixDecoder:
    """A computable parser of finite prefixes, not an omega decision method."""

    values: dict[Address, int] = field(default_factory=dict)
    records: list[tuple[Address, int]] = field(default_factory=list)
    fields: list[int] = field(default_factory=list)
    ones: int = 0
    error: Optional[str] = None
    physical_transitions: int = 0
    event_count: int = 0

    @property
    def at_boundary(self) -> bool:
        return not self.fields and self.ones == 0

    def feed(self, event: Event) -> None:
        self.physical_transitions += 1
        if self.error is not None or event is None:
            return
        if event not in (0, 1):
            self.error = "event outside the fixed alphabet"
            return
        self.event_count += 1
        if event == 1:
            self.ones += 1
            return
        self.fields.append(self.ones)
        self.ones = 0
        if len(self.fields) == 1 and self.fields[0] == 0:
            self.error = "rank zero is not an address"
            return
        n = self.fields[0]
        if len(self.fields) == n + 3:
            _, p, *tail = self.fields
            bit = tail.pop()
            address = (n, p, tuple(tail))
            if bit not in (0, 1):
                self.error = "non-Boolean record value"
                return
            previous = self.values.get(address)
            if previous is not None and previous != bit:
                self.error = "conflicting completed records"
                return
            self.values[address] = bit
            self.records.append((address, bit))
            self.fields = []

    def feed_all(self, events: Iterable[Event]) -> "PrefixDecoder":
        for event in events:
            self.feed(event)
        return self

    def observed_coverage(self, finite_addresses: Iterable[Address]) -> bool:
        """Check a caller-supplied finite window only; never all coverage."""
        return self.error is None and all(a in self.values for a in finite_addresses)


def finite_domain_prefix(existential: bool, rank: int, matrix, domain, xs=()):
    """Finite-domain regression oracle.  Not standard N-semantics."""
    if rank == 0:
        return bool(matrix(xs))
    children = (
        finite_domain_prefix(not existential, rank - 1, matrix, domain, xs + (x,))
        for x in domain
    )
    return any(children) if existential else all(children)


def finite_domain_bad(rank: int, proof_codes, record, domain) -> bool:
    """Bounded regression specialization of Bad_n, with the correct dual."""
    if rank < 1:
        raise ValueError("rank must be positive")
    return any(
        finite_domain_prefix(False, rank, lambda xs: record(rank, p, xs) == 1, domain)
        for p in proof_codes
    )
