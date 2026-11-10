#!/usr/bin/env python3
"""One destructive inverse-pair interface for every positional lookup step."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import field_sharing
from TMBuilder import subroutine

p = field_sharing.p


class HSharedLookup(field_sharing.HFieldSharing):
    @subroutine
    def lookup_a(self):
        return [
            self.copy(self.b, self.env),
            self.unpair(self.c, self.scratch, self.b),
            self.while_decnz(self.a, [
                self.clear(self.c), self.move(self.b, self.scratch),
                self.unpair(self.c, self.scratch, self.b),
            ]),
            self.clear(self.scratch), self.move(self.a, self.c),
        ]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(HSharedLookup, args.out)[1], indent=2))
