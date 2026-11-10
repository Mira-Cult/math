#!/usr/bin/env python3
"""Two-prefix finite truth tables; parameters are covered by finite syntax.

This changes the family and finite record function. The observer and address
enumeration are unchanged. The exact new family and parameter-specialization
argument are separate mathematical obligations, not a trace-equivalence claim.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import rank_shared
from TMBuilder import subroutine
p=rank_shared.p


class ClosedFiniteTable(rank_shared.RankSharedLookup):
    @subroutine
    def prefix(self):
        return [self.take(),self.move(self.b,self.a),
            self.take(),self.copy(self.owner,self.a),
            self.while_decnz(self.a,[
                self.if_not_decnz(self.count,[self.move(self.count,self.c),self.finish_true()]),
                self.c.inc]),self.move(self.count,self.c),
            self.copy(self.a,self.owner),self.bit_b_a(),
            self.move(self.a,self.owner),self.bind_a(),
            self.if_not_decnz(self.b,self.owner.inc),
            self.if_nz(self.owner,[self.take(),self.clear(self.a)])]


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(ClosedFiniteTable,args.out)[1],indent=2))
