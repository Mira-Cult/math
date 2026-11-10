#!/usr/bin/env python3
"""Paid rank-bounded finite tables with explicit arbitrary parameters.

At rank n>=4, support is y<=n-4. Outside it the payoff is true; inside it
the finite signed H game tests equality of the witness bit and predicate.
This is a changed schedule/family, not equal finite records to HWalk.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'architecture'))
import field_sharing
from TMBuilder import subroutine
p=field_sharing.p


class ParameterizedFiniteTable(field_sharing.HFieldSharing):
    @subroutine
    def prefix(self):
        return [self.take(),self.clear(self.a),
            self.take(),self.move(self.env,self.a),
            self.take(),self.move(self.b,self.a),
            self.take(),self.copy(self.owner,self.a),
            self.copy(self.c,self.count),
            self.while_decnz(self.a,self.if_not_decnz(self.c,self.finish_true())),
            self.clear(self.c),self.copy(self.a,self.owner),self.bit_b_a(),
            self.move(self.a,self.owner),self.bind_a(),
            self.if_not_decnz(self.b,self.owner.inc),
            self.if_nz(self.owner,[self.take(),self.clear(self.a)])]


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(ParameterizedFiniteTable,args.out)[1],indent=2))
