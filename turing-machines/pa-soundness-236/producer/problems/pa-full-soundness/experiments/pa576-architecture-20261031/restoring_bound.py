#!/usr/bin/env python3
"""Compare y with the remaining rank while restoring that live rank directly."""
from __future__ import annotations
import argparse,json
from pathlib import Path
import finite_table
from TMBuilder import subroutine
p=finite_table.p


class RestoringBound(finite_table.ParameterizedFiniteTable):
    @subroutine
    def prefix(self):
        return [self.take(),self.clear(self.a),
            self.take(),self.move(self.env,self.a),
            self.take(),self.move(self.b,self.a),
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
    print(json.dumps(p.opt.compile_candidate(RestoringBound,args.out)[1],indent=2))
