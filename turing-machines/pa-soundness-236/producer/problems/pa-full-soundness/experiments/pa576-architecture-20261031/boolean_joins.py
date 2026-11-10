#!/usr/bin/env python3
"""Paid terminal ownership and Boolean remainder interfaces.

The atom has finished all lookups when these joins run. Its sign is dead
after producing the rejection bit, so consume it instead of preserving it.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import atom_sharing
from TMBuilder import subroutine
p=atom_sharing.p


class ConsumeSign(atom_sharing.CommonSyntaxDecode):
    @subroutine
    def atom(self):
        return [self.unpair(self.c,self.scratch,self.b),
            self.move(self.a,self.c),self.move(self.top,self.scratch),self.lookup_a(),
            self.move(self.c,self.a),self.move(self.a,self.top),self.move(self.top,self.c),
            self.lookup_a(),self.move(self.b,self.top),self.bit_b_a(),
            self.if_not_decnz(self.owner,self.toggle(self.b)),self.move(self.top,self.b)]


class ReturnInSign(atom_sharing.CommonSyntaxDecode):
    @subroutine
    def atom(self):
        return [self.unpair(self.c,self.scratch,self.b),
            self.move(self.a,self.c),self.move(self.top,self.scratch),self.lookup_a(),
            self.move(self.c,self.a),self.move(self.a,self.top),self.move(self.top,self.c),
            self.lookup_a(),self.move(self.b,self.top),self.bit_b_a(),
            self.if_not_decnz(self.b,self.toggle(self.owner)),self.move(self.top,self.owner)]


class BooleanRemainder(ReturnInSign):
    @subroutine
    def bit_b_a(self):
        return [self.while_decnz(self.a,[self.divbase(self.c,self.scratch,self.b,2),
                    self.move(self.b,self.c),self.dec(self.scratch)]),
                self.divbase(self.c,self.scratch,self.b,2),self.clear(self.c),
                self.move(self.b,self.scratch)]


CLASSES={c.__name__:c for c in (ConsumeSign,ReturnInSign,BooleanRemainder)}
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--class-name',choices=CLASSES,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(CLASSES[args.class_name],args.out)[1],indent=2))
