#!/usr/bin/env python3
"""Paid complete-consumer alternatives for one syntax inverse-pair interface.

All classes preserve ClosedFiniteTable's exact finite records. Result moves,
real callers, both initializers and all cleanup are compiled and counted.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import closed_table
import restored_challenge
from TMBuilder import subroutine
p=closed_table.p


class NodeAtomDecode(restored_challenge.RestoredChallenge):
    @subroutine
    def atom(self):
        return [self.unpair(self.top,self.c,self.b),
            self.move(self.a,self.top),self.move(self.top,self.c),self.lookup_a(),
            self.move(self.c,self.a),self.move(self.a,self.top),self.move(self.top,self.c),
            self.lookup_a(),self.move(self.b,self.top),self.bit_b_a(),
            self.if_zero(self.owner,self.toggle(self.b)),self.move(self.top,self.b)]


class LookupAtomDecode(restored_challenge.RestoredChallenge):
    @subroutine
    def atom(self):
        return [self.unpair(self.c,self.scratch,self.b),
            self.move(self.a,self.c),self.move(self.top,self.scratch),self.lookup_a(),
            self.move(self.c,self.a),self.move(self.a,self.top),self.move(self.top,self.c),
            self.lookup_a(),self.move(self.b,self.top),self.bit_b_a(),
            self.if_zero(self.owner,self.toggle(self.b)),self.move(self.top,self.b)]


class CommonSyntaxDecode(LookupAtomDecode):
    @subroutine
    def h_node(self):
        return [self.take(),self.unpair(self.c,self.scratch,self.b),
            self.label('branch',[
                self.if_decnz(self.a,[self.clear(self.c),self.move(self.c,self.scratch),'break_branch']),
                self.clear(self.scratch)]),
            self.move(self.top,self.c),self.bind_a(),self.toggle(self.owner),'continue_walk']


CLASSES={c.__name__:c for c in (NodeAtomDecode,LookupAtomDecode,CommonSyntaxDecode)}
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--class-name',choices=CLASSES,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    print(json.dumps(p.opt.compile_candidate(CLASSES[args.class_name],args.out)[1],indent=2))
