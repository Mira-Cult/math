#!/usr/bin/env python3
"""Remove cleanup operations whose zero postconditions hold on every exit.

StrictCantor exits leave c and scratch zero.  Only a may retain comparison
residue.  Drain restores a,c,scratch to zero, so only rest,env,b need clearing.
"""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
import total_preparation
sys.path.insert(0,str(Path(__file__).resolve().parent/'architecture'))
import ordered_cantor
from TMBuilder import subroutine
p=ordered_cantor.p


class CleanBoundaries(ordered_cantor.StrictCantor):
    @subroutine
    def main(self):
        return [self.copy(self.rest,self.stage),self.unpair(self.a,self.c,self.rest),
            self.move(self.rest,self.c),self.a.inc,self.emit_preserving(self.a),
            self.move(self.count,self.a),self.formula_index(),
            self.label('record',[
                self.unsigned_prefix(),
                self.if_not_decnz(self.b,[self.take(),self.clear(self.a),self.signed_step(True)]),
                self.label('walk_pairs',[self.signed_step(False),self.signed_step(True),'continue_walk_pairs']),
            ]),self.clear(self.a),
            self.while_decnz(self.count,[self.emit_coordinate(),self.clear(self.a)]),
            self.clear(self.rest),self.clear(self.env),self.clear(self.b),
            self.emit_natural(self.top),self.stage.inc]


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    cls=type('TotalRunCleanBoundaries',(total_preparation.TotalPreparation,
        total_preparation.run_dispatch.RunDispatch,CleanBoundaries),{})
    builder,ledger,_=p.opt.compile_candidate(cls,args.out)
    (args.out/'run-dispatch.json').write_text(json.dumps(builder.run_dispatch_certificate,
                                                       sort_keys=True,indent=2)+'\n')
    print(json.dumps(ledger,indent=2))
