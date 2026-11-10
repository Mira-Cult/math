#!/usr/bin/env python3
"""Paid numeric-bound selectors and phase-specific scratch conventions."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'architecture'))
import paired_phase as parent
from TMBuilder import subroutine
p=parent.p


class NumericBound(parent.PairedSingleSign):
    """Inclusive support y<=E, where E is the full packed environment code."""
    @subroutine
    def prepare_predicate(self):
        return [self.copy(self.u,self.stack),self.bit(self.b,self.u),
            self.label('selected',[
                self.if_decnz(self.b,'break_selected'),
                self.copy(self.c,self.env),self.copy(self.a,self.stack),
                self.while_decnz(self.a,self.if_not_decnz(self.c,self.finish_true())),
                self.clear(self.c),self.owner.inc]),
            self.pair(self.c,self.stack,self.env),self.move(self.env,self.c)]


class SharedBitBound(NumericBound):
    """One set/index calling convention, no separate u cell."""
    def reg(self,name):
        return super().reg('k.a' if name=='k.u' else name)

    @subroutine
    def lookup(self,query):
        return [self.copy(self.c,self.env),
            self.while_decnz(query,[self.unpair(self.s2,self.s1,self.c),
                self.move(self.c,self.s1),self.clear(self.s2)]),
            self.unpair(query,self.s1,self.c),self.clear(self.s1)]

    @subroutine
    def lookup_both(self):
        # Return element in a, container in b, matching the selector's bit call.
        return [self.unpair(self.a,self.b,self.data),self.lookup(self.a),
            self.move(self.stack,self.a),self.move(self.a,self.b),self.lookup(self.a),
            self.move(self.b,self.stack)]

    @subroutine
    def matrix_atom(self,kind):
        assert kind==1
        return [self.lookup_both(),self.bit(self.b,self.a),self.move(self.count,self.b)]


class ScratchBound(SharedBitBound):
    """Borrow the copy scratch as tail/quotient only between completed copies."""
    def reg(self,name):
        return super().reg('scratch.copy' if name=='k.s1' else name)


class TerminalScratchBound(ScratchBound):
    """Formula cell is empty during atom lookup; c becomes the bit remainder."""
    def reg(self,name):
        return super().reg('k.c' if name=='k.s2' else name)

    @subroutine
    def lookup(self,query):
        # Called only after terminal payload moves top->data. Thus top=c=0.
        return [self.copy(self.c,self.env),
            self.while_decnz(query,[self.unpair(self.top,self.s1,self.c),
                self.move(self.c,self.s1),self.clear(self.top)]),
            self.unpair(query,self.s1,self.c),self.clear(self.s1)]


class ElevenRegisterBound(TerminalScratchBound):
    """Unbounded cached syntax selector doubles as the atom/selector index.

    Game traversal does not touch a. It must not clear that alias on waiting
    moves: a is the live unbounded formula selector in that phase.
    """
    def reg(self,name):
        return super().reg('k.a' if name=='k.selector' else name)

    @subroutine
    def game_step(self):
        return [self.label('dispatch',[
            self.if_not_decnz(self.selector,[
                self.if_nz(self.top,self.game_universal()),'break_dispatch']),
            self.if_not_decnz(self.selector,[self.selector.inc,'break_dispatch']),
            self.game_implication()]),
            [self.clear(r) for r in (self.stack,self.b,self.c,self.s1)],
            self.toggle(self.owner)]

    @subroutine
    def main(self):
        work=(self.rest,self.top,self.env,self.stack,self.a,self.b,self.c,self.s1,self.owner)
        return [self.copy(self.rest,self.stage),self.unpair(self.count,self.s1,self.rest),
            self.move(self.rest,self.s1),self.count.inc,self.emit_preserving(self.count),
            self.formula_index(),self.label('record',[
                self.take_coordinate(),self.clear(self.stack),
                self.take_coordinate(),self.move(self.env,self.stack),
                self.take_coordinate(),self.move(self.b,self.stack),
                self.take_coordinate(),self.prepare_predicate(),self.decode_top(),
                self.label('game_tail',[
                    self.while_decnz(self.count,[self.emit_coordinate(),self.game_step(),
                        self.if_not_decnz(self.count,[self.toggle(self.owner),'break_game_tail']),
                        self.emit_coordinate(),self.game_step()])]),
                self.game_terminal()]),
            self.toggle(self.count),[self.clear(r) for r in work],
            self.emit_natural(self.count),self.stage.inc]


VARIANTS={'numeric':NumericBound,'shared-bit':SharedBitBound,'copy-scratch':ScratchBound,
          'terminal-scratch':TerminalScratchBound,'eleven-register':ElevenRegisterBound}

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    if args.out.exists():raise ValueError('Fresh output directory required')
    for name,cls in VARIANTS.items():
        _,ledger,_=p.opt.compile_candidate(cls,args.out/name)
        print(name,json.dumps(ledger),flush=True)
