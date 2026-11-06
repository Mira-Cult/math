import Shared.Beeping.NPcoNP.Bootstrap284BitWrite

/-! Executable single-transition packed configurations for the literal table.
The conversion preserves the complete infinite tape and transition event. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284PackedStep
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.Bootstrap284BitSnapshot
open Shared.Beeping.NPcoNP.Bootstrap284BitWrite

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

structure Packed where
  state : Fin 284
  head : Int
  bits : Nat
  deriving Repr, DecidableEq

def toConfig (base : Int) (span : Nat) (c : Packed) : Config 284 :=
  cfg c.state c.head (bitSnapshot base span c.bits)

/-- Reject an out-of-span head; otherwise execute the actual table row,
including its fixed event flag. -/
def stepPacked (base : Int) (span : Nat) (c : Packed) : Option (Packed × Bool) :=
  if base≤c.head ∧ c.head<base+(span : Int) then
    let index := (c.head-base).toNat
    let row := machine.table.row c.state (c.bits.testBit index)
    some (⟨row.next,row.move.apply c.head,bitPut c.bits index row.write⟩,row.beep)
  else none

/-- Every accepted packed step is exactly the literal transition, including
the whole resulting tape and the event flag. -/
theorem stepPacked_sound (base : Int) (span : Nat) (c d : Packed) (event : Bool)
    (hstep : stepPacked base span c=some (d,event)) :
    machine.step (toConfig base span c)=(toConfig base span d,event) := by
  simp only [stepPacked] at hstep
  split at hstep
  · rename_i hh
    simp only [Option.some.injEq,Prod.mk.injEq] at hstep
    obtain ⟨rfl,rfl⟩ := hstep
    have hread : bitSnapshot base span c.bits c.head=c.bits.testBit (c.head-base).toNat := by
      simp [bitSnapshot,hh]
    have hwrite := snapshot_bitPut base c.head span c.bits
      (machine.table.row c.state (c.bits.testBit (c.head-base).toNat)).write hh
    simp only [toConfig,cfg,Machine.step,hread]
    rw [hwrite]
    rfl
  · contradiction

/-- Bounded packed execution rejects an out-of-span transition or a beep. -/
def runSilent (base : Int) (span : Nat) : Nat → Packed → Option Packed
  | 0,c => some c
  | n+1,c =>
    match stepPacked base span c with
    | some (d,false) => runSilent base span n d
    | _ => none

/-- Every accepted bounded packed run is exactly a silent segment of the
literal machine, including its complete final tape. -/
theorem runSilent_sound (base : Int) (span n : Nat) (c d : Packed)
    (hr : runSilent base span n c=some d) :
    silentSegment machine (toConfig base span c) (toConfig base span d) n := by
  induction n generalizing c with
  | zero =>
    simp only [runSilent,Option.some.injEq] at hr
    subst d
    simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ n ih =>
    cases hs : stepPacked base span c with
    | none => simp [runSilent,hs] at hr
    | some x =>
      rcases x with ⟨m,b⟩
      cases b with
      | true => simp [runSilent,hs] at hr
      | false =>
        have ht : runSilent base span n m=some d := by simpa [runSilent,hs] using hr
        have ha := oneSeg machine _ _ (stepPacked_sound base span c m false hs)
        have hb := ih m ht
        have hc := segAdd machine _ _ _ 1 n ha hb
        simpa [Nat.add_comm] using hc

end Shared.Beeping.NPcoNP.Bootstrap284PackedStep
