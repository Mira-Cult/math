import Shared.Beeping.ComparisonTotalized

/-! A finite single-tape result reader for the specific four-stack-to-tape
representation. It moves one cell right, reads the main-stack column, and
moves back. The promised evaluator output is 0 or 1; malformed tapes are not
claimed to represent a result. No events are attached here. -/
namespace Shared.Beeping.ComparisonResultReader
open Turing Turing.PartrecToTM2
open Shared.Beeping.ComparisonSingleTape
open Shared.Beeping.ComparisonTM2
open Shared.ComplexityBridge.TM2Symbols

/-- At offset one the output column is present exactly for the integer 1. -/
def readSymbol (a : Alphabet) : Bool := decide (a.2 K'.main = some Γ'.bit1)

theorem read_right (b : Bool) (final : TM1.Cfg Alphabet Labels1 Store)
    (h : TM2to1.TrCfg (halt [if b then 1 else 0]) final) :
    readSymbol (final.Tape.move Dir.right).head = b := by
  cases h with
  | mk L hL =>
    have hs := TM2to1.stk_nth_val (k := K'.main) 1 (hL K'.main)
    have hh : ((Tape.mk' ∅ (TM2to1.addBottom L)).move Dir.right).head =
        (TM2to1.addBottom L).nth 1 := by
      rw [← Tape.mk'_nth_nat, ← Tape.move_right_n_head]
      rfl
    rw [hh]
    unfold readSymbol
    rw [TM2to1.addBottom_nth_snd, hs]
    cases b <;> decide

inductive State where | start | scan | no | yes deriving DecidableEq, Repr
instance : Inhabited State := ⟨.start⟩
instance : Fintype State := Fintype.ofList [.start,.scan,.no,.yes] (by intro s; cases s <;> simp)

/-- The two live instructions move right then left; the result is encoded in
one of two finite states, and the complete tape is restored. -/
def program : TM0.Machine Alphabet State
  | .start, _ => some (.scan, .move .right)
  | .scan, a => some ((if readSymbol a then .yes else .no), .move .left)
  | .no, a => some (.no, .write a)
  | .yes, a => some (.yes, .write a)

def initial (T : Tape Alphabet) : TM0.Cfg Alphabet State := ⟨.start,T⟩
def resultState (b : Bool) : State := if b then .yes else .no

/-- Reading consumes exactly two post-Turing transitions and restores the
entire original tape and head position. -/
theorem run (b : Bool) (final : TM1.Cfg Alphabet Labels1 Store)
    (h : TM2to1.TrCfg (halt [if b then 1 else 0]) final) :
    runSteps (TM0.step program) 2 (initial final.Tape) =
      some ⟨resultState b, final.Tape⟩ := by
  have hr := read_right b final h
  simp [runSteps,TM0.step,initial,program,hr,resultState,Tape.move_right_left]

/-- A shared evaluator and reader agreement for all candidate/test pairs.
This is sequential composition of two programs at the tape boundary; it
is not yet a single finite transition table. -/
def Reads (R : Nat → Nat → Bool) : Prop :=
  ∃ c : ToPartrec.Code,
    letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
    ∀ e n, ∃ final : TM1.Cfg Alphabet Labels1 Store,
      StateTransition.Reaches (TM0.step (program0 c)) (initial0 c [e,n])
        (TM1to0.trCfg program1 final) ∧
      TM0.step (program0 c) (TM1to0.trCfg program1 final) = none ∧
      runSteps (TM0.step program) 2 (initial final.Tape) =
        some ⟨resultState (R e n), final.Tape⟩

theorem reads_of_singleTape (R : Nat → Nat → Bool)
    (h : Shared.Beeping.ComparisonSingleTape.Implements R) : Reads R := by
  obtain ⟨c,hc⟩ := h
  refine ⟨c, ?_⟩
  letI : Inhabited Labels := ⟨trNormal c Cont'.halt⟩
  intro e n
  obtain ⟨final,hrel,hreach,hhalt⟩ := hc.2 e n
  refine ⟨final,hreach,hhalt, ?_⟩
  apply run (R e n) final
  simpa [result] using hrel

theorem pnp : Reads Shared.PNP.TM2Candidate.compareSAT :=
  reads_of_singleTape _ pnp_has_singleTape

theorem npconp : Reads Shared.NPCONP.TM2Verifier.compare :=
  reads_of_singleTape _ npconp_has_singleTape

end Shared.Beeping.ComparisonResultReader
