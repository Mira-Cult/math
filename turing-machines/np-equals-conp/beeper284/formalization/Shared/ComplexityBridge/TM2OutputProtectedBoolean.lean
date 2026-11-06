import Shared.ComplexityBridge.TM2OutputProtectedCompact
import Shared.Codes.FiniteProgramTaggedBoolClassify

/-! A charged finite-table continuation for the protected TM2 output adapter.
It classifies the tagged word before erasing its length. The empty-output
source state and the classifier's invalid state are distinct. The empty
source state returns false on its next step and must be patched before use. -/
/-! This adapter assumes an actual output stack already represented by
`bits.map out.symm`. It does not prove that an earlier numeric transfer
rejects unknown symbols, nor that a timeout or malformed descriptor fails. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputProtectedBoolean
open Turing
open Shared.Codes Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.ComplexityBridge.TM2OutputProtectedCodec
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputProtectedAllScan (cells)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  FiniteProgramOneExit.program (TM2OutputProtectedCompact.program tm enc out)
    FiniteProgramTaggedBoolClassify.program (TM2OutputProtectedCompact.finalStop tm enc out)

def offset (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat :=
  FiniteProgramOneExit.offset (TM2OutputProtectedCompact.program tm enc out)

/-- The nonempty source stop lies inside the concrete linked table. -/
theorem finalStop_bound (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) :
    TM2OutputProtectedCompact.finalStop tm enc out <
      (TM2OutputProtectedCompact.program tm enc out).length := by
  have h := FiniteProgramProtectedCompressLoop.finish_bound width true
  have hlen : (FiniteProgramProtectedCompressLoop.source width).length <
      (FiniteProgramProtectedCompressLoop.program width).length := by
    simp [FiniteProgramProtectedCompressLoop.source, FiniteProgramProtectedCompressLoop.program_length]
  have hp : FiniteProgramProtectedCompressLoop.finish width true <
      (FiniteProgramProtectedCompressLoop.program width).length := by omega
  have hl : (TM2OutputProtectedCompact.positioned width).length =
      (width+4) + (FiniteProgramProtectedCompressLoop.program width).length := by
    simp [TM2OutputProtectedCompact.positioned, FiniteProgramLink.link]
  have ht : (TM2OutputProtectedCompact.program tm enc out).length =
      TM2OutputProtectedCompact.offset tm enc out +
        (TM2OutputProtectedCompact.positioned width).length := by
    simp [TM2OutputProtectedCompact.program, TM2OutputProtectedCompact.offset]
  rw [ht, hl]
  dsimp [TM2OutputProtectedCompact.finalStop]
  omega

theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : valid (program tm enc out) = true :=
  FiniteProgramOneExit.program_valid _ _ _ (TM2OutputProtectedCompact.program_valid tm enc out)
    FiniteProgramTaggedBoolClassify.program_valid (finalStop_bound tm enc out)

theorem program_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : (program tm enc out).length = 47*width+229 := by
  simp [program, FiniteProgramOneExit.offset, TM2OutputProtectedCompact.program_length,
    FiniteProgramTaggedBoolClassify.program_length]

/-- The empty source state is disjoint from every relocated classifier state. -/
theorem empty_before_classifier (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (q : Nat) : TM2OutputProtectedCompact.emptyStop tm enc out < offset tm enc out + q := by
  have h := TM2OutputProtectedPipeline.emptyStop_bound tm enc out
  have hp : (TM2OutputProtectedCompact.source tm enc out).length <
      (TM2OutputProtectedCompact.program tm enc out).length := by
    simp [TM2OutputProtectedCompact.program, FiniteProgramOneExit.program_length,
      FiniteProgramOneExit.offset]
    omega
  change TM2OutputProtectedCompact.emptyStop tm enc out <
    (TM2OutputProtectedCompact.source tm enc out).length at h
  dsimp [offset, FiniteProgramOneExit.offset]
  omega

/-- Classification adds at most eight steps, including the physical handoff. -/
theorem added_cost_bound (bits : List Bool) :
    2 + FiniteProgramTaggedBoolClassify.cost bits ≤ 8 := by
  cases bits <;> simp [FiniteProgramTaggedBoolClassify.cost]

/-- The three physical result states agree with the pinned canonical Boolean
decoder on all bit lists, including empty and overlong inputs. -/
theorem resultState_eq_bitDecode (bits : List Bool) :
    FiniteProgramTaggedBoolClassify.resultState bits =
      match (BitstringEncoding.bitDecode bits : Option Bool) with
      | none => 8
      | some false => 9
      | some true => 10 := by
  cases bits with
  | nil => rfl
  | cons b bs => cases b <;> cases bs <;> rfl

/-- The three classifier outcomes remain live rows in the actual linked
table; each advances the tape head and retains its result state. -/
theorem classifier_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (s : Nat) (hs : s = 8 ∨ s = 9 ∨ s = 10) (t : Tape) :
    step (program tm enc out) (offset tm enc out+s,t) =
      some (.inr (offset tm enc out+s,moveTape false t.2.1 t)) := by
  let p := TM2OutputProtectedCompact.program tm enc out
  let q := FiniteProgramTaggedBoolClassify.program
  let e := TM2OutputProtectedCompact.finalStop tm enc out
  have hslen : s < q.length := by
    rcases hs with rfl | rfl | rfl <;> simp [q]
  have hstep : step q (s,t) = some (.inr (s,moveTape false t.2.1 t)) := by
    rcases hs with rfl | rfl | rfl
    · exact FiniteProgramTaggedBoolClassify.invalid_placeholder t
    · exact FiniteProgramTaggedBoolClassify.false_placeholder t
    · exact FiniteProgramTaggedBoolClassify.true_placeholder t
  have h := FiniteProgramOneExit.continuation p q e
    FiniteProgramTaggedBoolClassify.program_valid (s,t) hslen 1
  simpa [program,offset,FiniteProgramOneExit.offset,p,q,e,shiftConfig,shiftStatus,
    run,advance,hstep] using h

/-- The empty branch still ends in the original false-returning placeholder.
It must be replaced before treating this table as a rejecting evaluator. -/
theorem empty_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (t : Tape) : step (program tm enc out) (TM2OutputProtectedCompact.emptyStop tm enc out,t) =
      some (.inl false) := by
  let p := TM2OutputProtectedCompact.program tm enc out
  let q := FiniteProgramTaggedBoolClassify.program
  let e := TM2OutputProtectedCompact.finalStop tm enc out
  let z := TM2OutputProtectedCompact.emptyStop tm enc out
  have hz : z < p.length := by
    have h := TM2OutputProtectedPipeline.emptyStop_bound tm enc out
    have hp : (TM2OutputProtectedCompact.source tm enc out).length < p.length := by
      simp [p,TM2OutputProtectedCompact.program,FiniteProgramOneExit.program_length,
        FiniteProgramOneExit.offset]
      omega
    change z < (TM2OutputProtectedCompact.source tm enc out).length at h
    omega
  have hne : z ≠ e := TM2OutputProtectedCompact.empty_final_distinct tm enc out
  have h := FiniteProgramTwoExit.source_other p q e e (z,t) hz hne hne
  change step p (z,t) = step (program tm enc out) (z,t) at h
  rw [← h]
  exact TM2OutputProtectedCompact.empty_placeholder tm enc out t

/-- Every actual nonempty halted-output tape reaches the classifier's
result state after the compactor, the two-step handoff and the classifier's
charged steps. Multi-bit outputs reach its distinct invalid state. -/
theorem run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) (t : Tape)
    (ht : TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (TM2BinaryOutputShape.outputBits tm (encode tm enc) (bits.map out.symm))) :
    ∃ u, run (program tm enc out) (0,t)
        (TM2OutputProtectedCompact.cost width (cells tm enc out bs.reverse) +
          (2 + FiniteProgramTaggedBoolClassify.cost bits)) =
      some (.inr (offset tm enc out + FiniteProgramTaggedBoolClassify.resultState bits,u)) := by
  let p := TM2OutputProtectedCompact.program tm enc out
  let q := FiniteProgramTaggedBoolClassify.program
  let e := TM2OutputProtectedCompact.finalStop tm enc out
  let n := TM2OutputProtectedCompact.cost width (cells tm enc out bs.reverse)
  have hp : valid p = true := TM2OutputProtectedCompact.program_valid tm enc out
  have hp0 : 0 < p.length := FiniteProgramLink.valid_nonempty p hp
  have hq : valid q = true := FiniteProgramTaggedBoolClassify.program_valid
  have hq0 : 0 < q.length := FiniteProgramLink.valid_nonempty q hq
  have he : e < p.length := finalStop_bound tm enc out
  obtain ⟨u,hu,hurel⟩ := TM2OutputProtectedCompact.run_nonempty tm enc dec hdec enc0 out bits first bs hrev t ht
  have hpre := FiniteProgramOneExit.first_entry p q e (0,t) (e,u) n hp hp0
    (TM2OutputProtectedCompact.final_placeholder tm enc out) hu
  have hhand := FiniteProgramOneExit.handoff p q e he u
  let bounced := FiniteProgramThreeExit.bounce u
  have ht' : TapeRel bounced (canonical [] false bits).2 :=
    (FiniteProgramThreeExit.bounce_related u).trans hurel
  obtain ⟨v,hv⟩ := FiniteProgramTaggedBoolClassify.run_classify bits (0,bounced) rfl ht'
  have hshift := FiniteProgramOneExit.continuation p q e hq (0,bounced) hq0
    (FiniteProgramTaggedBoolClassify.cost bits)
  rw [hv] at hshift
  refine ⟨v,?_⟩
  change run (FiniteProgramOneExit.program p q e) (0,t)
    (n + (2 + FiniteProgramTaggedBoolClassify.cost bits)) = _
  rw [run_continue _ _ _ _ _ hpre, run_continue _ _ _ _ _ hhand]
  simpa [program,offset,FiniteProgramOneExit.offset,bounced,shiftConfig,shiftStatus,p,q,e] using hshift

/-- Empty output remains in its separate source state. The source state is a
terminal-false placeholder on the next step; it must be replaced by an invalid
continuation before this table can serve as an evaluator. -/
theorem run_empty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape)
    (ht : TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (TM2BinaryOutputShape.outputBits tm (encode tm enc) ([] : List (tm.Γ tm.k₁)))) :
    ∃ u, run (program tm enc out) (0,t) ((width+3)+2) =
      some (.inr (TM2OutputProtectedCompact.emptyStop tm enc out,u)) := by
  let p := TM2OutputProtectedCompact.program tm enc out
  let q := FiniteProgramTaggedBoolClassify.program
  let e := TM2OutputProtectedCompact.finalStop tm enc out
  have hp : valid p = true := TM2OutputProtectedCompact.program_valid tm enc out
  have hp0 : 0 < p.length := FiniteProgramLink.valid_nonempty p hp
  obtain ⟨u,hu,_⟩ := TM2OutputProtectedCompact.run_empty tm enc dec hdec out t ht
  have h := FiniteProgramOneExit.first_entry p q e (0,t)
    (TM2OutputProtectedCompact.emptyStop tm enc out,u) ((width+3)+2) hp hp0
      (TM2OutputProtectedCompact.final_placeholder tm enc out) hu
  exact ⟨u,h⟩

end Shared.ComplexityBridge.TM2OutputProtectedBoolean

