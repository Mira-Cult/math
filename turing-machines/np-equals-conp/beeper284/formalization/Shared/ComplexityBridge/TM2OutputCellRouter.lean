import Shared.Codes.FiniteProgramThreeExit
import Shared.ComplexityBridge.TM2OutputCellClassify

/-! Connect the three canonical cell classifications to three distinct live
continuations. The continuations are placeholder rows, not an output loop. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputCellRouter
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputCellClassify
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTwoWordClassify
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def falseState (width : Nat) : Nat := state width (mask true false)
def trueState (width : Nat) : Nat := state width (mask false true)
def endState (width : Nat) : Nat := state width (mask false false)

def core (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) : Program :=
  Shared.Codes.FiniteProgramTwoWordClassify.program
    (code tm enc out marked (some false)) (code tm enc out marked (some true))

def routed (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) : Program :=
  Shared.Codes.FiniteProgramThreeExit.program (core tm enc out marked)
    (falseState width) (trueState width) (endState width)

def exit (base : Nat) : Option Bool → Nat
  | some false => base+3
  | some true => base+4
  | none => base+5

theorem states_bound (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) :
    falseState width < (core tm enc out marked).length ∧
      trueState width < (core tm enc out marked).length ∧ endState width < (core tm enc out marked).length := by
  simp [core,falseState,trueState,endState,state,mask]
  omega

theorem states_distinct (width : Nat) :
    falseState width ≠ trueState width ∧ falseState width ≠ endState width ∧
      trueState width ≠ endState width := by simp [falseState,trueState,endState,state,mask]

theorem routed_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) : valid (routed tm enc out marked) = true := by
  apply Shared.Codes.FiniteProgramThreeExit.program_valid
  exact Shared.Codes.FiniteProgramTwoWordClassify.program_valid _ _

theorem routed_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool) :
    (routed tm enc out marked).length = 4*(width+1)+6 := by simp [routed,core]

/-- On a canonical cell, classification and two handoff transitions enter
the corresponding distinct live continuation. The handoff's two moves have
an explicit tape representation; it is blank-equivalent to the prior tape. -/
theorem classify_and_route (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool)
    (value : Option Bool) (L suffix : List Bool) :
    let actual := code tm enc out marked value
    let after := tapeAt (consumed L actual) suffix
    run (routed tm enc out marked) (0,tapeAt L (actual++suffix)) (width+2) =
      some (.inr (exit (core tm enc out marked).length value,
        Shared.Codes.FiniteProgramThreeExit.bounce after)) := by
  let p := core tm enc out marked
  let a := falseState width
  let b := trueState width
  let c := endState width
  let actual := code tm enc out marked value
  let after := tapeAt (consumed L actual) suffix
  let target := state width (mask (value == some false) (value == some true))
  have hvalid : valid p = true := Shared.Codes.FiniteProgramTwoWordClassify.program_valid _ _
  have hbound := states_bound tm enc out marked
  change a < p.length ∧ b < p.length ∧ c < p.length at hbound
  have hdistinct := states_distinct width
  change a ≠ b ∧ a ≠ c ∧ b ≠ c at hdistinct
  have ha : ∃ r, ∀ t, step p (a,t) = some (.inl r) := by
    refine ⟨false,?_⟩
    intro t
    simpa [p,core,a,falseState,code_length] using
      Shared.Codes.FiniteProgramTwoWordClassify.step_terminal
        (code tm enc out marked (some false)) (code tm enc out marked (some true)) (mask true false) t
  have hb : ∃ r, ∀ t, step p (b,t) = some (.inl r) := by
    refine ⟨false,?_⟩
    intro t
    simpa [p,core,b,trueState,code_length] using
      Shared.Codes.FiniteProgramTwoWordClassify.step_terminal
        (code tm enc out marked (some false)) (code tm enc out marked (some true)) (mask false true) t
  have hc : ∃ r, ∀ t, step p (c,t) = some (.inl r) := by
    refine ⟨false,?_⟩
    intro t
    simpa [p,core,c,endState,code_length] using
      Shared.Codes.FiniteProgramTwoWordClassify.step_terminal
        (code tm enc out marked (some false)) (code tm enc out marked (some true)) (mask false false) t
  have hscan : run p (0,tapeAt L (actual++suffix)) width = some (.inr (target,after)) := by
    exact classify_cell tm enc dec hdec out marked value L suffix
  have hrun := Shared.Codes.FiniteProgramThreeExit.first_entry p a b c
    (0,tapeAt L (actual++suffix)) (target,after) width hvalid (by have := hbound.1; omega) ha hb hc hscan
  change run (Shared.Codes.FiniteProgramThreeExit.program p a b c) _ (width+2) = _
  rw [run_continue _ _ _ _ _ hrun]
  cases value with
  | none =>
    simpa [target,c,endState,exit] using
      Shared.Codes.FiniteProgramThreeExit.handoff_third p a b c hbound.2.2 after
  | some v =>
    cases v with
    | false =>
      simpa [target,a,falseState,exit] using
        Shared.Codes.FiniteProgramThreeExit.handoff_first p a b c hbound.1 hdistinct.1 hdistinct.2.1 after
    | true =>
      simpa [target,b,trueState,exit] using
        Shared.Codes.FiniteProgramThreeExit.handoff_second p a b c hbound.2.1 hdistinct.2.2 after

/-- The same routed run starts from any blank-equivalent physical tape and
leaves a tape blank-equivalent to the position after the classified word. -/
theorem classify_and_route_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (marked : Bool)
    (value : Option Bool) (L suffix : List Bool) (t : Tape)
    (ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel t
      (tapeAt L (code tm enc out marked value ++ suffix))) :
    ∃ t', run (routed tm enc out marked) (0,t) (width+2) =
      some (.inr (exit (core tm enc out marked).length value,t')) ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel t'
        (tapeAt (consumed L (code tm enc out marked value)) suffix) := by
  let after := tapeAt (consumed L (code tm enc out marked value)) suffix
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (routed tm enc out marked) (0,t)
    (0,tapeAt L (code tm enc out marked value ++ suffix)) rfl ht (width+2)
  rw [classify_and_route tm enc dec hdec out marked value L suffix] at h
  cases hr : run (routed tm enc out marked) (0,t) (width+2) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = exit (core tm enc out marked).length value ∧
        Shared.Codes.FiniteProgramTapeEquiv.TapeRel t' (Shared.Codes.FiniteProgramThreeExit.bounce after) at h
      refine ⟨t',?_,?_⟩
      · rw [h.1]
      · exact h.2.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related after)

/-- The three continuation rows are explicit false-result placeholders. -/
theorem continuation_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (marked : Bool) (value : Option Bool) (t : Tape) :
    step (routed tm enc out marked) (exit (core tm enc out marked).length value,t) = some (.inl false) := by
  have h := Shared.Codes.FiniteProgramThreeExit.continuation_rows (core tm enc out marked)
    (falseState width) (trueState width) (endState width)
  cases value with
  | none =>
    cases ht : t.2.1 <;> simp only [routed,exit,step,h.2.2,Shared.Codes.FiniteProgramThreeExit.stop,ht] <;> rfl
  | some v =>
    cases v with
    | false => cases ht : t.2.1 <;> simp only [routed,exit,step,h.1,Shared.Codes.FiniteProgramThreeExit.stop,ht] <;> rfl
    | true => cases ht : t.2.1 <;> simp only [routed,exit,step,h.2.1,Shared.Codes.FiniteProgramThreeExit.stop,ht] <;> rfl

end Shared.ComplexityBridge.TM2OutputCellRouter
