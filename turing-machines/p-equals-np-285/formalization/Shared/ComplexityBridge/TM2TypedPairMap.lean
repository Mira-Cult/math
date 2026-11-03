import Shared.ComplexityBridge.TM2PairMap
import Shared.ComplexityBridge.CNFLiteralConstructor
import Shared.ComplexityBridge.TM2ListAppend

set_option backward.isDefEq.respectTransparency false

/-! Preserve an arbitrary canonically encoded second component while applying
a polynomial-time function to the first. This uses the existing executable
TM2 pair parser, core machine, and charged re-serialization. -/
namespace Shared.ComplexityBridge.TM2TypedPairMap
open Shared.ComplexityBridge.TM2PairMap
open Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

variable {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β] [BitstringEncoding γ]

def pairMap (F : α → β) (p : α × γ) : β × γ := (F p.1,p.2)

theorem pair_run (f : Turing.FinTM2) (inp : f.Γ f.k₀ ≃ Bool) (out : f.Γ f.k₁ ≃ Bool)
    (x : α) (w : γ) (y : β) (n : Nat)
    (hf : runSteps f.step n (Turing.initList f ((BitstringEncoding.bitEncode x).map inp.symm)) =
      some (Turing.haltList f ((BitstringEncoding.bitEncode y).map out.symm))) :
    runSteps (machine f inp out).step
      ((3*(BitstringEncoding.bitEncode x).length+2)+n+(2*(BitstringEncoding.bitEncode y).length+2))
      (Turing.initList (machine f inp out) (BitstringEncoding.bitEncode (x,w))) =
      some (Turing.haltList (machine f inp out) (BitstringEncoding.bitEncode (y,w))) := by
  let payload := BitstringEncoding.bitEncode x
  let tail := BitstringEncoding.bitEncode w
  let output := BitstringEncoding.bitEncode y
  have hsplit := split_run f inp out payload tail
  have hcore := core_run f inp out tail n (Turing.initList f (payload.map inp.symm))
    (Turing.haltList f (output.map out.symm)) hf
  have hpost := post_run f inp out output tail
  change runSteps (machine f inp out).step ((3*payload.length+2)+n+(2*output.length+2))
    (Turing.initList (machine f inp out) (BitstringEncoding.delimit payload ++ tail)) =
    some (Turing.haltList (machine f inp out) (BitstringEncoding.delimit output ++ tail))
  rw [show (3*payload.length+2)+n+(2*output.length+2) =
    (3*payload.length+2)+(n+(2*output.length+2)) by omega,runSteps_add,hsplit]
  change runSteps (machine f inp out).step (n+(2*output.length+2))
    (coreEmbed f tail (Turing.initList f (payload.map inp.symm))) = _
  rw [runSteps_add,hcore]
  exact hpost

/-- Generic first-component map with full input, intermediate-output, and
transfer costs charged in the polynomial. -/
theorem pairMap_isPolyTime (F : α → β) (hF : ComplexityTheory.IsPolyTime F) :
    ComplexityTheory.IsPolyTime (pairMap (γ := γ) F) := by
  rcases hF with ⟨hF⟩
  let f := hF.toTM2ComputableAux
  let c := pairAux f
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound f.tm
  refine ⟨{ toTM2ComputableAux := c, time := timePolynomial hF.time D, outputsFun := ?_ }⟩
  intro a
  rcases a with ⟨x,w⟩
  let r := hF.outputsFun x
  let n := r.steps
  let payload := BitstringEncoding.bitEncode x
  let result := BitstringEncoding.bitEncode (F x)
  let bits := BitstringEncoding.bitEncode (x,w)
  have hf : runSteps f.tm.step n (Turing.initList f.tm (payload.map f.inputAlphabet.symm)) =
      some (Turing.haltList f.tm (result.map f.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact r.evals_in_steps
  have hn : n ≤ hF.time.eval payload.length := r.steps_le_m
  have hlen : payload.length ≤ bits.length := by
    change payload.length ≤ (BitstringEncoding.delimit payload ++ BitstringEncoding.bitEncode w).length
    simp only [List.length_append,BitstringEncoding.length_delimit]
    omega
  have htime := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono hF.time hlen
  have hn' : n ≤ hF.time.eval bits.length := le_trans hn htime
  have hstack := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length f.tm
    (payload.map f.inputAlphabet.symm) n (Turing.haltList f.tm (result.map f.outputAlphabet.symm)) hf f.tm.k₁
  have hresult : result.length ≤ payload.length+n*D := by simpa [Turing.haltList,D] using hstack
  have hmul : n*D ≤ hF.time.eval bits.length*D := Nat.mul_le_mul_right D hn'
  let t := (3*payload.length+2)+n+(2*result.length+2)
  have hrun := pair_run f.tm f.inputAlphabet f.outputAlphabet x w (F x) n hf
  refine ⟨⟨t,?_⟩,?_⟩
  · rw [runSteps_iterate] at hrun
    change (fun o => o.bind c.tm.step)^[t]
      (some (Turing.initList c.tm (bits.map id))) =
      some (Turing.haltList c.tm ((BitstringEncoding.bitEncode (pairMap F (x,w))).map id))
    simp only [List.map_id]
    exact hrun
  · change t ≤ (timePolynomial hF.time D).eval bits.length
    rw [timePolynomial_eval]
    dsimp [t]
    have hfactor : (2*D+1)*hF.time.eval bits.length = 2*(hF.time.eval bits.length*D) + hF.time.eval bits.length := by ring
    rw [hfactor]
    omega

open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

def prependChoice (p : (Nat × Nat) × Clause) : Clause :=
  (selector (p.1.1+p.1.2),true)::p.2

/-- One loop body for `choices` constructs its exact selector literal while
preserving the clause accumulator, then prepends the result. -/
theorem prependChoice_isPolyTime : ComplexityTheory.IsPolyTime prependChoice := by
  let F : Nat × Nat → Literal := fun p => (selector (p.1+p.2),true)
  have hf : ComplexityTheory.IsPolyTime F := Shared.ComplexityBridge.CNFLiteralConstructor.choice_literal_isPolyTime
  have hp : ComplexityTheory.IsPolyTime (pairMap (γ := Clause) F) := pairMap_isPolyTime F hf
  have hc : ComplexityTheory.IsPolyTime (Shared.ComplexityBridge.TM2ListAppend.cons (α := Literal)) :=
    Shared.ComplexityBridge.TM2ListAppend.cons_isPolyTime
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp (pairMap F)
    Shared.ComplexityBridge.TM2ListAppend.cons hp hc

def prependGuard (p : Nat × Clause) : Clause := (selector p.1,false)::p.2

/-- The guard prefix is built with the same accumulator-preserving adapter. -/
theorem prependGuard_isPolyTime : ComplexityTheory.IsPolyTime prependGuard := by
  let F : Nat → Literal := fun i => (selector i,false)
  have hf : ComplexityTheory.IsPolyTime F := Shared.ComplexityBridge.CNFLiteralConstructor.guard_literal_isPolyTime
  have hp : ComplexityTheory.IsPolyTime (pairMap (γ := Clause) F) := pairMap_isPolyTime F hf
  have hc : ComplexityTheory.IsPolyTime (Shared.ComplexityBridge.TM2ListAppend.cons (α := Literal)) :=
    Shared.ComplexityBridge.TM2ListAppend.cons_isPolyTime
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp (pairMap F)
    Shared.ComplexityBridge.TM2ListAppend.cons hp hc

/-- The exact choice list can be built backwards by repeated applications
of the proved loop body, followed by the separately proved list reversal. -/
theorem choices_reverse_step (start count : Nat) :
    (choices start (count+1)).reverse =
      prependChoice ((start,count),(choices start count).reverse) := by
  simp [choices,List.range_succ,prependChoice,List.reverse_append]

/-- Applying the guard prefix to the even-renamed clause is the existing
`guardClause`, not a new front-end convention. -/
theorem guardClause_eq_prepend (i : Nat) (c : Clause) :
    guardClause i c = prependGuard (i,evenClause c) := rfl

namespace Fixtures
example : prependChoice ((2,1),[(0,false)]) = [(7,true),(0,false)] := rfl
example : prependGuard (2,[(4,true)]) = [(5,false),(4,true)] := rfl
end Fixtures

end Shared.ComplexityBridge.TM2TypedPairMap
