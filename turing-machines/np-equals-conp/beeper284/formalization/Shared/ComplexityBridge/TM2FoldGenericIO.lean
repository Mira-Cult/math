import Shared.ComplexityBridge.TM2FoldIO
import Shared.ComplexityBridge.TM2PolynomialFold

/-! Generic canonical input/output wrapper for the canonical TM2 fold loop.

The loader copies the first input field as a *delimited* block; this is the
canonical encoding of `(initial, [])`, not of `initial` itself. Accordingly
the fold state is a pair `σ × List Bool`. The hypotheses supply an actual
finite-control TM2 core in the canonical model, and bounds on its runs and
serialized states. No arbitrary Lean function is postulated computable by
this module. No finite internal-alphabet normalization or effective program
encoding is asserted. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2FoldGenericIO

open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2PolynomialFold
open Shared.ComplexityBridge.TM2FoldIO

variable {σ α : Type} [BitstringEncoding σ] [BitstringEncoding α]

def result (step : ((σ × List Bool) × α) → (σ × List Bool))
    (p : σ × List α) : σ × List Bool := fold step (p.1,[]) p.2

/-- Actual complete machine run from the input pair through loader, bounded
fold loop, and output cleanup. `q` bounds each real step and all serialized
step data; `r` bounds the final serialized result in the complete input size. -/
theorem run (step : ((σ × List Bool) × α) → (σ × List Bool))
    (core : Turing.TM2ComputableAux Bool Bool) (q r : Polynomial Nat)
    (hstep : ∀ (init : σ) (xs pref : List α) (item : α) (tail : List α),
      xs = pref ++ item :: tail →
      let state := fold step (init,[]) pref
      let B := q.eval (BitstringEncoding.bitEncode (init,xs)).length
      ∃ n ≤ B,
        runSteps core.tm.step n
          (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,item)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step (state,item))).map core.outputAlphabet.symm)) ∧
        (BitstringEncoding.bitEncode state).length ≤ B ∧
        (BitstringEncoding.bitEncode item).length ≤ B ∧
        (BitstringEncoding.bitEncode (state,item)).length ≤ B ∧
        (BitstringEncoding.bitEncode (step (state,item))).length ≤ B)
    (hresult : ∀ (init : σ) (xs : List α),
      (BitstringEncoding.bitEncode (fold step (init,[]) xs)).length ≤
        r.eval (BitstringEncoding.bitEncode (init,xs)).length) :
    ∃ P : Polynomial Nat, ∀ (init : σ) (xs : List α),
      ∃ t ≤ P.eval (BitstringEncoding.bitEncode (init,xs)).length,
        runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step t
          (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet)
            (BitstringEncoding.bitEncode (init,xs))) =
        some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
          (BitstringEncoding.bitEncode (result step (init,xs)))) := by
  let P : Polynomial Nat := Polynomial.X*(Polynomial.C 16*q+Polynomial.C 16) +
    Polynomial.C 2*r + Polynomial.C 4*Polynomial.X + Polynomial.C 8
  refine ⟨P,?_⟩
  intro init xs
  let bits := BitstringEncoding.bitEncode init
  let tail := BitstringEncoding.bitEncode xs
  let out := BitstringEncoding.bitEncode (fold step (init,[]) xs)
  let N := (BitstringEncoding.bitEncode (init,xs)).length
  obtain ⟨n,hn,hr⟩ := loop_done step core (init,[]) xs (q.eval N) (hstep init xs)
  let start := Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .header) none (BitstringEncoding.delimit bits) [] [] [] [] tail)
      (Turing.initList core.tm []).stk)
  let finish := Shared.ComplexityBridge.TM2FoldHandoff.embed core.tm core.inputAlphabet core.outputAlphabet
    (Shared.ComplexityBridge.TM2ContextMapCall.srcEmbed core.tm
      (Shared.ComplexityBridge.TM2ContextMapSplit.cfg (.inr .done) none out [] [] [] [] [])
      (Turing.initList core.tm []).stk)
  have he : BitstringEncoding.bitEncode (init,([] : List Bool)) = BitstringEncoding.delimit bits := by
    change BitstringEncoding.delimit (BitstringEncoding.bitEncode init) ++ [] = _
    simp [bits]
  rw [he] at hr
  change runSteps (Source core.tm core.inputAlphabet core.outputAlphabet).step n start = some finish at hr
  obtain ⟨d,hd,hs⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Source core.tm core.inputAlphabet core.outputAlphabet).step (machine core.tm core.inputAlphabet core.outputAlphabet).step
    (embed core.tm core.inputAlphabet core.outputAlphabet) (terminal core.tm core.inputAlphabet core.outputAlphabet)
    (stable core.tm core.inputAlphabet core.outputAlphabet) (core_step core.tm core.inputAlphabet core.outputAlphabet)
    n start finish (by rfl) hr
  have hcount : xs.length ≤ N := by
    have hh := Shared.ComplexityBridge.CNF.list_length_le_bitEncode xs
    change xs.length ≤ (BitstringEncoding.delimit (BitstringEncoding.bitEncode init)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append]; omega
  have hbits : bits.length ≤ N := by
    change (BitstringEncoding.bitEncode init).length ≤
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode init)++BitstringEncoding.bitEncode xs).length
    simp only [List.length_append,BitstringEncoding.length_delimit]
    omega
  have hout : out.length ≤ r.eval N := hresult init xs
  refine ⟨(4*bits.length+3)+d+(2*out.length+3),?_,?_⟩
  · have hm := Nat.mul_le_mul_right (16*q.eval N+16) hcount
    change (4*bits.length+3)+d+(2*out.length+3) ≤ P.eval N
    simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  · change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      ((4*bits.length+3)+d+(2*out.length+3))
      (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet) (BitstringEncoding.delimit bits++tail)) = _
    rw [show (4*bits.length+3)+d+(2*out.length+3) =
      (4*bits.length+3)+(d+(2*out.length+3)) by omega,runSteps_add,load_run]
    change runSteps (machine core.tm core.inputAlphabet core.outputAlphabet).step
      (d+(2*out.length+3)) (embed core.tm core.inputAlphabet core.outputAlphabet start) = _
    rw [runSteps_add,hs]
    exact cleanup_run core.tm core.inputAlphabet core.outputAlphabet out

/-- The same explicit hypotheses yield a canonical polynomial-time witness. -/
theorem isPolyTime (step : ((σ × List Bool) × α) → (σ × List Bool))
    (core : Turing.TM2ComputableAux Bool Bool) (q r : Polynomial Nat)
    (hstep : ∀ (init : σ) (xs pref : List α) (item : α) (tail : List α),
      xs = pref ++ item :: tail →
      let state := fold step (init,[]) pref
      let B := q.eval (BitstringEncoding.bitEncode (init,xs)).length
      ∃ n ≤ B,
        runSteps core.tm.step n
          (Turing.initList core.tm ((BitstringEncoding.bitEncode (state,item)).map core.inputAlphabet.symm)) =
          some (Turing.haltList core.tm ((BitstringEncoding.bitEncode (step (state,item))).map core.outputAlphabet.symm)) ∧
        (BitstringEncoding.bitEncode state).length ≤ B ∧
        (BitstringEncoding.bitEncode item).length ≤ B ∧
        (BitstringEncoding.bitEncode (state,item)).length ≤ B ∧
        (BitstringEncoding.bitEncode (step (state,item))).length ≤ B)
    (hresult : ∀ (init : σ) (xs : List α),
      (BitstringEncoding.bitEncode (fold step (init,[]) xs)).length ≤
        r.eval (BitstringEncoding.bitEncode (init,xs)).length) :
    ComplexityTheory.IsPolyTime (result step) := by
  obtain ⟨P,hP⟩ := run step core q r hstep hresult
  refine ⟨{
    tm := machine core.tm core.inputAlphabet core.outputAlphabet
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := P
    outputsFun := ?_ }⟩
  rintro ⟨init,xs⟩
  classical
  let t := Nat.find (hP init xs)
  have ht := (Nat.find_spec (hP init xs)).1
  have hr := (Nat.find_spec (hP init xs)).2
  refine ⟨⟨t,?_⟩,ht⟩
  rw [runSteps_iterate] at hr
  change (fun o => o.bind (machine core.tm core.inputAlphabet core.outputAlphabet).step)^[t]
    (some (Turing.initList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (init,xs)).map id))) =
    some (Turing.haltList (machine core.tm core.inputAlphabet core.outputAlphabet)
      ((BitstringEncoding.bitEncode (result step (init,xs))).map id))
  simpa using hr

end Shared.ComplexityBridge.TM2FoldGenericIO
