import Shared.ComplexityBridge.TM2Compose

namespace Shared.ComplexityBridge.TM2ComposeEncoded
open Shared.ComplexityBridge.TM2Symbols

set_option backward.isDefEq.respectTransparency false in
/-- Compose two actual TM2 witnesses with matching intermediate encodings.
The encoding functions need not be canonical, but the intermediate bits must
match exactly. All transfer and intermediate-size costs are included. -/
theorem compose {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool) (ec : γ → List Bool)
    (F : α → β) (G : β → γ)
    (hF : Turing.TM2ComputableInPolyTime ea eb F) (hG : Turing.TM2ComputableInPolyTime eb ec G) :
    Nonempty (Turing.TM2ComputableInPolyTime ea ec (fun x => G (F x))) := by
  let f := hF.toTM2ComputableAux
  let g := hG.toTM2ComputableAux
  let c := Shared.ComplexityBridge.TM2Compose.composeAux f g
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound f.tm
  refine ⟨{ toTM2ComputableAux := c, time := Shared.ComplexityBridge.TM2Compose.timePolynomial hF.time hG.time D, outputsFun := ?_ }⟩
  intro a
  let rF := hF.outputsFun a
  let rG := hG.outputsFun (F a)
  let n := rF.steps
  let m := rG.steps
  let input := ea a
  let middle := eb (F a)
  let output := ec (G (F a))
  have hf : runSteps f.tm.step n (Turing.initList f.tm (input.map f.inputAlphabet.symm)) =
      some (Turing.haltList f.tm (middle.map f.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact rF.evals_in_steps
  have hg : runSteps g.tm.step m (Turing.initList g.tm (middle.map g.inputAlphabet.symm)) =
      some (Turing.haltList g.tm (output.map g.outputAlphabet.symm)) := by
    rw [runSteps_iterate]
    exact rG.evals_in_steps
  have hfirst : n ≤ hF.time.eval input.length := rF.steps_le_m
  have hsecond : m ≤ hG.time.eval middle.length := rG.steps_le_m
  have hlength := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length f.tm
    (input.map f.inputAlphabet.symm) n (Turing.haltList f.tm (middle.map f.outputAlphabet.symm)) hf f.tm.k₁
  have hmid : middle.length ≤ input.length+n*D := by simpa [Turing.haltList,D] using hlength
  have hmul : n*D ≤ hF.time.eval input.length*D := Nat.mul_le_mul_right D hfirst
  have hmid' : middle.length ≤ input.length+hF.time.eval input.length*D := by omega
  have hsecond' := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono hG.time hmid'
  let t := n+(2*middle.length+2)+m
  have hrun := Shared.ComplexityBridge.TM2Compose.compose_run f.tm g.tm f.outputAlphabet g.inputAlphabet
    (input.map f.inputAlphabet.symm) middle (output.map g.outputAlphabet.symm) n m hf hg
  refine ⟨⟨t,?_⟩,?_⟩
  · rw [runSteps_iterate] at hrun
    exact hrun
  · change t ≤ (Shared.ComplexityBridge.TM2Compose.timePolynomial hF.time hG.time D).eval input.length
    rw [Shared.ComplexityBridge.TM2Compose.timePolynomial_eval]
    dsimp [t]
    omega

end Shared.ComplexityBridge.TM2ComposeEncoded
