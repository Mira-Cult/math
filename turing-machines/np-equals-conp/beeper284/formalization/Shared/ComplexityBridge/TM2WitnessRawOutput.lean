import Shared.ComplexityBridge.TM2WitnessRaw

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2WitnessOutput
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

theorem loaded_run_raw (frame witness query : List Bool) :
    let size := frame.length+witness.length+query.length
    let start := Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none
      frame witness query [] [] []
    ∃ t ≤ outputBound size, runSteps machine.step t (embed start) =
      some (Turing.haltList machine [Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw frame witness query]) := by
  let size := frame.length+witness.length+query.length
  let B := frame.length+query.length
  let P := loopBound size
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let start := Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none frame witness query [] [] []
  let answer := Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw frame witness query
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw_progress frame witness query false false none
  change n ≤ (B+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound B at hn
  change runSteps Source.step n start = some q at hr
  change q.l = some (.inl (if answer then .yes else .no)) at hq
  have hB : B ≤ size := by dsimp [B,size]; omega
  have hm := Nat.mul_le_mul (show B+1 ≤ size+1 by omega) (Shared.ComplexityBridge.TM2WitnessLookup.iterationBound_mono hB)
  have hnP : n ≤ P := by dsimp [P,loopBound]; exact le_trans hn hm
  have hterminal : terminal q := by
    unfold terminal
    cases he : answer with
    | false => right; simpa [he] using hq
    | true => left; simpa [he] using hq
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step embed terminal stable source_step n start q hterminal hr
  have hstart : ∀ k : Key, (start.stk k).length ≤ size := by
    intro k
    cases k <;> simp [start,Shared.ComplexityBridge.TM2WitnessLookup.cfg,
      Shared.ComplexityBridge.TM2WitnessLookup.stackVals,size] <;> omega
  have hstack : ∀ k : Key, (q.stk k).length ≤ size+P*D := by
    intro k
    have hh := Shared.ComplexityBridge.TM2GenericStackBound.run_length Source n start q hr k
    have hm := Nat.mul_le_mul_right D hnP
    have hs := hstart k
    change (q.stk k).length ≤ (start.stk k).length+n*D at hh
    omega
  obtain ⟨c,hc,hcr⟩ := sweep_all answer q.stk (size+P*D) hstack
  refine ⟨a+1+c,?_,?_⟩
  · change a+1+c ≤ outputBound size
    change a+1+c ≤ P+1+6*(size+P*D+1)+1
    omega
  · change runSteps machine.step (a+1+c) (embed start) = _
    rw [show a+1+c = a+(1+c) by omega,runSteps_add,har]
    change runSteps machine.step (1+c) (embed q) = _
    rw [runSteps_add]
    change (machine.step (embed q)).bind (runSteps machine.step c) = _
    rw [dispatch q answer hq]
    exact hcr


theorem loaded_run_raw_polynomial (frame witness query : List Bool) :
    let size := frame.length+witness.length+query.length
    let start := Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none frame witness query [] [] []
    ∃ t ≤ timePolynomial.eval size, runSteps machine.step t (embed start) =
      some (Turing.haltList machine [Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw frame witness query]) := by
  simpa [timePolynomial_eval] using loaded_run_raw frame witness query

end Shared.ComplexityBridge.TM2WitnessOutput
