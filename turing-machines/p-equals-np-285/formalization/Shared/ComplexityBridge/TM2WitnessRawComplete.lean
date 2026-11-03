import Shared.ComplexityBridge.TM2WitnessRawOutput

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2WitnessComplete
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

theorem input_run_raw (first witness query : List Bool) :
    let bits := Shared.ComplexityBridge.TM2WitnessInput.inputBits
      first witness query
    ∃ t ≤ timePolynomial.eval bits.length,
      runSteps machine.step t (Turing.initList machine bits) =
        some (Turing.haltList machine [Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw first witness query]) := by
  let inner := BitstringEncoding.bitEncode (witness,query)
  let bits := Shared.ComplexityBridge.TM2WitnessInput.inputBits first witness query
  let size := first.length+witness.length+query.length
  let answer := Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw first witness query
  let finish := Shared.ComplexityBridge.TM2WitnessInput.finalCfg first witness query
  let start := Shared.ComplexityBridge.TM2WitnessOutput.embed
    (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none first witness query [] [] [])
  obtain ⟨n,hn,hr⟩ := Shared.ComplexityBridge.TM2WitnessInput.load_input first witness query
  change n ≤ 4*bits.length+6 at hn
  change runSteps Load.step n (Turing.initList Load bits) = some finish at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Load.step machine.step loadEmbed loadTerminal load_stable load_step n (Turing.initList Load bits) finish rfl hr
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2WitnessOutput.loaded_run_raw_polynomial first witness query
  change b ≤ Shared.ComplexityBridge.TM2WitnessOutput.timePolynomial.eval size at hb
  change runSteps Output.step b start = some (Turing.haltList Output [answer]) at hbr
  have hinner : inner.length = 6*witness.length+1+3*query.length := Shared.ComplexityBridge.bitstring_pair_encoded_length witness query
  have hbits : bits.length = 6*first.length+1+3*inner.length := Shared.ComplexityBridge.bitstring_pair_encoded_length first inner
  have hsize : size ≤ bits.length := by dsimp [size]; omega
  have hp := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono Shared.ComplexityBridge.TM2WitnessOutput.timePolynomial hsize
  have hb' : b ≤ Shared.ComplexityBridge.TM2WitnessOutput.timePolynomial.eval bits.length := le_trans hb hp
  have hbRun := out_run start b
  rw [hbr] at hbRun
  refine ⟨1+a+1+b,?_,?_⟩
  · change 1+a+1+b ≤ timePolynomial.eval bits.length
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega
  · change runSteps machine.step (1+a+1+b) (Turing.initList machine bits) = _
    rw [show 1+a+1+b = 1+(a+(1+b)) by omega,runSteps_add]
    change (machine.step (Turing.initList machine bits)).bind _ = _
    rw [startup]
    change runSteps machine.step (a+(1+b)) (loadEmbed (Turing.initList Load bits)) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+b) (loadEmbed finish) = _
    rw [runSteps_add]
    change (machine.step (loadEmbed finish)).bind _ = _
    rw [dispatch]
    change runSteps machine.step b (outEmbed start) = _
    rw [hbRun]
    change some (outEmbed (Turing.haltList Output [answer])) = some (Turing.haltList machine [answer])
    rw [out_halt]



abbrev Triple := List Bool × (List Bool × List Bool)
def tripleInput (p : Triple) : List Bool := Shared.ComplexityBridge.TM2WitnessInput.inputBits p.1 p.2.1 p.2.2
def lookupTriple (p : Triple) : Bool := Shared.ComplexityBridge.TM2WitnessLookup.lookupRaw p.1 p.2.1 p.2.2

/-- A witness under the explicit nested serialization, for all triples. -/
noncomputable def tripleTimeMachine : Turing.TM2ComputableInPolyTime
    tripleInput (BitstringEncoding.bitEncode : Bool → List Bool) lookupTriple where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun p := by
    let t := Classical.choose (input_run_raw p.1 p.2.1 p.2.2)
    have ht := (Classical.choose_spec (input_run_raw p.1 p.2.1 p.2.2)).1
    have hr := (Classical.choose_spec (input_run_raw p.1 p.2.1 p.2.2)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine ((tripleInput p).map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (lookupTriple p)).map id))
      rw [List.map_id,List.map_id]
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine (tripleInput p))) =
        some (Turing.haltList machine [lookupTriple p])
      simpa [tripleInput,lookupTriple,t] using hr
    · simpa [tripleInput] using ht


namespace Fixtures
set_option maxRecDepth 4096 in
example : (runSteps machine.step 66 (Turing.initList machine
    (Shared.ComplexityBridge.TM2WitnessInput.inputBits [true] [true] []))).map
    (fun q => (q.l.isNone,q.stk .query)) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .query)) (runSteps machine.step 66
    (Turing.initList machine (Shared.ComplexityBridge.TM2WitnessInput.inputBits [true] [true] []))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2WitnessComplete
