import Shared.ComplexityBridge.CNFComputability
/-! Conditional raw-input computability corollaries. The premise is a
separate computability proof for the pinned Google decoder; no time bound,
TM2 simulation, or finite-machine implementation follows from these lemmas. -/
namespace Shared.ComplexityBridge.CNF

theorem sat_computable_of_parse (hp : Computable parse) : Computable sat := by
  unfold sat
  refine (Computable.option_casesOn hp (Computable.const false)
    (satFormula_computable.comp Computable.snd).to₂).of_eq ?_
  intro a
  cases parse a <;> rfl

theorem validUnsat_computable_of_parse (hp : Computable parse) : Computable validUnsat := by
  unfold validUnsat
  refine (Computable.option_casesOn hp (Computable.const false)
    (Primrec.not.to_comp.comp (satFormula_computable.comp Computable.snd)).to₂).of_eq ?_
  intro a
  cases parse a <;> rfl

theorem complementSat_computable_of_parse (hp : Computable parse) : Computable complementSat := by
  exact Primrec.not.to_comp.comp (sat_computable_of_parse hp)

theorem satAtIndex_computable_of_parse (hp : Computable parse) : Computable satAtIndex := by
  exact (sat_computable_of_parse hp).comp Shared.Codes.Inputs.computable

end Shared.ComplexityBridge.CNF
