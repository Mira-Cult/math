import Shared.Beeping.NPcoNP.Source284ReferenceHard
import Shared.Beeping.NPcoNP.Source284RawWitnessComputable

/-! The exact raw-bitstring source reference instantiates the shared
complete-language contract. This is a source result, not a physical-machine
refinement or a proof of candidate coverage. -/
namespace Shared.Beeping.NPcoNP.Source284ReferenceComplete

open ComplexityTheory
open Shared.ComplexityBridge.CanonicalClasses
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- The bounded reference evaluation is primitive recursive on every raw
bitstring, including empty and noncanonical numeral encodings. This is an
executable computability proof and asserts no polynomial running time. -/
theorem referenceLanguage_primrec : Primrec referenceLanguage := by
  let value := Shared.Codes.BitNumeralCompare.value
  have hv : Primrec value := Source284RawWitness.value_primrec
  have hn : Primrec (fun xs : List Bool => Source284Parser.length (value xs)) :=
    Source284Parser.length_primrec.comp hv
  have hd : Primrec (fun xs : List Bool => Source284Parser.description (value xs)) :=
    Source284Parser.description_primrec.comp hv
  have ha : Primrec (fun xs : List Bool =>
      (((Source284Parser.description (value xs),0),Source284Parser.length (value xs)),
        Source284Parser.description (value xs))) :=
    Primrec.pair (Primrec.pair (Primrec.pair hd (Primrec.const 0)) hn) hd
  exact Source284Relative.boundedAcceptance_primrec.comp ha

/-- The exact source reference meets the shared canonical NP-completeness
contract, including an independently executable total reference evaluator. -/
noncomputable def complete : CompleteLanguage referenceLanguage where
  reference := referenceLanguage
  reference_correct := fun _ => rfl
  reference_computable := referenceLanguage_primrec.to_comp
  member := Source284ReferenceNP.reference_mem_NP
  hard := Source284ReferenceHard.np_hard

end Shared.Beeping.NPcoNP.Source284ReferenceComplete
