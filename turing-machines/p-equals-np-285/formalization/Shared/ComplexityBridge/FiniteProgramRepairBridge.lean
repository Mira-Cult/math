import Shared.Codes.FiniteProgramRepair
import Shared.ComplexityBridge.BoundedHardness

/-! The hypothetical canonical-model adapters can be required to emit valid
finite tables without adding a new assumption or changing their clocks. The
adapters themselves remain unproved. -/
namespace Shared.ComplexityBridge.FiniteProgramRepairBridge

open ComplexityTheory
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramRepair
open Shared.ComplexityBridge.BoundedHardness

def ValidFiniteVerifierCompiler : Prop :=
  ∀ R : (List Bool × List Bool) → Bool, IsPolyTime R →
    ∃ (program : Program) (time : Polynomial Nat), valid program = true ∧ ∀ x w,
      bounded program (BitstringEncoding.bitEncode (x,w))
        (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (R (x,w))

theorem finiteVerifierCompiler_iff_valid : FiniteVerifierCompiler ↔ ValidFiniteVerifierCompiler := by
  constructor
  · intro hc R hR
    obtain ⟨program,time,hprogram⟩ := hc R hR
    refine ⟨repair program,time,repair_valid program,?_⟩
    intro x w
    rw [bounded_repair,hprogram]
  · intro hc R hR
    obtain ⟨program,time,_,hprogram⟩ := hc R hR
    exact ⟨program,time,hprogram⟩

def ValidNumericPairCompiler : Prop :=
  ∀ c : Shared.Codes.TM2Candidate.Candidate,
    Shared.Codes.TM2CheckedCandidate.candidateValid c = true →
    ∃ (program : Program) (time : Polynomial Nat), valid program = true ∧ ∀ x w,
      bounded program (BitstringEncoding.bitEncode (x,w))
        (time.eval (BitstringEncoding.bitEncode (x,w)).length) =
      Shared.Codes.TM2PairCandidate.evaluate c x w

theorem numericPairCompiler_iff_valid : NumericPairCompiler ↔ ValidNumericPairCompiler := by
  constructor
  · intro hc c hvalid
    obtain ⟨program,time,hprogram⟩ := hc c hvalid
    refine ⟨repair program,time,repair_valid program,?_⟩
    intro x w
    rw [bounded_repair,hprogram]
  · intro hc c hvalid
    obtain ⟨program,time,_,hprogram⟩ := hc c hvalid
    exact ⟨program,time,hprogram⟩

end Shared.ComplexityBridge.FiniteProgramRepairBridge
