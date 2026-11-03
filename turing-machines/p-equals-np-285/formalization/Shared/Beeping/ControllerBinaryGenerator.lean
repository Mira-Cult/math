import Shared.Beeping.ControllerBinaryClasses
import Shared.ComplexityBridge.FiniteVerifierCompiler

/-! The previously constructed progress-sensitive binary controllers need
only the CNF reduction generator runtime theorem for class-equality endpoints.
The existence proofs do not bind a literal serialized transition table. -/
namespace Shared.Beeping.ControllerBinaryGenerator

open Turing.ToPartrec
open Shared.Beeping.ControllerBinary
open Shared.ComplexityBridge

/-- A separately chosen binary controller for P = NP. -/
theorem pnp_exists_of_generator (hgenerator : BoundedHardness.GeneratorPolyTime) :
    ∃ c : Code, (machine c).system.EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  ControllerBinaryClasses.pnp_exists_of_sat_hard
    (FiniteVerifierCompiler.sat_hard_of_generator hgenerator)

/-- A separately chosen binary controller for NP = coNP. -/
theorem npconp_exists_of_generator (hgenerator : BoundedHardness.GeneratorPolyTime) :
    ∃ c : Code, (machine c).system.EventuallySilent ↔
      ComplexityTheory.NP = ComplexityTheory.coNP :=
  ControllerBinaryClasses.npconp_exists_of_sat_hard
    (FiniteVerifierCompiler.sat_hard_of_generator hgenerator)

end Shared.Beeping.ControllerBinaryGenerator
