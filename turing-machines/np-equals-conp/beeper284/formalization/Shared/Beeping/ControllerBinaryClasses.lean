import Shared.Beeping.ControllerBinary
import Shared.ComplexityBridge.TM2PreparedVerify
import Shared.ComplexityBridge.TM2CutoffCompose
import Shared.ComplexityBridge.TM2PairMap
import Shared.ComplexityBridge.BoundedHardness

/-! Connect the binary controllers to the proved canonical candidate
characterizations. SAT hardness remains an explicit hypothesis for the two
separate class-equality conclusions. -/
namespace Shared.Beeping.ControllerBinaryClasses
open Turing.ToPartrec
open Shared.Beeping.ControllerBinary
open Shared.ComplexityBridge

theorem pnp_iff_sat_in_P (c : Code)
    (hc : Shared.Beeping.ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c) :
    (machine c).system.EventuallySilent ↔ CNF.sat ∈ ComplexityTheory.P :=
  (ControllerBinary.pnp c hc).trans (TM2Whole.candidate_iff_P CNF.sat)

theorem npconp_iff_complement_in_NP (c : Code)
    (hc : Shared.Beeping.ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c) :
    (machine c).system.EventuallySilent ↔ CNF.complementSat ∈ ComplexityTheory.NP :=
  (ControllerBinary.npconp c hc).trans TM2CutoffCompose.good_verifier_iff_complement_in_NP

/-- The actual canonical P/NP endpoint follows from the one remaining SAT
hardness premise, with a separately supplied correct comparison code. -/
theorem pnp_of_sat_hard (c : Code)
    (hc : Shared.Beeping.ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c)
    (hhard : CNFWitness.SatHard) :
    (machine c).system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  let complete := TM2PreparedVerify.complete_of_sat_hard hhard
  exact (pnp_iff_sat_in_P c hc).trans
    (CanonicalClasses.p_eq_np_iff_complete_in_p complete TM2IgnoreWitness.P_subset_NP
      TM2Compose.p_pullback_closed).symm

/-- The NP/coNP endpoint uses its own comparison code and binary machine. -/
theorem npconp_of_sat_hard (c : Code)
    (hc : Shared.Beeping.ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c)
    (hhard : CNFWitness.SatHard) :
    (machine c).system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP := by
  let complete := TM2PreparedVerify.complete_of_sat_hard hhard
  apply (npconp_iff_complement_in_NP c hc).trans
  rw [CanonicalClasses.totalComplement_eq]
  exact (CanonicalClasses.np_eq_conp_iff_complement_complete_in_np complete TM2PairMap.np_pullback_closed).symm

theorem pnp_exists_iff_sat_in_P : ∃ c : Code,
    (machine c).system.EventuallySilent ↔ CNF.sat ∈ ComplexityTheory.P := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.PNP.TM2Candidate.compareSAT Shared.PNP.TM2Candidate.compareSAT_computable
  exact ⟨c,pnp_iff_sat_in_P c hc⟩

theorem npconp_exists_iff_complement_in_NP : ∃ c : Code,
    (machine c).system.EventuallySilent ↔ CNF.complementSat ∈ ComplexityTheory.NP := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.NPCONP.TM2Verifier.compare Shared.NPCONP.TM2Verifier.compare_computable
  exact ⟨c,npconp_iff_complement_in_NP c hc⟩

theorem pnp_exists_of_sat_hard (hhard : CNFWitness.SatHard) : ∃ c : Code,
    (machine c).system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.PNP.TM2Candidate.compareSAT Shared.PNP.TM2Candidate.compareSAT_computable
  exact ⟨c,pnp_of_sat_hard c hc hhard⟩

theorem npconp_exists_of_sat_hard (hhard : CNFWitness.SatHard) : ∃ c : Code,
    (machine c).system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.NPCONP.TM2Verifier.compare Shared.NPCONP.TM2Verifier.compare_computable
  exact ⟨c,npconp_of_sat_hard c hc hhard⟩

/-- SAT membership is already proved, so the forward implications require
neither the SAT hardness premise nor a model-simulation hypothesis. -/
theorem pnp_equality_forward (c : Code)
    (hc : Shared.Beeping.ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c)
    (heq : ComplexityTheory.P = ComplexityTheory.NP) : (machine c).system.EventuallySilent :=
  ControllerBinary.pnp_equality_forward c hc TM2PreparedVerify.sat_in_NP heq

theorem npconp_equality_forward (c : Code)
    (hc : Shared.Beeping.ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c)
    (heq : ComplexityTheory.NP = ComplexityTheory.coNP) : (machine c).system.EventuallySilent :=
  ControllerBinary.npconp_equality_forward c hc TM2PreparedVerify.sat_in_NP heq

/-- Two more concrete, still unproved obligations suffice for SAT hardness:
the validated numeric-pair to finite-program adapter and polynomial-time
execution of the actual CNF generator. -/
theorem pnp_exists_of_numeric_and_generator
    (hadapter : BoundedHardness.NumericPairCompiler)
    (hgenerator : BoundedHardness.GeneratorPolyTime) : ∃ c : Code,
    (machine c).system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  pnp_exists_of_sat_hard (BoundedHardness.satHard_of_compiler_and_generator
    (BoundedHardness.finiteVerifierCompiler_of_numeric hadapter) hgenerator)

theorem npconp_exists_of_numeric_and_generator
    (hadapter : BoundedHardness.NumericPairCompiler)
    (hgenerator : BoundedHardness.GeneratorPolyTime) : ∃ c : Code,
    (machine c).system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  npconp_exists_of_sat_hard (BoundedHardness.satHard_of_compiler_and_generator
    (BoundedHardness.finiteVerifierCompiler_of_numeric hadapter) hgenerator)

end Shared.Beeping.ControllerBinaryClasses
