import Shared.Beeping.ControllerTM2Refinement

/-! Separate looping TM2 controllers for the two concrete candidate
comparisons. These are not binary transition tables or class equalities. -/
namespace Shared.Beeping.ControllerTM2Candidates
open Turing.ToPartrec
open Shared.Beeping.ControllerTM2Loop Shared.Beeping.ControllerTM2Refinement

theorem pnp : ∃ c : Code,
    (∀ t, ((system c).run t).l ≠ none) ∧
    ((system c).EventuallySilent ↔
      ∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
        Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
          some (Shared.ComplexityBridge.CNF.sat x)) := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.PNP.TM2Candidate.compareSAT Shared.PNP.TM2Candidate.compareSAT_computable
  refine ⟨c,run_never_halts c, ?_⟩
  exact ((simulation Shared.PNP.TM2Candidate.compareSAT c hc).toEventRefinement.eventuallySilent_iff).symm.trans
    Shared.PNP.TM2Candidate.controller_silent_iff

theorem npconp : ∃ c : Code,
    (∀ t, ((system c).run t).l ≠ none) ∧
    ((system c).EventuallySilent ↔
      ∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
        Shared.NPCONP.TM2Verifier.test verifier x = true) := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.NPCONP.TM2Verifier.compare Shared.NPCONP.TM2Verifier.compare_computable
  refine ⟨c,run_never_halts c, ?_⟩
  exact ((simulation Shared.NPCONP.TM2Verifier.compare c hc).toEventRefinement.eventuallySilent_iff).symm.trans
    Shared.NPCONP.TM2Verifier.controller_silent_iff

end Shared.Beeping.ControllerTM2Candidates
