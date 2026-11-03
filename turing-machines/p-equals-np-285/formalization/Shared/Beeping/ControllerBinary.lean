import Shared.Beeping.MarkedTM1Support
import Shared.Beeping.PostFiniteSupport
import Shared.Beeping.PostInputRefinement

/-! Conditional-on-comparison-code binary controller construction. Classical
finite-support numbering proves existence of the literal finite table, but
is not an effective algorithm to reify the function-valued TM1 statements. -/
namespace Shared.Beeping.ControllerBinary
open Turing Turing.PartrecToTM2 Turing.ToPartrec
open Shared.Beeping.ControllerTM1Progress Shared.Beeping.MarkedTM1Post
open Shared.Beeping.PostFiniteSupport Shared.Beeping.PostTableGenerator
open Shared.Beeping.PostTableBinding Shared.Beeping.PostInputLoader
open Shared.Beeping.BinarySourceCompiler

noncomputable def states (c : Code) : Finset Phase :=
  MarkedTM1Support.support (program1 c) (support1 c)

theorem states_correct (c : Code) :
    TM0.Supports (table (program1 c)) (states c : Set Phase) :=
  MarkedTM1Support.table_support (program1 c) (support1 c) (support1_correct c)

theorem rows_total (c : Code) (q : Phase) (a : A) :
    ∃ dst op, table (program1 c) q a = some (dst,op) := by
  cases q <;> exact ⟨_,_,rfl⟩

noncomputable def numbering (c : Code) : FiniteIndex (table (program1 c)) (states c).card := by
  classical
  exact PostFiniteSupport.numbering (table (program1 c)) (states c) (states_correct c)
    (fun q _ a => rows_total c q a)

noncomputable def start (c : Code) : Fin (states c).card := by
  classical
  exact PostFiniteSupport.start (states c) default (states_correct c).1

theorem start_correct (c : Code) : (numbering c).state (start c) = default := by
  classical
  exact PostFiniteSupport.start_state _ _ _ _ _ _

noncomputable def sourceTable (c : Code) : SourceTable (states c).card :=
  generate (table (program1 c)) (flags flag1) (numbering c)

/-- The binary initial tape is blank. The fixed loader writes the one-symbol
TM1 stack-bottom marker, encoded as 13 bits. -/
noncomputable def machine (c : Code) :=
  Shared.Beeping.BinaryLoader.machine (BinarySourceCompiler.machine (sourceTable c) (start c))
    (payload (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main []))

theorem blank (c : Code) : (machine c).blank = false := rfl
theorem start_head (c : Code) : (machine c).startHead = 0 := rfl

/-- The loader for the one-symbol TM1 input uses exactly 26 silent
transitions and 26 states. -/
theorem loader_count :
    2 * Shared.Beeping.BinaryLoader.count false
      (payload (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main [])) = 26 := by
  rw [Shared.Beeping.BinaryLoader.count_eq_max,payload_length,initial_input]
  decide

theorem state_count (c : Code) :
    Shared.Beeping.BinaryLoader.total (BinarySourceCompiler.machine (sourceTable c) (start c))
      (payload (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main [])) =
        26 + (states c).card * 147483 := by
  change 2 * Shared.Beeping.BinaryLoader.count false
    (payload (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main [])) +
      (states c).card * 147483 = _
  rw [loader_count]

noncomputable def refinement (c : Code) :
    EventRefinement (system1 c) (machine c).system := by
  classical
  let binding := PostTableGenerator.binding (table (program1 c)) (flags flag1) (numbering c)
  have h := PostInputRefinement.refinement binding (start c)
    (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main [])
  change EventRefinement (externalSystem (table (program1 c)) (flags flag1)
    ⟨(numbering c).state (start c),Tape.mk₁ (TM2to1.trInit (Γ := fun _ : K' => Γ') K'.main [])⟩) _ at h
  rw [start_correct] at h
  have h' : EventRefinement (controllerPost c) (machine c).system := h
  exact (simulation (program1 c) flag1 initial1).toEventRefinement.trans h'

theorem pnp (c : Code) (hc : ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c) :
    (machine c).system.EventuallySilent ↔
      ∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
        Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
          some (Shared.ComplexityBridge.CNF.sat x) :=
  (refinement c).eventuallySilent_iff.symm.trans (ControllerTM1Interior.pnp c hc)

theorem npconp (c : Code) (hc : ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c) :
    (machine c).system.EventuallySilent ↔
      ∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
        Shared.NPCONP.TM2Verifier.test verifier x = true :=
  (refinement c).eventuallySilent_iff.symm.trans (ControllerTM1Interior.npconp c hc)

/-- The remaining canonical complexity bridge is explicit; no conjecture
negation or unproved class equality is assumed. -/
theorem pnp_equality_conditional (c : Code)
    (hc : ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c)
    (bridge : (∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
      Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
        some (Shared.ComplexityBridge.CNF.sat x)) ↔ ComplexityTheory.P = ComplexityTheory.NP) :
    (machine c).system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  (pnp c hc).trans bridge

theorem npconp_equality_conditional (c : Code)
    (hc : ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c)
    (bridge : (∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
      Shared.NPCONP.TM2Verifier.test verifier x = true) ↔ ComplexityTheory.NP = ComplexityTheory.coNP) :
    (machine c).system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  (npconp c hc).trans bridge

theorem pnp_endpoint_conditional
    (bridge : (∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
      Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
        some (Shared.ComplexityBridge.CNF.sat x)) ↔ ComplexityTheory.P = ComplexityTheory.NP) :
    ∃ c : Code, (machine c).system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.PNP.TM2Candidate.compareSAT Shared.PNP.TM2Candidate.compareSAT_computable
  exact ⟨c,pnp_equality_conditional c hc bridge⟩

theorem npconp_endpoint_conditional
    (bridge : (∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
      Shared.NPCONP.TM2Verifier.test verifier x = true) ↔ ComplexityTheory.NP = ComplexityTheory.coNP) :
    ∃ c : Code, (machine c).system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.NPCONP.TM2Verifier.compare Shared.NPCONP.TM2Verifier.compare_computable
  exact ⟨c,npconp_equality_conditional c hc bridge⟩

theorem pnp_exists : ∃ c : Code,
    (machine c).system.EventuallySilent ↔
      ∃ candidate : Shared.Codes.TM2Candidate.Candidate, ∀ x,
        Shared.Codes.TM2CheckedCandidate.evaluate candidate x =
          some (Shared.ComplexityBridge.CNF.sat x) := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.PNP.TM2Candidate.compareSAT Shared.PNP.TM2Candidate.compareSAT_computable
  exact ⟨c,pnp c hc⟩

theorem npconp_exists : ∃ c : Code,
    (machine c).system.EventuallySilent ↔
      ∃ verifier : Shared.NPCONP.TM2Verifier.Verifier, ∀ x,
        Shared.NPCONP.TM2Verifier.test verifier x = true := by
  obtain ⟨c,hc⟩ := Shared.Beeping.ControllerCode.has_update_code
    Shared.NPCONP.TM2Verifier.compare Shared.NPCONP.TM2Verifier.compare_computable
  exact ⟨c,npconp c hc⟩

theorem pnp_equality_forward (c : Code)
    (hc : ControllerTM2Refinement.CodeCorrect Shared.PNP.TM2Candidate.compareSAT c)
    (hsat : Shared.ComplexityBridge.CNF.sat ∈ ComplexityTheory.NP)
    (heq : ComplexityTheory.P = ComplexityTheory.NP) :
    (machine c).system.EventuallySilent :=
  (pnp c hc).2 (Shared.PNP.TM2Candidate.controller_silent_iff.1
    (Shared.PNP.TM2Candidate.equality_implies_silence hsat heq))

theorem npconp_equality_forward (c : Code)
    (hc : ControllerTM2Refinement.CodeCorrect Shared.NPCONP.TM2Verifier.compare c)
    (hsat : Shared.ComplexityBridge.CNF.sat ∈ ComplexityTheory.NP)
    (heq : ComplexityTheory.NP = ComplexityTheory.coNP) :
    (machine c).system.EventuallySilent :=
  (npconp c hc).2 (Shared.NPCONP.TM2Verifier.controller_silent_iff.1
    (Shared.NPCONP.TM2Verifier.equality_implies_silence hsat heq))

end Shared.Beeping.ControllerBinary
