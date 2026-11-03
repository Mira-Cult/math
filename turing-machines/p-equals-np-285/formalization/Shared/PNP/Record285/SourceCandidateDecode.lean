import Shared.PNP.Record285.SourceVirtualStep

/-! Candidate program selection and the relocated unary decoder. The
candidate uses deterministic choice zero, independent of the retained choice
register. The subsequent action, HALT toggle and full evaluator are in
`SourceCandidateStep`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceCandidateDecode
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceUnarySkip

def candidateProgramBank (bank : Nat → Nat) : Nat → Nat :=
  copyRaw 11 17 4 1 (update (.dec 20) bank)

def candidateProgramTime (bank : Nat → Nat) : Nat :=
  1 + copyTime 11 17 4 1 (update (.dec 20) bank)

/-- For every bank, positive candidate clock enters the actual compiled
program-copy block and finishes it silently with its exact raw bank effect. -/
theorem candidate_program_raw (bank : Nat → Nat) (hp : 0 < bank 20) :
    Silent originalRows ⟨119,bank⟩ ⟨128,candidateProgramBank bank⟩ (candidateProgramTime bank) := by
  let first := update (.dec 20) bank
  have hn : bank 20 ≠ 0 := by omega
  have h119 : step originalRows ⟨119,bank⟩ = (⟨120,first⟩,false) := by
    simp [step,originalRows,observe,hn,first]
  have h120 : originalRows[120]? = some ⟨.dec 11,121,123⟩ := by decide
  have h121 : originalRows[121]? = some ⟨.inc 17,122,122⟩ := by decide
  have h122 : originalRows[122]? = some ⟨.inc 4,120,120⟩ := by decide
  have h123 : originalRows[123]? = some ⟨.dec 4,124,125⟩ := by decide
  have h124 : originalRows[124]? = some ⟨.inc 11,123,123⟩ := by decide
  have h125 : originalRows[125]? = some ⟨.dec 1,125,126⟩ := by decide
  have h126 : originalRows[126]? = some ⟨.dec 17,127,128⟩ := by decide
  have h127 : originalRows[127]? = some ⟨.inc 1,126,126⟩ := by decide
  have hc := copy_block originalRows 120 121 122 123 124 125 126 127 128 11 17 4 1 first
    h120 h121 h122 h123 h124 h125 h126 h127
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact silent_trans originalRows _ _ _ 1 _ (silent_one _ _ _ h119) hc

/-- The two scratch slots are the only preconditions needed for the copy to
read the unmodified candidate program and retain every other register. -/
theorem candidate_program_clean (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    candidateProgramBank bank = (fun j => if j = 1 then bank 11 else if j = 20 then bank 20-1 else bank j) := by
  have h4' : update (.dec 20) bank 4 = 0 := by simp [update,h4]
  have h17' : update (.dec 20) bank 17 = 0 := by simp [update,h17]
  rw [candidateProgramBank,copyRaw_clean 11 17 4 1 _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h17' h4']
  funext j
  by_cases h1 : j = 1
  · subst j; simp [update]
  · by_cases h20 : j = 20
    · subst j; simp [update]
    · simp [update,h1,h20]

/-- The relocated candidate selector loop uses the same generic proof as the
reference decoder. -/
theorem candidate_skip (bank : Nat → Nat) :
    Silent originalRows ⟨128,bank⟩ ⟨130,afterSkip bank⟩ (skipTime (bank 3) (bank 1)) :=
  skip_loop_generic originalRows 128 129 130 (by decide) (by decide) (bank 3) (bank 1) bank rfl rfl

/-- The relocated candidate record counter also uses the generic proof. -/
theorem candidate_record (bank : Nat → Nat) :
    Silent originalRows ⟨130,bank⟩ ⟨133,recordBank bank⟩ (recordTime bank) :=
  record_decode_generic originalRows 130 131 132 133 (by decide) (by decide) (by decide) bank

def candidateDecodedBank (bank : Nat → Nat) : Nat → Nat :=
  recordBank (afterSkip (candidateProgramBank bank))

def candidateDecodeTime (bank : Nat → Nat) : Nat :=
  candidateProgramTime bank +
    skipTime ((candidateProgramBank bank) 3) ((candidateProgramBank bank) 1) +
    recordTime (afterSkip (candidateProgramBank bank))

/-- Full positive-clock candidate decoding for arbitrary banks, with exact
finite duration, complete resulting bank and no event. -/
theorem candidate_decode_raw (bank : Nat → Nat) (hp : 0 < bank 20) :
    Silent originalRows ⟨119,bank⟩ ⟨133,candidateDecodedBank bank⟩ (candidateDecodeTime bank) := by
  have hp1 := candidate_program_raw bank hp
  have hp2 := candidate_skip (candidateProgramBank bank)
  have hp3 := candidate_record (afterSkip (candidateProgramBank bank))
  have h := silent_trans originalRows _ _ _ _ _ hp1 hp2
  exact silent_trans originalRows _ _ _ _ _ h hp3

/-- Candidate choice is zero. Under clean scratch, the selected unary record
and untouched frame agree with that deterministic source input. -/
theorem candidate_decode_source (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    let stream := Source.skipUnary (bank 3) (bank 11)
    candidateDecodedBank bank 3 = (Source.popUnary stream).1 ∧
    candidateDecodedBank bank 1 = (Source.popUnary stream).2 ∧
    candidateDecodedBank bank 20 = bank 20-1 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → j ≠ 20 → candidateDecodedBank bank j = bank j) := by
  let prog := candidateProgramBank bank
  have hp := candidate_program_clean bank h4 h17
  have hp1 : prog 1 = bank 11 := by simp [prog,hp]
  have hp3 : prog 3 = bank 3 := by simp [prog,hp]
  have hp20 : prog 20 = bank 20-1 := by simp [prog,hp]
  have hpf : ∀ j, j ≠ 1 → j ≠ 20 → prog j = bank j := by
    intro j h1 h20
    simp [prog,hp,h1,h20]
  have hs := afterSkip_read prog
  have hr := recordBank_read (afterSkip prog)
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · change recordBank (afterSkip prog) 3 = _
    rw [hr.1,hs.1,hp3,hp1]
  · change recordBank (afterSkip prog) 1 = _
    rw [hr.2.1,hs.1,hp3,hp1]
  · change recordBank (afterSkip prog) 20 = _
    rw [hr.2.2 20 (by decide) (by decide),hs.2.2 20 (by decide) (by decide),hp20]
  · intro j h1 h3 h20
    change recordBank (afterSkip prog) j = bank j
    rw [hr.2.2 j h1 h3,hs.2.2 j h1 h3]
    exact hpf j h1 h20

/-- Every reachable positive-clock candidate decode transfers to the exact
pre-control grammar with positive bounded progress and no event. -/
theorem candidate_decode_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨119,bank⟩) (hp : 0 < bank 20) :
    let d := candidateDecodeTime bank
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))
    r.boundary t < r.boundary (t+d) ∧ r.boundary (t+d) ≤ r.boundary t + 32*d ∧
    PreControlGrammar.positions[133]? = some g.pc ∧ g.bank = candidateDecodedBank bank ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+d) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have hd : 0 < candidateDecodeTime bank := by
    unfold candidateDecodeTime candidateProgramTime
    omega
  exact transfer_silent_graph t _ 119 133 bank _ hstate hd (candidate_decode_raw bank hp)

end Shared.PNP.Record285.SourceCandidateDecode
