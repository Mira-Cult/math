import PASoundness.Integration
import PASoundness.CompactSemantics
import PASoundness.CompactArithmetic

/-!
# Closed behavior of the pinned compact source

The local record/failure equivalence below is structural and does not use K or
PA soundness. The acceptance corollary then applies the independently proved
standard bit-model soundness of the actual K calculus. This closes the source
acceptance statement without claiming the missing syntactic K/PA transports
or an implementation certificate for PA926.
-/

namespace PASoundness.CompactAcceptance
open Observer Integration CompactProof

/-- Exact finite-rank meaning of the actual emitted relation. Invalid syntax
does not become a witness. The statement covers arbitrary finite certificates. -/
theorem rank_failure_iff (n : Nat) :
    RankFailure (Source.recordValues value) n ↔
      ∃ p, CompactMatrix.valid theoremCode n p ∧ ¬ compactTruth (theoremCode p) := by
  unfold RankFailure
  apply exists_congr
  intro p
  calc
    altPrefix .all n (fun xs => Source.recordValues value n p xs = true) ↔
        altPrefix .all n (fun xs => CompactMatrix.valid theoremCode n p ∧
          ¬ CompactMatrix.matrixTruth theoremCode n p xs) := by
      apply altPrefix_congr_length
      intro xs hlen
      exact CompactMatrix.record_spec theoremCode n p xs hlen
    _ ↔ CompactMatrix.valid theoremCode n p ∧
        altPrefix .all n (fun xs => ¬ CompactMatrix.matrixTruth theoremCode n p xs) :=
      altPrefix_and_constant .all n _ _
    _ ↔ CompactMatrix.valid theoremCode n p ∧
        ¬ altPrefix .ex n (CompactMatrix.matrixTruth theoremCode n p) :=
      and_congr Iff.rfl (altPrefix_duality .all n _)
    _ ↔ CompactMatrix.valid theoremCode n p ∧ ¬ compactTruth (theoremCode p) := by
      apply and_congr_right
      intro hv
      exact not_congr (normalized_prefix n p hv).symm

/-- Every positive finite observer condition is exactly a false, recognized
K conclusion at that rank, including the proved completeness/address guards. -/
theorem source_level_iff (n : Nat) (hn : 0 < n) :
    Q_n events n ↔
      ∃ p, CompactMatrix.valid theoremCode n p ∧ ¬ compactTruth (theoremCode p) := by
  change (0 < n ∧ Complete events ∧ RawFailure events n) ↔ _
  rw [and_iff_right hn, and_iff_right source_complete,
    rawFailure_iff_rankFailure events (Source.recordValues value)
      (Source.recordsAgree value) n hn, rank_failure_iff]

/-- This direction is established before any standard-model soundness is used.
An observed finite failure always has a genuine finite K derivation whose
conclusion is false in the standard bit model. -/
theorem source_failure_origin : Q_omega .compactSuffix events →
    ∃ f, KProves f ∧ ¬ compactTruth f := by
  rintro (hz | ⟨n, hn, hc, hb⟩)
  · refine ⟨1, source_levelZero_iff_KBottom.mp hz, ?_⟩
    exact CompactSemantics.realize_one (fun _ => 0)
  · obtain ⟨p, _, hp⟩ := (source_level_iff n hn).mp ⟨hn,hc,hb⟩
    exact ⟨theoremCode p, theorem_origin p, hp⟩

/-- The same observed witness has an explicit standard-false genuine arithmetic
sentence. This does not yet assert PA provability of that translated sentence. -/
theorem source_failure_arithmetic_witness : Q_omega .compactSuffix events →
    ∃ f, KProves f ∧ ¬ (Nat ⊨ CompactArithmetic.toPA f) := by
  intro h
  obtain ⟨f,hp,hf⟩ := source_failure_origin h
  exact ⟨f,hp,fun ht => hf ((CompactArithmetic.truth_toPA f).mp ht)⟩

/-- Independent standard-model consequence of the exact nine K schemas. -/
theorem source_no_failure : ¬ Q_omega .compactSuffix events := by
  intro h
  obtain ⟨f,hp,hf⟩ := source_failure_origin h
  exact hf (CompactSemantics.proves_sound hp (fun _ => 0))

/-- Closed acceptance of the recovered compact source. No PA interpretation,
prenex-coverage interface, or physical table behavior is a premise. -/
theorem source_acceptance : SoundnessAcceptance .compactSuffix events :=
  (acceptance_complement_on_complete .compactSuffix events).mpr
    ⟨source_complete,source_no_failure⟩

theorem source_formula_acceptance : FormulaAcceptance .compactSuffix events :=
  (formulaAcceptance_iff .compactSuffix events).mpr source_acceptance

theorem source_no_zero : ¬ Q_0 .compactSuffix events :=
  fun h => source_no_failure (Or.inl h)

theorem source_no_positive (n : Nat) : ¬ Q_n events n :=
  fun h => source_no_failure (Or.inr ⟨n,h⟩)

/-- Only the local physical refinement remains in this direct K-model result.
It is not a closed theorem about the selected PA926 table. -/
theorem machine_acceptance {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : ImplementationCertificate source M) :
    SoundnessAcceptance .compactSuffix (UniformMachine.events cert) :=
  (UnaryCodec.implementation_observer_preserved cert .compactSuffix).mp source_acceptance

theorem machine_no_failure {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : ImplementationCertificate source M) :
    ¬ Q_omega .compactSuffix (UniformMachine.events cert) :=
  ((acceptance_complement_on_complete .compactSuffix (UniformMachine.events cert)).mp
    (machine_acceptance cert)).2

end PASoundness.CompactAcceptance
