import PASoundness.Observer

/-!
Composition of the finite observer syntax with the generic producer theorem.
The record equation, normalization, and optional finite-level translations
remain explicit client obligations.  In particular this is not a proof about
the 926-state transition table or a proof of the PA238/HF interpretation.
-/

namespace PASoundness.Observer

def ZeroReceipt (view : ZeroView) (E : EventStructure) (p : Nat) : Prop :=
  match view with
  | .rankZero => Emitted E true ⟨0, p, []⟩
  | .compactSuffix => Marker.bottomTail p = true ∧ Emitted E true ⟨1, p, [0]⟩

theorem rawZero_iff (view : ZeroView) (E : EventStructure) :
    RawZero view E ↔ ∃ p, ZeroReceipt view E p := by
  cases view <;> rfl

/-- A source relation, not an observer operation.  In the compact view it
requires the existing producer's proof computation to validate the marker. -/
def ZeroEmittedRelation {T : TheoryPresentation} (B : BottomCertificates T)
    (view : ZeroView) (E : EventStructure) : Prop :=
  ∀ p, ZeroReceipt view E p ↔ B.valid p

theorem rawZero_exact {T : TheoryPresentation} (B : BottomCertificates T)
    (view : ZeroView) (E : EventStructure) (records : ZeroEmittedRelation B view E) :
    RawZero view E ↔ B.ProvesBottom := by
  rw [rawZero_iff]
  exact (exists_congr records).trans B.exact

/-- For a concrete logical-false conclusion, this is the intended inconsistency
detector.  No implication from arbitrary quantifier-free falsity is used. -/
theorem levelZero_exact {T : TheoryPresentation} (B : BottomCertificates T)
    (view : ZeroView) (E : EventStructure) (records : ZeroEmittedRelation B view E)
    (hc : Complete E) : Q_0 view E ↔ B.ProvesBottom := by
  unfold Q_0
  rw [rawZero_exact B view E records]
  exact and_iff_right hc

/-- All finite formulas are actual syntax; their countable aggregation is external. -/
def FormulaAcceptance (view : ZeroView) (E : EventStructure) : Prop :=
  completeFormula.Realize E {} ∧
  ¬ (rawZeroFormula view).Realize E {} ∧
  ∀ n, 0 < n → ¬ (rawLevelFormula n).Realize E {}

theorem formulaAcceptance_iff (view : ZeroView) (E : EventStructure) :
    FormulaAcceptance view E ↔ SoundnessAcceptance view E := by
  apply and_congr (completeFormula_realize E {})
  apply and_congr (not_congr (rawZeroFormula_realize view E {}))
  apply forall_congr'
  intro n
  exact imp_congr_right (fun _ => not_congr (rawLevelFormula_realize E n {}))

/-- Reusable all-rank theorem with a separate designated-contradiction bridge. -/
theorem observer_soundness_reduction {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (values : RecordValues) (records : EmittedRelation N values)
    (view : ZeroView) (E : EventStructure) (agreement : RecordsAgree E values)
    (zeroRecords : ZeroEmittedRelation B view E) (hc : Complete E) :
    SoundnessAcceptance view E ↔ T.Sound := by
  constructor
  · rintro ⟨_, _, hpositive⟩
    apply (full_soundness_reduction N values records (Complete E) hc).mp
    refine ⟨hc, ?_⟩
    intro n hn hbad
    exact hpositive n hn ((rawFailure_iff_rankFailure E values agreement n hn).mpr hbad)
  · intro hs
    refine ⟨hc, ?_, ?_⟩
    · intro hz
      exact B.unsound ((rawZero_exact B view E zeroRecords).mp hz) hs
    · intro n hn hb
      have ha := (full_soundness_reduction N values records (Complete E) hc).mpr hs
      exact ha.2 n hn ((rawFailure_iff_rankFailure E values agreement n hn).mp hb)

/-- This endpoint states the reduction in terms of realization of generated
finite FO sentences, not just arbitrary logical functions in Lean. -/
theorem formula_soundness_reduction {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (values : RecordValues) (records : EmittedRelation N values)
    (view : ZeroView) (E : EventStructure) (agreement : RecordsAgree E values)
    (zeroRecords : ZeroEmittedRelation B view E) (hc : Complete E) :
    FormulaAcceptance view E ↔ T.Sound :=
  (formulaAcceptance_iff view E).trans
    (observer_soundness_reduction N B values records view E agreement zeroRecords hc)

theorem observer_omega_iff_unsound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (values : RecordValues) (records : EmittedRelation N values)
    (view : ZeroView) (E : EventStructure) (agreement : RecordsAgree E values)
    (zeroRecords : ZeroEmittedRelation B view E) (hc : Complete E) :
    Q_omega view E ↔ ¬ T.Sound := by
  constructor
  · rintro (hz | ⟨n, hn, _, hb⟩)
    · exact B.unsound ((levelZero_exact B view E zeroRecords hc).mp hz)
    · apply (rankOmega_iff_unsound N values records).mp
      exact ⟨n, hn, (rawFailure_iff_rankFailure E values agreement n hn).mp hb⟩
  · intro hs
    obtain ⟨n, hn, hb⟩ := (rankOmega_iff_unsound N values records).mpr hs
    exact Or.inr ⟨n, hn, hc, (rawFailure_iff_rankFailure E values agreement n hn).mpr hb⟩

/-- Exact positive calibration is conditional on the named rank-preserving
syntactic origin/coverage bridge, independently of the all-rank theorem. -/
theorem positive_level_calibration {T : TheoryPresentation}
    (N : NormalizationCertificate T) (values : RecordValues)
    (records : EmittedRelation N values) (E : EventStructure)
    (agreement : RecordsAgree E values) (hc : Complete E)
    (level : Nat → T.Sentence → Prop) (bridge : FiniteLevelBridge T N level)
    (n : Nat) (hn : 0 < n) : Q_n E n ↔ LevelUnsound T level n := by
  unfold Q_n
  rw [rawFailure_iff_rankFailure E values agreement n hn,
    rankFailure_iff_levelUnsound N values records level bridge n hn]
  exact (and_iff_right hn).trans (and_iff_right hc)

theorem positive_level_upward {T : TheoryPresentation}
    (N : NormalizationCertificate T) (values : RecordValues)
    (records : EmittedRelation N values) (E : EventStructure)
    (agreement : RecordsAgree E values) (hc : Complete E)
    (level : Nat → T.Sentence → Prop) (bridge : FiniteLevelBridge T N level)
    (nest : ∀ n sentence, 0 < n → level n sentence → level (n+1) sentence)
    (n : Nat) (hn : 0 < n) : Q_n E n → Q_n E (n+1) := by
  intro h
  apply (positive_level_calibration N values records E agreement hc level bridge
    (n+1) (Nat.zero_lt_succ n)).mpr
  apply levelUnsound_upward level nest n hn
  exact (positive_level_calibration N values records E agreement hc level bridge n hn).mp h

/-- The level-zero nesting case needs a genuine contradiction classified at
positive level one.  It is not inferred from quantifier-free standard falsity. -/
theorem zero_to_first_level {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (values : RecordValues) (records : EmittedRelation N values)
    (view : ZeroView) (E : EventStructure) (agreement : RecordsAgree E values)
    (zeroRecords : ZeroEmittedRelation B view E) (hc : Complete E)
    (level : Nat → T.Sentence → Prop) (bridge : FiniteLevelBridge T N level)
    (bottomAtOne : level 1 B.bottom) : Q_0 view E → Q_n E 1 := by
  intro hz
  apply (positive_level_calibration N values records E agreement hc level bridge 1 (by decide)).mpr
  exact ⟨B.bottom, (levelZero_exact B view E zeroRecords hc).mp hz, bottomAtOne, B.falseInN⟩

end PASoundness.Observer
