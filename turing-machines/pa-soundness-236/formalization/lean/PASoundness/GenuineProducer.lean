import PASoundness.ArithmeticCertificates
import PASoundness.ArithmeticNormalization
import PASoundness.UniformMachine

/-!
A closed, effective source instance for genuine arithmetic calculi. Its
certificate carries the original syntactic theorem. Canonical semantic
normalization is performed by the producer; no unproved claim that a normalized
formula is an object-theory theorem is needed. This is a separate reusable
source format, not a new identification of PA926's compact PA238 computation.
The wire and finite observer syntax are unchanged. Positive levels here mean
the explicit computed singleton-rank bound, not semantic Sigma_n levels.
-/
namespace PASoundness.GenuineProducer
open FirstOrder FirstOrder.Language Observer ArithmeticCertificates
open Shared.Beeping.Machines

def normalized (T : CheckedTheory) (n p : Nat) : Option Peano.Sentence :=
  (checked T p).bind fun φ => if ArithmeticNormalization.rank φ ≤ n then some φ else none

theorem normalized_some (T : CheckedTheory) (n p : Nat) (φ : Peano.Sentence) :
    normalized T n p = some φ ↔ checked T p = some φ ∧ ArithmeticNormalization.rank φ ≤ n := by
  simp only [normalized, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨ψ, hc, hh⟩
    split at hh
    · cases hh; exact ⟨hc, ‹_›⟩
    · cases hh
  · rintro ⟨hc, hr⟩
    exact ⟨φ, hc, if_pos hr⟩

def matrixValue (T : CheckedTheory) (n p : Nat) (xs : List Nat) : Bool :=
  match normalized T n p with
  | none => false
  | some φ => ArithmeticNormalization.matrix φ (xs.take (ArithmeticNormalization.rank φ))

def normalization (T : CheckedTheory) : NormalizationCertificate T.presentation where
  valid := fun n p => ∃ φ, normalized T n p = some φ
  matrix := fun n p xs => matrixValue T n p xs = true
  origin := by
    rintro n p _ ⟨φ, hf⟩
    obtain ⟨hc, hr⟩ := (normalized_some T n p φ).mp hf
    refine ⟨φ, checked_origin T p φ hc, ?_⟩
    simp only [matrixValue, hf]
    exact (ArithmeticNormalization.semantics φ).trans
      (altPrefix_pad_to .ex (ArithmeticNormalization.rank φ) n
        (fun xs => ArithmeticNormalization.matrix φ xs = true) hr).symm
  coverage := by
    intro φ hp
    obtain ⟨p, hc⟩ := checked_coverage T φ hp
    have hf : normalized T (ArithmeticNormalization.rank φ) p = some φ :=
      (normalized_some T _ p φ).mpr ⟨hc, le_rfl⟩
    refine ⟨ArithmeticNormalization.rank φ, ArithmeticNormalization.rank_pos φ, p,
      ⟨φ, hf⟩, ?_⟩
    simp only [matrixValue, hf]
    exact (ArithmeticNormalization.semantics φ).trans
      (altPrefix_pad_to .ex (ArithmeticNormalization.rank φ) (ArithmeticNormalization.rank φ)
        (fun xs => ArithmeticNormalization.matrix φ xs = true) le_rfl).symm

/-- Invalid proof/sentence payloads, insufficient rank, or wrong tuple length
produce zero. Valid records compute the negated finite arithmetic matrix. -/
def value (T : CheckedTheory) (a : Address) : Bool :=
  if a.coordinates.length = a.rank then
    match normalized T a.rank a.certificate with
    | none => false
    | some φ => !(ArithmeticNormalization.matrix φ
        (a.coordinates.take (ArithmeticNormalization.rank φ)))
  else false

theorem record_spec (T : CheckedTheory) (n p : Nat) (xs : List Nat) (hlen : xs.length = n) :
    value T ⟨n, p, xs⟩ = true ↔
      (normalization T).valid n p ∧ ¬ (normalization T).matrix n p xs := by
  cases hf : normalized T n p with
  | none => simp [value, hlen, normalization, hf]
  | some φ =>
    simp only [value, hlen, if_true, hf, normalization, matrixValue, Option.some.injEq]
    cases ArithmeticNormalization.matrix φ (xs.take (ArithmeticNormalization.rank φ)) <;> simp

theorem emitted_relation (T : CheckedTheory) :
    EmittedRelation (normalization T) (Source.recordValues (value T)) :=
  fun n p xs _ hlen => record_spec T n p xs hlen

theorem malformed_tuple_zero (T : CheckedTheory) (a : Address)
    (h : a.coordinates.length ≠ a.rank) : value T a = false := by
  simp [value, h]

theorem rejected_certificate_zero (T : CheckedTheory) (n p : Nat) (xs : List Nat)
    (h : checked T p = none) : value T ⟨n, p, xs⟩ = false := by
  simp [value, normalized, h]

/-- The same finite proof payload serves higher syntactic ranks; the only
change is the proved projection away from unused matrix coordinates. -/
def padding (T : CheckedTheory) : CertificatePadding (normalization T) where
  next := fun _ p => p
  valid := by
    rintro n p _ ⟨φ, hf⟩
    obtain ⟨hc, hr⟩ := (normalized_some T n p φ).mp hf
    exact ⟨φ, (normalized_some T (n+1) p φ).mpr ⟨hc, Nat.le.step hr⟩⟩
  matrix := by
    rintro n p xs _ ⟨φ, hf⟩ _
    obtain ⟨hc, hr⟩ := (normalized_some T n p φ).mp hf
    have hnext := (normalized_some T (n+1) p φ).mpr ⟨hc, Nat.le.step hr⟩
    simp [normalization, matrixValue, hf, hnext, List.take_take, Nat.min_eq_left hr]

def events (T : CheckedTheory) : EventStructure := Source.events (value T)
def source (T : CheckedTheory) : WordEventSystem Nat Bool := Source.source (value T)

theorem complete (T : CheckedTheory) : Complete (events T) := Source.complete (value T)

def bottomCertificates (T : CheckedTheory) : BottomCertificates T.presentation where
  bottom := (⊥ : Peano.Sentence)
  falseInN := FirstOrder.Language.Sentence.not_realize_bot Nat
  valid := fun p => Marker.bottomTail p = true ∧ checked T p = some (⊥ : Peano.Sentence)
  origin := fun p h => checked_origin T p _ h.2
  coverage := by
    intro h
    obtain ⟨p, hp⟩ := T.coverage _ h
    exact ⟨bottomCode p, bottomCode_marked p, checked_bottomCode T p hp⟩

theorem marked_value_iff (T : CheckedTheory) (p : Nat) (hm : Marker.bottomTail p = true) :
    value T ⟨1, p, [0]⟩ = true ↔ checked T p = some (⊥ : Peano.Sentence) := by
  constructor
  · intro hv
    obtain ⟨⟨φ, hf⟩, _⟩ := (record_spec T 1 p [0] rfl).mp hv
    have hc := ((normalized_some T 1 p φ).mp hf).1
    rw [checked_marked_bottom T p φ hm hc] at hc
    exact hc
  · intro hc
    have hf : normalized T 1 p = some (⊥ : Peano.Sentence) :=
      (normalized_some T 1 p _).mpr ⟨hc, by rw [ArithmeticNormalization.rank_bot]⟩
    simp [value, hf, ArithmeticNormalization.matrix_bot]

theorem zero_emitted_relation (T : CheckedTheory) :
    ZeroEmittedRelation (bottomCertificates T) .compactSuffix (events T) := by
  intro p
  change (Marker.bottomTail p = true ∧ Emitted (Source.events (value T)) true ⟨1, p, [0]⟩) ↔ _
  rw [Source.emitted_exact]
  constructor
  · rintro ⟨hm, _, hv⟩
    exact ⟨hm, (marked_value_iff T p hm).mp hv⟩
  · rintro ⟨hm, hc⟩
    exact ⟨hm, ⟨rfl, fun _ => Nat.zero_lt_succ 0⟩, (marked_value_iff T p hm).mpr hc⟩

/-- Closed source theorem: no theory soundness is used in its proof. -/
theorem source_iff_sound (T : CheckedTheory) :
    SoundnessAcceptance .compactSuffix (events T) ↔ T.presentation.Sound :=
  Source.acceptance_iff_sound (normalization T) (bottomCertificates T) (value T)
    (emitted_relation T) .compactSuffix (zero_emitted_relation T)

theorem source_formulas_iff_sound (T : CheckedTheory) :
    FormulaAcceptance .compactSuffix (events T) ↔ T.presentation.Sound :=
  Source.formulaAcceptance_iff_sound (normalization T) (bottomCertificates T) (value T)
    (emitted_relation T) .compactSuffix (zero_emitted_relation T)

theorem source_omega_iff_unsound (T : CheckedTheory) :
    Q_omega .compactSuffix (events T) ↔ ¬ T.presentation.Sound :=
  observer_omega_iff_unsound (normalization T) (bottomCertificates T)
    (Source.recordValues (value T)) (emitted_relation T) .compactSuffix (events T)
    (Source.recordsAgree (value T)) (zero_emitted_relation T) (complete T)

theorem source_zero_iff_inconsistent (T : CheckedTheory) :
    Q_0 .compactSuffix (events T) ↔ T.Proves (⊥ : Peano.Sentence) :=
  levelZero_exact (bottomCertificates T) .compactSuffix (events T)
    (zero_emitted_relation T) (complete T)

/-- An explicit syntactic class, computed from the original sentence's
canonical prenex form. This name never denotes the arithmetic Sigma hierarchy. -/
def RankAtMost (n : Nat) (φ : Peano.Sentence) : Prop := ArithmeticNormalization.rank φ ≤ n

theorem finiteRankBridge (T : CheckedTheory) :
    FiniteLevelBridge T.presentation (normalization T) RankAtMost where
  origin := by
    rintro n p _ ⟨φ, hf⟩
    obtain ⟨hc, hr⟩ := (normalized_some T n p φ).mp hf
    refine ⟨φ, checked_origin T p φ hc, hr, ?_⟩
    simp only [normalization, matrixValue, hf]
    exact (ArithmeticNormalization.semantics φ).trans
      (altPrefix_pad_to .ex (ArithmeticNormalization.rank φ) n
        (fun xs => ArithmeticNormalization.matrix φ xs = true) hr).symm
  coverage := by
    intro n φ _ hp hr
    obtain ⟨p, hc⟩ := checked_coverage T φ hp
    have hf := (normalized_some T n p φ).mpr ⟨hc, hr⟩
    refine ⟨p, ⟨φ, hf⟩, ?_⟩
    simp only [normalization, matrixValue, hf]
    exact (ArithmeticNormalization.semantics φ).trans
      (altPrefix_pad_to .ex (ArithmeticNormalization.rank φ) n
        (fun xs => ArithmeticNormalization.matrix φ xs = true) hr).symm

theorem source_level_iff_rankUnsound (T : CheckedTheory) (n : Nat) (hn : 0 < n) :
    Q_n (events T) n ↔ LevelUnsound T.presentation RankAtMost n :=
  positive_level_calibration (normalization T) (Source.recordValues (value T))
    (emitted_relation T) (events T) (Source.recordsAgree (value T)) (complete T)
    RankAtMost (finiteRankBridge T) n hn

theorem source_level_upward (T : CheckedTheory) (n : Nat) (hn : 0 < n) :
    Q_n (events T) n → Q_n (events T) (n+1) :=
  positive_level_upward (normalization T) (Source.recordValues (value T))
    (emitted_relation T) (events T) (Source.recordsAgree (value T)) (complete T)
    RankAtMost (finiteRankBridge T) (fun _ _ _ h => Nat.le.step h) n hn

theorem source_zero_to_one (T : CheckedTheory) :
    Q_0 .compactSuffix (events T) → Q_n (events T) 1 :=
  zero_to_first_level (normalization T) (bottomCertificates T)
    (Source.recordValues (value T)) (emitted_relation T) .compactSuffix (events T)
    (Source.recordsAgree (value T)) (zero_emitted_relation T) (complete T)
    RankAtMost (finiteRankBridge T) (by change ArithmeticNormalization.rank _ ≤ 1; rfl)

theorem machine_iff_sound (T : CheckedTheory) {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate (source T) M) :
    SoundnessAcceptance .compactSuffix (UniformMachine.events cert) ↔ T.presentation.Sound :=
  UniformMachine.acceptance_iff_sound (normalization T) (bottomCertificates T)
    (value T) (emitted_relation T) .compactSuffix (zero_emitted_relation T) cert

theorem machine_omega_iff_unsound (T : CheckedTheory) {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate (source T) M) :
    Q_omega .compactSuffix (UniformMachine.events cert) ↔ ¬ T.presentation.Sound :=
  UniformMachine.omega_iff_unsound (normalization T) (bottomCertificates T)
    (value T) (emitted_relation T) .compactSuffix (zero_emitted_relation T) cert

theorem machine_zero_iff_inconsistent (T : CheckedTheory) {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate (source T) M) :
    Q_0 .compactSuffix (UniformMachine.events cert) ↔ T.Proves (⊥ : Peano.Sentence) :=
  UniformMachine.zero_iff_bottom (bottomCertificates T) (value T)
    .compactSuffix (zero_emitted_relation T) cert

theorem machine_level_iff_rankUnsound (T : CheckedTheory) {states : Nat}
    {M : Machine states} (cert : ImplementationCertificate (source T) M)
    (n : Nat) (hn : 0 < n) :
    Q_n (UniformMachine.events cert) n ↔ LevelUnsound T.presentation RankAtMost n :=
  UniformMachine.positive_level_iff (normalization T) (value T) (emitted_relation T)
    RankAtMost (finiteRankBridge T) cert n hn

theorem machine_level_upward (T : CheckedTheory) {states : Nat}
    {M : Machine states} (cert : ImplementationCertificate (source T) M)
    (n : Nat) (hn : 0 < n) :
    Q_n (UniformMachine.events cert) n → Q_n (UniformMachine.events cert) (n+1) :=
  fun h => (UniformMachine.level_iff_source cert (n+1)).mpr
    (source_level_upward T n hn ((UniformMachine.level_iff_source cert n).mp h))

theorem machine_zero_to_one (T : CheckedTheory) {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (source T) M) :
    Q_0 .compactSuffix (UniformMachine.events cert) → Q_n (UniformMachine.events cert) 1 :=
  fun h => (UniformMachine.level_iff_source cert 1).mpr
    (source_zero_to_one T ((UniformMachine.zero_iff_source cert .compactSuffix).mp h))

/-- PA soundness is applied only after the structural source theorem. -/
theorem pa_source_acceptance : SoundnessAcceptance .compactSuffix (events pa) :=
  (source_iff_sound pa).mpr pa_sound

theorem pa_source_no_finite_failure : ¬ Q_omega .compactSuffix (events pa) :=
  fun h => (source_omega_iff_unsound pa).mp h pa_sound

theorem pa_machine_acceptance {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate (source pa) M) :
    SoundnessAcceptance .compactSuffix (UniformMachine.events cert) :=
  (machine_iff_sound pa cert).mpr pa_sound

theorem pa_machine_no_finite_failure {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate (source pa) M) :
    ¬ Q_omega .compactSuffix (UniformMachine.events cert) :=
  fun h => (machine_omega_iff_unsound pa cert).mp h pa_sound

/-! The same source, decoder, finite observer vocabulary, and formula generator
are now instantiated on each elementary control theory, without PA background. -/

theorem empty_acceptance : SoundnessAcceptance .compactSuffix (events empty) :=
  (source_iff_sound empty).mpr empty_sound

theorem harmless_acceptance :
    SoundnessAcceptance .compactSuffix (events (oneAxiom Fixtures.reflexive)) :=
  (source_iff_sound _).mpr harmless_sound

theorem falseZero_zero : Q_0 .compactSuffix (events (oneAxiom Fixtures.falseZero)) :=
  (source_zero_iff_inconsistent _).mpr falseZero_inconsistent

theorem allZero_omega : Q_omega .compactSuffix (events (oneAxiom Fixtures.allZero)) :=
  (source_omega_iff_unsound _).mpr allZero_unsound

theorem allZero_no_zero : ¬ Q_0 .compactSuffix (events (oneAxiom Fixtures.allZero)) :=
  fun h => allZero_consistent ((source_zero_iff_inconsistent _).mp h)

theorem allZero_rankThree : Q_n (events (oneAxiom Fixtures.allZero)) 3 := by
  apply (source_level_iff_rankUnsound _ 3 (by decide)).mpr
  exact ⟨Fixtures.allZero, FOL.sentence_axiom rfl,
    (by change 3 ≤ 3; exact le_rfl), Fixtures.allZero_not_nat⟩

theorem collapsedSuccessor_omega :
    Q_omega .compactSuffix (events (oneAxiom Fixtures.collapsedSuccessor)) :=
  (source_omega_iff_unsound _).mpr collapsedSuccessor_unsound

theorem collapsedSuccessor_no_zero :
    ¬ Q_0 .compactSuffix (events (oneAxiom Fixtures.collapsedSuccessor)) :=
  fun h => collapsedSuccessor_consistent ((source_zero_iff_inconsistent _).mp h)

theorem collapsedSuccessor_rankOne :
    Q_n (events (oneAxiom Fixtures.collapsedSuccessor)) 1 := by
  apply (source_level_iff_rankUnsound _ 1 (by decide)).mpr
  exact ⟨Fixtures.collapsedSuccessor, FOL.sentence_axiom rfl,
    (by change 1 ≤ 1; exact le_rfl), Fixtures.collapsedSuccessor_not_nat⟩

theorem oneAxiom_sound_iff (φ : Peano.Sentence) :
    (oneAxiom φ).presentation.Sound ↔ Nat ⊨ φ := by
  constructor
  · intro h; exact h φ (FOL.sentence_axiom rfl)
  · intro h ψ hp
    exact FOL.theory_sound (fun χ hχ => hχ ▸ h) hp

theorem oneAxiom_acceptance_iff (φ : Peano.Sentence) :
    SoundnessAcceptance .compactSuffix (events (oneAxiom φ)) ↔ Nat ⊨ φ :=
  (source_iff_sound _).trans (oneAxiom_sound_iff φ)

end PASoundness.GenuineProducer
