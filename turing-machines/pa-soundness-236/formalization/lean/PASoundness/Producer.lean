import Std

/-!
The all-rank alternating-bit argument.  This module contains no arithmetic
truth algorithm and no axiom asserting soundness of a theory.  Normalization
origin and coverage are explicit *premises* of the reusable theorem.  The
old `failureExact` certificate field is replaced by a proved theorem.
-/

namespace PASoundness

inductive Polarity where
  | ex
  | all
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
  | .ex => .all
  | .all => .ex

@[simp] theorem Polarity.flip_flip (q : Polarity) : q.flip.flip = q := by
  cases q <;> rfl

/-- Finite alternating quantification, in the source's left-to-right tuple order. -/
def altPrefix : Polarity → Nat → (List Nat → Prop) → Prop
  | _, 0, matrix => matrix []
  | .ex, n + 1, matrix => ∃ x : Nat, altPrefix .all n (fun xs => matrix (x :: xs))
  | .all, n + 1, matrix => ∀ x : Nat, altPrefix .ex n (fun xs => matrix (x :: xs))

/-- Only tuples of the advertised finite length are ever read. -/
theorem altPrefix_congr_length (q : Polarity) (n : Nat)
    (left right : List Nat → Prop)
    (h : ∀ xs, xs.length = n → (left xs ↔ right xs)) :
    altPrefix q n left ↔ altPrefix q n right := by
  induction n generalizing q left right with
  | zero => exact h [] rfl
  | succ n ih =>
    cases q with
    | ex =>
      apply exists_congr
      intro x
      apply ih
      intro xs hx
      exact h (x :: xs) (by simp [hx])
    | all =>
      apply forall_congr'
      intro x
      apply ih
      intro xs hx
      exact h (x :: xs) (by simp [hx])

/-- Finite quantified duality; classical logic is used only in the metatheory. -/
theorem altPrefix_duality (q : Polarity) (n : Nat) (matrix : List Nat → Prop) :
    altPrefix q n (fun xs => ¬ matrix xs) ↔ ¬ altPrefix q.flip n matrix := by
  classical
  induction n generalizing q matrix with
  | zero => rfl
  | succ n ih =>
    cases q <;> simp only [altPrefix, Polarity.flip, ih, Classical.not_forall, not_exists]

/-- Invalid certificates cannot acquire a witness through an alternating altPrefix.
The universal step uses the nonempty natural-number domain. -/
theorem altPrefix_and_constant (q : Polarity) (n : Nat)
    (valid : Prop) (matrix : List Nat → Prop) :
    altPrefix q n (fun xs => valid ∧ matrix xs) ↔ valid ∧ altPrefix q n matrix := by
  induction n generalizing q matrix with
  | zero => rfl
  | succ n ih =>
    cases q <;> simp only [altPrefix, ih]
    · constructor
      · rintro ⟨x, hv, hx⟩
        exact ⟨hv, x, hx⟩
      · rintro ⟨hv, x, hx⟩
        exact ⟨x, hv, hx⟩
    · constructor
      · intro h
        exact ⟨(h 0).1, fun x => (h x).2⟩
      · rintro ⟨hv, h⟩ x
        exact ⟨hv, h x⟩

theorem altPrefix_constant (q : Polarity) (n : Nat) (P : Prop) :
    altPrefix q n (fun _ => P) ↔ P := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    cases q <;> simp only [altPrefix, ih]
    · constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨0, h⟩
    · constructor
      · intro h; exact h 0
      · intro h _; exact h

/-- A trailing unused coordinate gives the next alternating syntactic rank.
This is semantic padding only; a producer must also transport certificates. -/
theorem altPrefix_pad (q : Polarity) (n : Nat) (matrix : List Nat → Prop) :
    altPrefix q (n+1) (fun xs => matrix (xs.take n)) ↔ altPrefix q n matrix := by
  induction n generalizing q matrix with
  | zero =>
    cases q <;> simp only [altPrefix, List.take_zero]
    · constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨0, h⟩
    · constructor
      · intro h; exact h 0
      · intro h _; exact h
  | succ n ih =>
    cases q with
    | ex =>
      apply exists_congr
      intro x
      simpa only [List.take_succ_cons] using ih .all (fun xs => matrix (x :: xs))
    | all =>
      apply forall_congr'
      intro x
      simpa only [List.take_succ_cons] using ih .ex (fun xs => matrix (x :: xs))

/-- Any number of trailing unused coordinates preserves the finite prefix.
The theorem does not by itself assert that a concrete proof checker admits
the padded rank; that certificate transport remains a source obligation. -/
theorem altPrefix_pad_to (q : Polarity) (r n : Nat) (matrix : List Nat → Prop)
    (h : r ≤ n) :
    altPrefix q n (fun xs => matrix (xs.take r)) ↔ altPrefix q r matrix := by
  induction h with
  | refl =>
    apply altPrefix_congr_length
    intro xs hx
    rw [← hx, List.take_length]
  | @step n h ih =>
    calc
      altPrefix q (n+1) (fun xs => matrix (xs.take r)) ↔
          altPrefix q (n+1) (fun xs => matrix ((xs.take n).take r)) := by
        apply altPrefix_congr_length
        intro xs _
        rw [List.take_take, Nat.min_eq_left h]
      _ ↔ altPrefix q n (fun xs => matrix (xs.take r)) :=
        altPrefix_pad q n (fun xs => matrix (xs.take r))
      _ ↔ altPrefix q r matrix := ih

/-- An unused leading existential converts a universal-leading finite prefix
to the legacy existential-leading convention without changing its truth. -/
theorem altPrefix_leading_dummy (n : Nat) (matrix : List Nat → Prop) :
    altPrefix .ex (n+1) (fun xs => matrix xs.tail) ↔ altPrefix .all n matrix := by
  change (∃ _ : Nat, altPrefix .all n matrix) ↔ _
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨0, h⟩

abbrev RecordValues := Nat → Nat → List Nat → Bool

/-- Raw syntactic-rank failure, without a claim about the arithmetic hierarchy. -/
def RankFailure (values : RecordValues) (rank : Nat) : Prop :=
  ∃ certificate : Nat, altPrefix .all rank (fun xs => values rank certificate xs = true)

/-- Relational interface only.  Concrete clients supply genuine syntax and
syntactic provability; naming a relation here does not construct a calculus. -/
structure TheoryPresentation where
  Sentence : Type
  proves : Sentence → Prop
  trueInN : Sentence → Prop

def TheoryPresentation.Sound (T : TheoryPresentation) : Prop :=
  ∀ sentence, T.proves sentence → T.trueInN sentence

/-- The syntax/proof-transport boundary.  No field assumes soundness. -/
structure NormalizationCertificate (T : TheoryPresentation) where
  valid : Nat → Nat → Prop
  matrix : Nat → Nat → List Nat → Prop
  origin : ∀ n p, 0 < n → valid n p →
    ∃ sentence, T.proves sentence ∧
      (T.trueInN sentence ↔ altPrefix .ex n (matrix n p))
  coverage : ∀ sentence, T.proves sentence →
    ∃ n, 0 < n ∧ ∃ p, valid n p ∧
      (T.trueInN sentence ↔ altPrefix .ex n (matrix n p))

/-- The emitted relation is local and does not require `T.Sound`. -/
def EmittedRelation {T : TheoryPresentation} (N : NormalizationCertificate T)
    (values : RecordValues) : Prop :=
  ∀ n p xs, 0 < n → xs.length = n →
    (values n p xs = true ↔ N.valid n p ∧ ¬ N.matrix n p xs)

/-- The essential equivalence is a theorem, not a certificate assumption. -/
theorem failureExact {T : TheoryPresentation} (N : NormalizationCertificate T)
    (values : RecordValues) (records : EmittedRelation N values)
    (n : Nat) (hn : 0 < n) :
    RankFailure values n ↔
      ∃ p, N.valid n p ∧ ¬ altPrefix .ex n (N.matrix n p) := by
  unfold RankFailure
  apply exists_congr
  intro p
  calc
    altPrefix .all n (fun xs => values n p xs = true) ↔
        altPrefix .all n (fun xs => N.valid n p ∧ ¬ N.matrix n p xs) :=
      altPrefix_congr_length .all n _ _ (fun xs hx => records n p xs hn hx)
    _ ↔ N.valid n p ∧ altPrefix .all n (fun xs => ¬ N.matrix n p xs) :=
      altPrefix_and_constant .all n _ _
    _ ↔ N.valid n p ∧ ¬ altPrefix .ex n (N.matrix n p) :=
      and_congr Iff.rfl (altPrefix_duality .all n (N.matrix n p))

/-- Explicit code-producing padding obligation.  This is not supplied for the
compact source merely by asserting that its theory is sound. -/
structure CertificatePadding {T : TheoryPresentation} (N : NormalizationCertificate T) where
  next : Nat → Nat → Nat
  valid : ∀ n p, 0 < n → N.valid n p → N.valid (n+1) (next n p)
  matrix : ∀ n p xs, 0 < n → N.valid n p → xs.length = n+1 →
    (N.matrix (n+1) (next n p) xs ↔ N.matrix n p (xs.take n))

theorem rankFailure_upward_of_padding {T : TheoryPresentation}
    (N : NormalizationCertificate T) (values : RecordValues)
    (records : EmittedRelation N values) (padding : CertificatePadding N)
    (n : Nat) (hn : 0 < n) : RankFailure values n → RankFailure values (n+1) := by
  intro h
  obtain ⟨p, hv, hf⟩ := (failureExact N values records n hn).mp h
  apply (failureExact N values records (n+1) (Nat.zero_lt_succ n)).mpr
  refine ⟨padding.next n p, padding.valid n p hn hv, ?_⟩
  intro hnext
  have ht := altPrefix_congr_length .ex (n+1) _ _
    (fun xs hx => padding.matrix n p xs hn hv hx)
  exact hf ((altPrefix_pad .ex n (N.matrix n p)).mp (ht.mp hnext))

/-- External existence across finite positive syntactic ranks. -/
def RankOmega (values : RecordValues) : Prop :=
  ∃ n, 0 < n ∧ RankFailure values n

/-- A failure of completeness is not a soundness certificate. -/
def RankAcceptance (complete : Prop) (values : RecordValues) : Prop :=
  complete ∧ ∀ n, 0 < n → ¬ RankFailure values n

theorem rankOmega_iff_unsound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (values : RecordValues)
    (records : EmittedRelation N values) :
    RankOmega values ↔ ¬ T.Sound := by
  classical
  constructor
  · rintro ⟨n, hn, hbad⟩ hs
    obtain ⟨p, hv, hf⟩ := (failureExact N values records n hn).mp hbad
    obtain ⟨sentence, hp, ht⟩ := N.origin n p hn hv
    exact hf (ht.mp (hs sentence hp))
  · intro hs
    have hex : ∃ sentence, T.proves sentence ∧ ¬ T.trueInN sentence := by
      apply Classical.byContradiction
      intro h
      apply hs
      intro sentence hp
      apply Classical.byContradiction
      intro hf
      exact h ⟨sentence, hp, hf⟩
    obtain ⟨sentence, hp, hf⟩ := hex
    obtain ⟨n, hn, p, hv, ht⟩ := N.coverage sentence hp
    exact ⟨n, hn, (failureExact N values records n hn).mpr
      ⟨p, hv, fun h => hf (ht.mpr h)⟩⟩

/-- Conditional producer theorem.  Its result does not instantiate any table. -/
theorem full_soundness_reduction {T : TheoryPresentation}
    (N : NormalizationCertificate T) (values : RecordValues)
    (records : EmittedRelation N values) (complete : Prop) (hc : complete) :
    RankAcceptance complete values ↔ T.Sound := by
  classical
  constructor
  · intro ha sentence hp
    obtain ⟨n, hn, p, hv, ht⟩ := N.coverage sentence hp
    apply ht.mpr
    apply Classical.byContradiction
    intro hf
    exact ha.2 n hn ((failureExact N values records n hn).mpr ⟨p, hv, hf⟩)
  · intro hs
    refine ⟨hc, ?_⟩
    intro n hn hbad
    obtain ⟨p, hv, hf⟩ := (failureExact N values records n hn).mp hbad
    obtain ⟨sentence, hp, ht⟩ := N.origin n p hn hv
    exact hf (ht.mp (hs sentence hp))

theorem incomplete_not_rankAcceptance (complete : Prop) (values : RecordValues)
    (hc : ¬ complete) : ¬ RankAcceptance complete values :=
  fun h => hc h.1

/-- Exact finite-level calibration requires additional syntactic proof transport.
`level` is a specified syntax class supplied by a client, not arbitrary semantic
equivalence in Nat.  No such bridge is asserted for the PA238/HF producer. -/
structure FiniteLevelBridge (T : TheoryPresentation)
    (N : NormalizationCertificate T) (level : Nat → T.Sentence → Prop) where
  origin : ∀ n p, 0 < n → N.valid n p →
    ∃ sentence, T.proves sentence ∧ level n sentence ∧
      (T.trueInN sentence ↔ altPrefix .ex n (N.matrix n p))
  coverage : ∀ n sentence, 0 < n → T.proves sentence → level n sentence →
    ∃ p, N.valid n p ∧
      (T.trueInN sentence ↔ altPrefix .ex n (N.matrix n p))

def LevelUnsound (T : TheoryPresentation) (level : Nat → T.Sentence → Prop)
    (n : Nat) : Prop :=
  ∃ sentence, T.proves sentence ∧ level n sentence ∧ ¬ T.trueInN sentence

theorem rankFailure_iff_levelUnsound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (values : RecordValues)
    (records : EmittedRelation N values) (level : Nat → T.Sentence → Prop)
    (bridge : FiniteLevelBridge T N level) (n : Nat) (hn : 0 < n) :
    RankFailure values n ↔ LevelUnsound T level n := by
  rw [failureExact N values records n hn]
  constructor
  · rintro ⟨p, hv, hf⟩
    obtain ⟨sentence, hp, hl, ht⟩ := bridge.origin n p hn hv
    exact ⟨sentence, hp, hl, fun h => hf (ht.mp h)⟩
  · rintro ⟨sentence, hp, hl, hf⟩
    obtain ⟨p, hv, ht⟩ := bridge.coverage n sentence hn hp hl
    exact ⟨p, hv, fun h => hf (ht.mpr h)⟩

theorem levelUnsound_upward {T : TheoryPresentation}
    (level : Nat → T.Sentence → Prop)
    (nest : ∀ n sentence, 0 < n → level n sentence → level (n+1) sentence)
    (n : Nat) (hn : 0 < n) :
    LevelUnsound T level n → LevelUnsound T level (n+1) := by
  rintro ⟨sentence, hp, hl, hf⟩
  exact ⟨sentence, hp, nest n sentence hn hl, hf⟩

/-- Finite certificates of a designated syntactic contradiction.  A concrete
calculus must instantiate `bottom` with its literal false sentence.  This
interface does not equate arbitrary standard-false sentences with contradiction. -/
structure BottomCertificates (T : TheoryPresentation) where
  bottom : T.Sentence
  falseInN : ¬ T.trueInN bottom
  valid : Nat → Prop
  origin : ∀ p, valid p → T.proves bottom
  coverage : T.proves bottom → ∃ p, valid p

def BottomCertificates.ProvesBottom {T : TheoryPresentation} (B : BottomCertificates T) : Prop :=
  T.proves B.bottom

theorem BottomCertificates.exact {T : TheoryPresentation} (B : BottomCertificates T) :
    (∃ p, B.valid p) ↔ B.ProvesBottom := by
  constructor
  · rintro ⟨p, hp⟩
    exact B.origin p hp
  · exact B.coverage

theorem BottomCertificates.unsound {T : TheoryPresentation}
    (B : BottomCertificates T) : B.ProvesBottom → ¬ T.Sound := by
  intro hp hs
  exact B.falseInN (hs B.bottom hp)

end PASoundness
