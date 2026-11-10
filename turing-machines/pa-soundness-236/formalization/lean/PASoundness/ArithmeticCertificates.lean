import PASoundness.NumericCertificates
import PASoundness.Producer
import PASoundness.Marker
import PASoundness.Fixtures

/-!
Numeric finite certificates for effective presentations in the fixed genuine
arithmetic signature. Every presentation uses the explicit FOL derivation
relation. The checker interface requires syntactic origin and coverage, never
semantic soundness. Its concrete PA, finite-theory, and witnessed-enumeration
instances are total Lean programs. An arbitrary function supplied to an abstract
interface is not thereby claimed computable.
-/
namespace PASoundness.ArithmeticCertificates
open FirstOrder FirstOrder.Language Certificates

-- Never evaluate the enormous fixed marker address by kernel unfolding of
-- the deliberately simple recursive Cantor reference definition.
attribute [local irreducible] Cantor.pair Cantor.triangle

structure CheckedTheory where
  axioms : Peano.Formula → Prop
  check : Nat → Option Peano.Formula
  origin : ∀ code φ, check code = some φ → FOL.Derivation axioms φ
  coverage : ∀ φ, FOL.Derivation axioms φ → ∃ code, check code = some φ

def CheckedTheory.Proves (T : CheckedTheory) (φ : Peano.Sentence) : Prop :=
  FOL.Derivation T.axioms (FOL.openSentence φ)

def CheckedTheory.presentation (T : CheckedTheory) : TheoryPresentation where
  Sentence := Peano.Sentence
  proves := T.Proves
  trueInN := fun φ => Nat ⊨ φ

def pa : CheckedTheory where
  axioms := Peano.Axiom
  check := NumericCertificates.check
  origin := fun _ _ h => NumericCertificates.check_sound h
  coverage := fun _ h => NumericCertificates.check_coverage h

theorem pa_proves (φ : Peano.Sentence) : pa.Proves φ ↔ Peano.Proves φ := Iff.rfl

/-- Serialization tree for a natural-number nonlogical axiom witness. -/
inductive Tree where
  | logical (c : LogicalCode Peano.language)
  | nonlogical (witness : Nat)
  | mp (implication argument : Tree)
  | generalize (x : Nat) (premise : Tree)
  deriving Encodable

abbrev Proof := ProofCode Peano.language Nat

def ofProof : Proof → Tree
  | .logical c => .logical c
  | .nonlogical w => .nonlogical w
  | .mp p q => .mp (ofProof p) (ofProof q)
  | .generalize x p => .generalize x (ofProof p)

def toProof : Tree → Proof
  | .logical c => .logical c
  | .nonlogical w => .nonlogical w
  | .mp p q => .mp (toProof p) (toProof q)
  | .generalize x p => .generalize x (toProof p)

theorem to_of (p : Proof) : toProof (ofProof p) = p := by
  induction p <;> simp [toProof, ofProof, *]

theorem of_to (p : Tree) : ofProof (toProof p) = p := by
  induction p <;> simp [toProof, ofProof, *]

def encode (p : Proof) : Nat := Encodable.encode (ofProof p)

def checkWith (decodeAxiom : Nat → Option Peano.Formula) (code : Nat) :
    Option Peano.Formula :=
  (Encodable.decode (α := Tree) code).bind fun t => Certificates.check decodeAxiom (toProof t)

theorem check_encode (decodeAxiom : Nat → Option Peano.Formula) (p : Proof) :
    checkWith decodeAxiom (encode p) = Certificates.check decodeAxiom p := by
  simp [checkWith, encode, Encodable.encodek, to_of]

def ofDecoder (A : Peano.Formula → Prop) (decodeAxiom : Nat → Option Peano.Formula)
    (origin : ∀ w φ, decodeAxiom w = some φ → A φ)
    (coverage : ∀ φ, A φ → ∃ w, decodeAxiom w = some φ) : CheckedTheory where
  axioms := A
  check := checkWith decodeAxiom
  origin := by
    intro code φ h
    obtain ⟨t, _, ht⟩ := Option.bind_eq_some_iff.mp h
    exact Certificates.check_sound decodeAxiom origin (toProof t) φ ht
  coverage := by
    intro φ hp
    obtain ⟨p, hp⟩ := Certificates.check_coverage decodeAxiom coverage hp
    exact ⟨encode p, (check_encode decodeAxiom p).trans hp⟩

/-- A c.e. axiom certificate carries both its finite enumeration stage and
the list position at that stage. The producer never tests unbounded membership. -/
def ofEnumeration (enumerate : Nat → List Peano.Formula) : CheckedTheory :=
  ofDecoder (EnumeratedAxiom enumerate)
    (fun code => enumeratedDecode enumerate (Cantor.unpair code))
    (fun code φ h => enumeration_origin enumerate (Cantor.unpair code) φ h)
    (by
      intro φ h
      obtain ⟨⟨stage, position⟩, hw⟩ := enumeration_coverage enumerate φ h
      exact ⟨Cantor.pair stage position, by simpa using hw⟩)

/-- Empty nonlogical theory, with every syntactic logical proof still admitted. -/
def empty : CheckedTheory :=
  ofDecoder (FOL.SentenceAxiom Fixtures.emptyTheory) (fun _ => none)
    (by intro _ _ h; cases h)
    (by rintro _ ⟨_, h, _⟩; cases h)

/-- One-axiom family with no implicit PA background axioms. -/
def oneAxiom (φ : Peano.Sentence) : CheckedTheory :=
  ofDecoder (FOL.SentenceAxiom (Fixtures.oneAxiom φ))
    (fun code => if code = 0 then some (FOL.openSentence φ) else none)
    (by
      intro code ψ h
      split at h
      · cases h; exact ⟨φ, rfl, rfl⟩
      · cases h)
    (by
      rintro ψ ⟨χ, hχ, rfl⟩
      cases hχ
      exact ⟨0, rfl⟩)

theorem empty_proves (φ : Peano.Sentence) :
    empty.Proves φ ↔ FOL.Proves Fixtures.emptyTheory φ := Iff.rfl

theorem oneAxiom_proves (φ ψ : Peano.Sentence) :
    (oneAxiom φ).Proves ψ ↔ FOL.Proves (Fixtures.oneAxiom φ) ψ := Iff.rfl

theorem pa_sound : pa.presentation.Sound := Peano.soundness
theorem empty_sound : empty.presentation.Sound := fun _ h => Fixtures.empty_sound h
theorem harmless_sound : (oneAxiom Fixtures.reflexive).presentation.Sound :=
  fun _ h => Fixtures.harmless_sound h

theorem falseZero_inconsistent : (oneAxiom Fixtures.falseZero).Proves (⊥ : Peano.Sentence) :=
  Fixtures.falseZero_inconsistent

theorem allZero_consistent : ¬ (oneAxiom Fixtures.allZero).Proves (⊥ : Peano.Sentence) :=
  Fixtures.allZero_consistent

theorem allZero_unsound : ¬ (oneAxiom Fixtures.allZero).presentation.Sound := by
  intro h
  exact Fixtures.allZero_not_nat (h Fixtures.allZero (FOL.sentence_axiom rfl))

theorem collapsedSuccessor_consistent :
    ¬ (oneAxiom Fixtures.collapsedSuccessor).Proves (⊥ : Peano.Sentence) :=
  Fixtures.collapsedSuccessor_consistent

theorem collapsedSuccessor_unsound :
    ¬ (oneAxiom Fixtures.collapsedSuccessor).presentation.Sound := by
  intro h
  exact Fixtures.collapsedSuccessor_not_nat
    (h Fixtures.collapsedSuccessor (FOL.sentence_axiom rfl))

/-! The addressed source uses a separate, explicit certificate ABI. Ordinary
certificates are three-word lists `[0, sentenceCode, proofCode]`. A literal
contradiction certificate is `[1, proofCode]` followed by the already fixed
sixteen-word structural marker. Reusing that finite metadata recognizer does
not claim that these numbers are PA238 postfix programs. -/

def sentenceCheck (T : CheckedTheory) (sentenceCode proofCode : Nat) :
    Option Peano.Sentence :=
  (Encodable.decode (α := Peano.Sentence) sentenceCode).bind fun φ =>
    if T.check proofCode = some (FOL.openSentence φ) then some φ else none

theorem sentenceCheck_origin (T : CheckedTheory) (s p : Nat) (φ : Peano.Sentence)
    (h : sentenceCheck T s p = some φ) : T.Proves φ := by
  obtain ⟨ψ, _, hψ⟩ := Option.bind_eq_some_iff.mp h
  split at hψ
  · cases hψ; exact T.origin p _ ‹_›
  · cases hψ

theorem sentenceCheck_encode (T : CheckedTheory) (φ : Peano.Sentence) (p : Nat)
    (h : T.check p = some (FOL.openSentence φ)) :
    sentenceCheck T (Encodable.encode φ) p = some φ := by
  simp [sentenceCheck, Encodable.encodek, h]

def normalFields : List Nat → Option (Nat × Nat)
  | [0, s, p] => some (s, p)
  | _ => none

theorem normalFields_some {words : List Nat} {s p : Nat}
    (h : normalFields words = some (s, p)) : words = [0, s, p] := by
  unfold normalFields at h
  split at h <;> simp_all

theorem normalFields_exact (words : List Nat) (s p : Nat) :
    normalFields words = some (s, p) ↔ words = [0, s, p] := by
  constructor
  · exact normalFields_some
  · rintro rfl
    rfl

def markedProof : List Nat → Option Nat
  | 1 :: p :: tail => if tail = Marker.bottomSuffix then some p else none
  | _ => none

theorem markedProof_exact (words : List Nat) (p : Nat) :
    markedProof words = some p ↔ words = 1 :: p :: Marker.bottomSuffix := by
  constructor
  · intro h
    unfold markedProof at h
    split at h
    · split at h <;> simp_all
    · cases h
  · rintro rfl
    unfold markedProof
    exact if_pos rfl

theorem normal_missing_field (s : Nat) : normalFields [0, s] = none := rfl

theorem normal_extra_field (s p extra : Nat) : normalFields [0, s, p, extra] = none := rfl

theorem normal_wrong_tag (s p : Nat) : normalFields [1, s, p] = none := rfl

theorem marked_missing_suffix (p : Nat) : markedProof [1, p] = none := rfl

theorem marked_wrong_suffix (p : Nat) (tail : List Nat) (h : tail ≠ Marker.bottomSuffix) :
    markedProof (1 :: p :: tail) = none := if_neg h

/-- A complete marker followed by even one extra word is not accepted as the
payload suffix. The decoder is sensitive to exact order and list length. -/
theorem marked_extra_word (p extra : Nat) :
    markedProof ([1, p] ++ Marker.bottomSuffix ++ [extra]) = none := by
  change markedProof (1 :: p :: (Marker.bottomSuffix ++ [extra])) = none
  apply marked_wrong_suffix
  intro h
  have hl := congrArg List.length h
  simp only [List.length_append, Marker.bottomSuffix_length, List.length_singleton] at hl
  omega

def bottomCheck (T : CheckedTheory) (p : Nat) : Option Peano.Sentence :=
  if T.check p = some (⊥ : Peano.Formula) then some (⊥ : Peano.Sentence) else none

theorem bottomCheck_origin (T : CheckedTheory) (p : Nat) (φ : Peano.Sentence)
    (h : bottomCheck T p = some φ) : φ = ⊥ ∧ T.Proves φ := by
  unfold bottomCheck at h
  split at h
  · cases h; exact ⟨rfl, T.origin p _ ‹_›⟩
  · cases h

def checkedWords (T : CheckedTheory) (words : List Nat) : Option Peano.Sentence :=
  match normalFields words with
  | some (s, p) => sentenceCheck T s p
  | none => (markedProof words).bind (bottomCheck T)

def checked (T : CheckedTheory) (code : Nat) : Option Peano.Sentence :=
  checkedWords T (Marker.decode code)

/-- Rewrite numeric list decoding while its input remains a symbolic list.
This prevents proof elaboration from evaluating the enormous marker address. -/
theorem checked_encodeWords (T : CheckedTheory) (words : List Nat) :
    checked T (Marker.encode words) = checkedWords T words := by
  unfold checked
  rw [Marker.decode_encode]

theorem checkedWords_marked (T : CheckedTheory) (p : Nat) :
    checkedWords T (1 :: p :: Marker.bottomSuffix) = bottomCheck T p := by
  unfold checkedWords
  change (markedProof (1 :: p :: Marker.bottomSuffix)).bind (bottomCheck T) = _
  have hp : markedProof (1 :: p :: Marker.bottomSuffix) = some p := by
    unfold markedProof
    exact if_pos rfl
  rw [hp, Option.bind_some]

theorem checkedWords_origin (T : CheckedTheory) (words : List Nat) (φ : Peano.Sentence)
    (h : checkedWords T words = some φ) : T.Proves φ := by
  unfold checkedWords at h
  split at h
  · exact sentenceCheck_origin T _ _ φ h
  · obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.mp h
    exact (bottomCheck_origin T p φ hp).2

theorem checked_origin (T : CheckedTheory) (code : Nat) (φ : Peano.Sentence)
    (h : checked T code = some φ) : T.Proves φ :=
  checkedWords_origin T _ φ h

def normalCode (φ : Peano.Sentence) (p : Nat) : Nat :=
  Marker.encode [0, Encodable.encode φ, p]

def bottomCode (p : Nat) : Nat := Marker.encode ([1, p] ++ Marker.bottomSuffix)

theorem checked_normalCode (T : CheckedTheory) (φ : Peano.Sentence) (p : Nat)
    (h : T.check p = some (FOL.openSentence φ)) :
    checked T (normalCode φ p) = some φ := by
  simp only [checked, normalCode, Marker.decode_encode, checkedWords, normalFields]
  exact sentenceCheck_encode T φ p h

theorem checked_coverage (T : CheckedTheory) (φ : Peano.Sentence) (h : T.Proves φ) :
    ∃ code, checked T code = some φ := by
  obtain ⟨p, hp⟩ := T.coverage _ h
  exact ⟨normalCode φ p, checked_normalCode T φ p hp⟩

theorem checked_exact (T : CheckedTheory) (φ : Peano.Sentence) :
    (∃ code, checked T code = some φ) ↔ T.Proves φ :=
  ⟨fun ⟨p, h⟩ => checked_origin T p φ h, checked_coverage T φ⟩

theorem checked_bottomCode (T : CheckedTheory) (p : Nat)
    (h : T.check p = some (⊥ : Peano.Formula)) :
    checked T (bottomCode p) = some (⊥ : Peano.Sentence) := by
  rw [bottomCode, checked_encodeWords]
  change checkedWords T (1 :: p :: Marker.bottomSuffix) = _
  rw [checkedWords_marked]
  exact if_pos h

theorem sentenceCheck_rejects (T : CheckedTheory) (s p : Nat) (h : T.check p = none) :
    sentenceCheck T s p = none := by
  unfold sentenceCheck
  cases Encodable.decode (α := Peano.Sentence) s <;> simp [h]

theorem checked_normal_rejects (T : CheckedTheory) (φ : Peano.Sentence) (p : Nat)
    (h : T.check p = none) : checked T (normalCode φ p) = none := by
  rw [normalCode, checked_encodeWords]
  exact sentenceCheck_rejects T _ p h

theorem checked_bottom_rejects (T : CheckedTheory) (p : Nat)
    (h : T.check p ≠ some (⊥ : Peano.Formula)) : checked T (bottomCode p) = none := by
  rw [bottomCode, checked_encodeWords]
  change checkedWords T (1 :: p :: Marker.bottomSuffix) = _
  rw [checkedWords_marked]
  exact if_neg h

theorem checked_pa_invalid_parent (φ : Peano.Sentence) :
    checked pa (normalCode φ
      (NumericCertificates.encode CertificateFixtures.invalidParent)) = none :=
  checked_normal_rejects pa φ _ NumericCertificates.malformed_parent_rejected

theorem bottomCode_marked (p : Nat) : Marker.bottomTail (bottomCode p) = true :=
  Marker.encoded_suffix_recognized [1, p]

theorem normalCode_unmarked (φ : Peano.Sentence) (p : Nat) :
    Marker.bottomTail (normalCode φ p) = false := by
  simp [Marker.bottomTail, normalCode, Marker.decode_encode, Marker.hasBottomSuffix]

/-- The decoder observes only the fixed suffix. This theorem about producer
certificate checking explains why a marked accepted sentence is literal falsity. -/
theorem checked_marked_bottom (T : CheckedTheory) (code : Nat) (φ : Peano.Sentence)
    (hm : Marker.bottomTail code = true) (h : checked T code = some φ) : φ = ⊥ := by
  unfold checked checkedWords at h
  split at h
  · rename_i s p hf
    have hw := normalFields_some hf
    have hl := (Marker.hasBottomSuffix_iff (Marker.decode code)).mp hm
    rw [hw] at hl
    simp at hl
  · obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.mp h
    exact (bottomCheck_origin T p φ hp).1

end PASoundness.ArithmeticCertificates
