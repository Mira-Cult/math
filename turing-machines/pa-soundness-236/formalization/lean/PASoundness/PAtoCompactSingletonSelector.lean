import PASoundness.PAtoCompactAdjunction

/-! Selector-8 witness for the equality predicate used to construct a
singleton. This module gives the literal selector body only; converting it
into a singleton membership graph requires additional proof. -/
namespace PASoundness.PAtoCompactSingletonSelector
open PASoundness.CompactProof PASoundness.CompactDerivations

/-- The candidate member named `b` equals the intended element named `a`.
The predicate code is also the witness name selected by selector 8. -/
def singletonPredicate (a b : Nat) : Nat := equal b a

/-- Exact unmodified selector-8 body for the equality predicate. -/
def singletonBody (a b : Nat) : Nat :=
  let c := singletonPredicate a b
  both (allCode b (both
      (imp (member a b) (imp c (member c b)))
      (imp (member c b) c)))
    (imp c (member c b))

/-- The equality code is larger than both of its input names, discharging
selector 8's collision guard. -/
theorem predicate_names_lt (a b : Nat) :
    a < singletonPredicate a b ∧ b < singletonPredicate a b := by
  have ha := Cantor.right_le_pair b a
  have hb := Cantor.left_le_pair b a
  unfold singletonPredicate equal
  omega

/-- Selector 8 supplies its literal body for the equality predicate. This is
a finite K proof, without a semantic-model or domain hypothesis. -/
def selector8_singleton_witness (a b : Nat) :
    KDerivation (existsCode (singletonPredicate a b) (singletonBody a b)) := by
  let c := singletonPredicate a b
  have hc := predicate_names_lt a b
  have hguard : ¬ (c = a ∨ c = b) := by dsimp [c]; omega
  have h := KDerivation.axiom (⟨8, by decide⟩ : Fin 9) a b c 0
  simp only [axiomCode, if_neg hguard] at h
  exact Context.closeEmpty (Context.conjunctionLeft (.closed h))

theorem selector8_singleton_certificate (a b : Nat) :
    theoremCode (certificate (selector8_singleton_witness a b)) =
      existsCode (singletonPredicate a b) (singletonBody a b) :=
  certificate_correct (selector8_singleton_witness a b)

end PASoundness.PAtoCompactSingletonSelector

#print axioms PASoundness.PAtoCompactSingletonSelector.selector8_singleton_witness
#print axioms PASoundness.PAtoCompactSingletonSelector.selector8_singleton_certificate
