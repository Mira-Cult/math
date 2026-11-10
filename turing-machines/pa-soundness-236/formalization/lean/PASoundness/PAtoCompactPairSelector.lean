import PASoundness.PAtoCompactAdjunction

/-! The literal selector-8 witness for an unordered-pair predicate. This
module retains the exact selector body and explicit container-name guard; it
does not establish the pair graph or uniqueness of representatives. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactPairSelector
open PASoundness.CompactProof PASoundness.CompactDerivations

/-- The designated element name `t` is equal to either displayed endpoint. -/
def pairPredicate (a b t : Nat) : Nat :=
  either (equal t a) (equal t b)

/-- Exact selector body for input container `x`, free endpoints `a`, `b`,
and the element name `t`. The predicate code is the witness name. -/
def pairSelectorBody (x a b t : Nat) : Nat :=
  let c := pairPredicate a b t
  both (allCode t (both
      (imp (member x t) (imp c (member c t)))
      (imp (member c t) c)))
    (imp c (member c t))

/-- The predicate code is larger than each name occurring in it. -/
theorem predicate_names_lt (a b t : Nat) :
    a < pairPredicate a b t ∧ b < pairPredicate a b t ∧ t < pairPredicate a b t := by
  have hta := Cantor.right_le_pair t a
  have htt := Cantor.left_le_pair t a
  have htb := Cantor.right_le_pair t b
  have hleft := Cantor.left_le_pair (equal t a) 1
  have hroot := Cantor.left_le_pair (neg (equal t a)) (equal t b)
  have hright := Cantor.right_le_pair (neg (equal t a)) (equal t b)
  unfold pairPredicate either neg imp equal at *
  omega

/-- Selector 8 gives its unmodified witness whenever the container name does
not equal the computed predicate/witness name. The element-name guard follows
from `predicate_names_lt`; the endpoint names remain unrestricted. -/
def selector8_pair_witness (x a b t : Nat) (hxc : x ≠ pairPredicate a b t) :
    KDerivation (existsCode (pairPredicate a b t) (pairSelectorBody x a b t)) := by
  let c := pairPredicate a b t
  have hc := predicate_names_lt a b t
  have hguard : ¬ (c = x ∨ c = t) := by dsimp [c]; omega
  have h := KDerivation.axiom (⟨8, by decide⟩ : Fin 9) x t c 0
  simp only [axiomCode, if_neg hguard] at h
  exact Context.closeEmpty (Context.conjunctionLeft (.closed h))

theorem selector8_pair_certificate (x a b t : Nat) (hxc : x ≠ pairPredicate a b t) :
    theoremCode (certificate (selector8_pair_witness x a b t hxc)) =
      existsCode (pairPredicate a b t) (pairSelectorBody x a b t) :=
  certificate_correct (selector8_pair_witness x a b t hxc)

end PASoundness.PAtoCompactPairSelector

#print axioms PASoundness.PAtoCompactPairSelector.selector8_pair_witness
#print axioms PASoundness.PAtoCompactPairSelector.selector8_pair_certificate
