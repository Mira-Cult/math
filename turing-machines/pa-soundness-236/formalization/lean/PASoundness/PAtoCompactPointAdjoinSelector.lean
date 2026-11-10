import PASoundness.PAtoCompactAdjunction

/-! Literal selector-8 witness for adjoining an arbitrary single represented
point to a supplied represented set. This constructs the raw selector body;
it does not itself derive the full adjunction graph or a collection theorem. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactPointAdjoinSelector
open PASoundness.CompactProof PASoundness.CompactDerivations

/-- A candidate member t is either the selected point p or a member of x. -/
def adjoinPredicate (x p t : Nat) : Nat :=
  either (equal t p) (member x t)

/-- The literal selector-8 body with x as container and t as both its test
and designated-point name. The predicate code is the witness name. -/
def adjoinBody (x p t : Nat) : Nat :=
  let c := adjoinPredicate x p t
  both (allCode t (both
      (imp (member x t) (imp c (member c t)))
      (imp (member c t) c)))
    (imp c (member c t))

/-- The witness name exceeds the numeric names x, p, and t. -/
theorem predicate_names_lt (x p t : Nat) :
    x < adjoinPredicate x p t ∧ p < adjoinPredicate x p t ∧ t < adjoinPredicate x p t := by
  have hxt := Cantor.left_le_pair x t
  have htx := Cantor.right_le_pair x t
  have htp := Cantor.right_le_pair t p
  have he := Cantor.left_le_pair (equal t p) 1
  have hroot := Cantor.left_le_pair (neg (equal t p)) (member x t)
  have hright := Cantor.right_le_pair (neg (equal t p)) (member x t)
  unfold adjoinPredicate either neg imp equal member at *
  omega

/-- The exact selector witness. The explicit container-name guard is retained;
the test-name guard follows from the predicate-code bound. -/
def selector8_adjoin_witness (x p t : Nat) (hxc : x ≠ adjoinPredicate x p t) :
    KDerivation (existsCode (adjoinPredicate x p t) (adjoinBody x p t)) := by
  let c := adjoinPredicate x p t
  have hc := predicate_names_lt x p t
  have hguard : ¬ (c = x ∨ c = t) := by
    intro h
    rcases h with hx | ht
    · exact hxc hx.symm
    · dsimp [c] at ht
      omega
  have h := KDerivation.axiom (⟨8, by decide⟩ : Fin 9) x t c 0
  simp only [axiomCode, if_neg hguard] at h
  exact Context.closeEmpty (Context.conjunctionLeft (.closed h))

theorem selector8_adjoin_certificate (x p t : Nat) (hxc : x ≠ adjoinPredicate x p t) :
    theoremCode (certificate (selector8_adjoin_witness x p t hxc)) =
      existsCode (adjoinPredicate x p t) (adjoinBody x p t) :=
  certificate_correct (selector8_adjoin_witness x p t hxc)

/-- The code bound supplies the guard, so the raw selector witness is closed. -/
def selector8_adjoin_witness_closed (x p t : Nat) :
    KDerivation (existsCode (adjoinPredicate x p t) (adjoinBody x p t)) :=
  selector8_adjoin_witness x p t (Nat.ne_of_lt (predicate_names_lt x p t).1)

end PASoundness.PAtoCompactPointAdjoinSelector

#print axioms PASoundness.PAtoCompactPointAdjoinSelector.selector8_adjoin_witness
#print axioms PASoundness.PAtoCompactPointAdjoinSelector.selector8_adjoin_certificate
#print axioms PASoundness.PAtoCompactPointAdjoinSelector.selector8_adjoin_witness_closed
