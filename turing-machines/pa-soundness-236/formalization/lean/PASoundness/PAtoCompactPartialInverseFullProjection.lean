import PASoundness.PAtoCompactPartialInverseBase
import PASoundness.PAtoCompactRestrictedInverseFirst

/-! Project a partial-inverse invariant at the full input prefix into the
exact domain-restricted inverse correspondence. This is finite literal K
proof data; it neither produces the full-prefix graph nor asserts symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseFullProjection
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialInverseBase
open PASoundness.PAtoCompactRestrictedInverseExists PASoundness.PAtoCompactRestrictedInverseFirst
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def fullPrefix : Formula := replace 8 0 partialInverse

def pointBody : Formula := match fullPrefix with
  | .all _ (.all _ f) => f
  | _ => .truth

def forwardBody : Formula := .imp (conj (.member 1 3) (.member 0 2))
  (.imp (graphFormula 6 2 3) (graphFormula 7 3 2))

def backwardBody : Formula := .imp (conj (.member 1 3) (.member 0 2))
  (.imp (graphFormula 7 3 2) (graphFormula 6 2 3))

/-- Guarded forward projection of the full-prefix invariant at names 2,3. -/
def point_forward : KDerivation (imp pointBody.encode forwardBody.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let X := member 0 2
  let Y := member 1 3
  let G := (graphFormula 6 2 3).encode
  let H := (graphFormula 7 3 2).encode
  let B := both (imp H (both X G)) (imp (both X G) H)
  let P := imp (both X Y) B
  let Γ := [G,both Y X,P]
  have hg : Context Γ G := Context.head _ _
  have hyx : Context Γ (both Y X) := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hx : Context Γ X := Context.conjunctionRight hyx
  have hy : Context Γ Y := Context.conjunctionLeft hyx
  have hb : Context Γ B := .mp (Context.conjunctionIntro hx hy) hp
  exact .mp (Context.conjunctionIntro hx hg) (Context.conjunctionRight hb)

/-- Guarded backward projection of the full-prefix invariant at names 2,3. -/
def point_backward : KDerivation (imp pointBody.encode backwardBody.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let X := member 0 2
  let Y := member 1 3
  let G := (graphFormula 6 2 3).encode
  let H := (graphFormula 7 3 2).encode
  let B := both (imp H (both X G)) (imp (both X G) H)
  let P := imp (both X Y) B
  let Γ := [H,both Y X,P]
  have hh : Context Γ H := Context.head _ _
  have hyx : Context Γ (both Y X) := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hx : Context Γ X := Context.conjunctionRight hyx
  have hy : Context Γ Y := Context.conjunctionLeft hyx
  have hb : Context Γ B := .mp (Context.conjunctionIntro hx hy) hp
  exact Context.conjunctionRight (.mp hh (Context.conjunctionLeft hb))

/-- Full-prefix invariant entails the exact forward restricted family. -/
def full_to_forward : KDerivation (imp fullPrefix.encode (Formula.all 3 forwardFormula).encode) := by
  have hlift := allCongr 2 (allCongr 3 point_forward)
  have hcomm := allCommute 2 3 forwardBody.encode
  exact compose hlift hcomm

/-- Full-prefix invariant entails the exact backward restricted family. -/
def full_to_backward : KDerivation (imp fullPrefix.encode (Formula.all 3 backwardFormula).encode) := by
  have hlift := allCongr 2 (allCongr 3 point_backward)
  have hcomm := allCommute 2 3 backwardBody.encode
  have halpha := (universalAlpha 2 4 backwardBody (by decide) (by decide) (by decide)).1
  have hsyntax : Formula.all 4 (replace 2 4 backwardBody) = backwardFormula := by decide
  change KDerivation (imp (allCode 2 backwardBody.encode)
    (Formula.all 4 (replace 2 4 backwardBody)).encode) at halpha
  rw [hsyntax] at halpha
  exact compose (compose hlift hcomm) (allCongr 3 halpha)

/-- Any represented graph satisfying the exact partial inverse on the full
input prefix satisfies the candidate's restricted inverse correspondence. -/
def full_prefix_to_restricted : KDerivation
    (imp fullPrefix.encode restrictedInverseMatrix.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hp : Context [fullPrefix.encode] fullPrefix.encode := Context.head [] _
  exact Context.conjunctionIntro (.mp hp (.closed full_to_forward))
    (.mp hp (.closed full_to_backward))

theorem full_prefix_to_restricted_certificate :
    theoremCode (certificate full_prefix_to_restricted) =
      imp fullPrefix.encode restrictedInverseMatrix.encode :=
  certificate_correct full_prefix_to_restricted

/-- Existentially package the same graph projection; its graph witness is
retained rather than replaced or chosen uniformly. -/
def full_prefix_exists_to_restricted_exists : KDerivation
    (imp (existsCode 7 fullPrefix.encode) (existsCode 7 restrictedInverseMatrix.encode)) :=
  existsCongr 7 full_prefix_to_restricted

theorem full_prefix_exists_to_restricted_exists_certificate :
    theoremCode (certificate full_prefix_exists_to_restricted_exists) =
      imp (existsCode 7 fullPrefix.encode) (existsCode 7 restrictedInverseMatrix.encode) :=
  certificate_correct full_prefix_exists_to_restricted_exists

end PASoundness.PAtoCompactPartialInverseFullProjection

#print axioms PASoundness.PAtoCompactPartialInverseFullProjection.full_prefix_to_restricted
#print axioms PASoundness.PAtoCompactPartialInverseFullProjection.full_prefix_to_restricted_certificate
#print axioms PASoundness.PAtoCompactPartialInverseFullProjection.full_prefix_exists_to_restricted_exists
#print axioms PASoundness.PAtoCompactPartialInverseFullProjection.full_prefix_exists_to_restricted_exists_certificate
