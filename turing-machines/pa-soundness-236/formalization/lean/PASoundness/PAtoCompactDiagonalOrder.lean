import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor

/-! Literal K derivation of the exact isomorphism order clause from an
explicit uniform diagonal-graph soundness hypothesis. This module does not
construct a graph, prove the hypothesis, establish bijectivity or reflexivity,
or use semantic soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism

/-- Every represented graph edge has equal endpoints. The names 28 and 29
are chosen disjoint from the literal order clause's four test binders. -/
def diagonalSound : Formula :=
  .all 28 (.all 29 (.imp (graphFormula 6 28 29) (.equal 28 29)))

/-- The uniform hypothesis at the first order-clause graph occurrence. -/
def sound_23 : KDerivation (imp diagonalSound.encode
    (imp (graphFormula 6 2 3).encode (equal 2 3))) := by
  let f : Formula := .imp (graphFormula 6 28 29) (.equal 28 29)
  let f2 : Formula := .imp (graphFormula 6 2 29) (.equal 2 29)
  have h28 := CompactNamed.universalInstance 28 2 (.all 29 f)
    (by decide) (by decide) (by decide)
  have h28syntax : CompactNamed.replace 28 2 (.all 29 f) = .all 29 f2 := by decide
  rw [h28syntax] at h28
  have h29 := CompactNamed.universalInstance 29 3 f2
    (by decide) (by decide) (by decide)
  have h29syntax : CompactNamed.replace 29 3 f2 =
      .imp (graphFormula 6 2 3) (.equal 2 3) := by decide
  rw [h29syntax] at h29
  exact compose h28 h29

/-- The uniform hypothesis at the second order-clause graph occurrence. -/
def sound_45 : KDerivation (imp diagonalSound.encode
    (imp (graphFormula 6 4 5).encode (equal 4 5))) := by
  let f : Formula := .imp (graphFormula 6 28 29) (.equal 28 29)
  let f4 : Formula := .imp (graphFormula 6 4 29) (.equal 4 29)
  have h28 := CompactNamed.universalInstance 28 4 (.all 29 f)
    (by decide) (by decide) (by decide)
  have h28syntax : CompactNamed.replace 28 4 (.all 29 f) = .all 29 f4 := by decide
  rw [h28syntax] at h28
  have h29 := CompactNamed.universalInstance 29 5 f4
    (by decide) (by decide) (by decide)
  have h29syntax : CompactNamed.replace 29 5 f4 =
      .imp (graphFormula 6 4 5) (.equal 4 5) := by decide
  rw [h29syntax] at h29
  exact compose h28 h29

/-- A single-context generalization from the uniform graph-soundness code. -/
def generalize_sound (x A : Nat) (hx : x ∉ diagonalSound.names)
    (h : Context [diagonalSound.encode] A) :
    Context [diagonalSound.encode] (allCode x A) :=
  Context.generalize x (by
    intro z hz
    have he : z = diagonalSound.encode := by simpa using hz
    subst z
    exact diagonalSound.vacuity x hx) h

/-- Diagonal edge soundness forces the exact order-preservation clause. -/
def diagonal_order : KDerivation (imp diagonalSound.encode orderFormula.encode) := by
  let G := diagonalSound.encode
  let G23 := (graphFormula 6 2 3).encode
  let G45 := (graphFormula 6 4 5).encode
  let A := both (member 0 2) (both (member 0 4) (both (member 1 3)
    (both (member 1 5) (both G23 G45))))
  let L := member 4 2
  let R := member 5 3
  have hpoint : Context [G] (imp A (both (imp L R) (imp R L))) := by
    apply Context.deduction
    let Γ := [A,G]
    have ha : Context Γ A := Context.head _ _
    have hg : Context Γ G := .hypothesis (by simp [Γ])
    have hg23 : Context Γ G23 := Context.conjunctionLeft
      (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ha))))
    have hg45 : Context Γ G45 := Context.conjunctionRight
      (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ha))))
    have he23 : Context Γ (equal 2 3) := .mp hg23 (.mp hg (.closed sound_23))
    have he45 : Context Γ (equal 4 5) := .mp hg45 (.mp hg (.closed sound_45))
    have hforward : Context Γ (imp L R) := by
      apply Context.deduction
      have hl : Context (L :: Γ) L := Context.head Γ L
      have hm : Context (L :: Γ) (member 5 2) :=
        .mp hl (.mp (Context.under he45 L) (.closed (memberLeftEquality 4 5 2)))
      exact .mp (Context.under he23 L) (.mp hm (.closed (memberRightEquality 5 2 3)))
    have hreverse : Context Γ (imp R L) := by
      apply Context.deduction
      have hr : Context (R :: Γ) R := Context.head Γ R
      have hm : Context (R :: Γ) (member 4 3) :=
        .mp hr (.mp (Context.eqSymm (Context.under he45 R)) (.closed (memberLeftEquality 5 4 3)))
      exact .mp (Context.eqSymm (Context.under he23 R)) (.mp hm (.closed (memberRightEquality 4 3 2)))
    exact Context.conjunctionIntro hforward hreverse
  have h5 := generalize_sound 5 _ (by decide) hpoint
  have h3 := generalize_sound 3 _ (by decide) h5
  have h4 := generalize_sound 4 _ (by decide) h3
  have h2 := generalize_sound 2 _ (by decide) h4
  apply Context.closeEmpty
  apply Context.deduction
  change Context [G] (allCode 2 (allCode 4 (allCode 3 (allCode 5
    (imp A (both (imp L R) (imp R L)))))))
  exact h2

theorem diagonal_order_certificate : theoremCode (certificate diagonal_order) =
    imp diagonalSound.encode orderFormula.encode := certificate_correct diagonal_order

end PASoundness.PAtoCompactDiagonalOrder

#print axioms PASoundness.PAtoCompactDiagonalOrder.diagonal_order
#print axioms PASoundness.PAtoCompactDiagonalOrder.diagonal_order_certificate
