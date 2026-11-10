import PASoundness.PAtoCompactIsoInversePoint

/-! Pointwise inverse-order transfer retaining all four membership guards.
This assumes actual inverse-edge implications and the forward order instance;
it does not produce a graph, quantify the relation, or prove isomorphism
symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactIsoInverseGuard
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactIsoInversePoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Reorder the input/output domain guards and transfer the two reverse edges
to forward edges. All arguments are arbitrary literal formula codes. -/
def reverse_guarded (X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N : Nat) :
    KDerivation (imp (imp H₁ G₁) (imp (imp H₂ G₂)
      (imp (imp (both X₁ (both X₂ (both Y₁ (both Y₂ (both G₁ G₂)))))
        (both (imp M N) (imp N M)))
        (imp (both Y₁ (both Y₂ (both X₁ (both X₂ (both H₁ H₂)))))
          (both (imp N M) (imp M N)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let I₁ := imp H₁ G₁
  let I₂ := imp H₂ G₂
  let F := imp (both X₁ (both X₂ (both Y₁ (both Y₂ (both G₁ G₂)))))
    (both (imp M N) (imp N M))
  let R := both Y₁ (both Y₂ (both X₁ (both X₂ (both H₁ H₂))))
  let Γ := [R,F,I₂,I₁]
  have hr : Context Γ R := Context.head _ _
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hi₁ : Context Γ I₁ := .hypothesis (by simp [Γ])
  have hi₂ : Context Γ I₂ := .hypothesis (by simp [Γ])
  have hy₁ : Context Γ Y₁ := Context.conjunctionLeft hr
  have hy₂ : Context Γ Y₂ := Context.conjunctionLeft (Context.conjunctionRight hr)
  have hx₁ : Context Γ X₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hr))
  have hx₂ : Context Γ X₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr)))
  have hh : Context Γ (both H₁ H₂) :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr)))
  have hp : Context Γ (imp (both G₁ G₂) (both (imp M N) (imp N M))) := by
    apply Context.deduction
    have hg : Context (both G₁ G₂ :: Γ) (both G₁ G₂) := Context.head _ _
    have hxs : Context (both G₁ G₂ :: Γ) X₁ := Context.under hx₁ _
    have hxt : Context (both G₁ G₂ :: Γ) X₂ := Context.under hx₂ _
    have hys : Context (both G₁ G₂ :: Γ) Y₁ := Context.under hy₁ _
    have hyt : Context (both G₁ G₂ :: Γ) Y₂ := Context.under hy₂ _
    exact .mp (Context.conjunctionIntro hxs (Context.conjunctionIntro hxt
      (Context.conjunctionIntro hys (Context.conjunctionIntro hyt hg)))) (Context.under hf _)
  have hc := (.closed (reverse_pointwise G₁ G₂ H₁ H₂ M N) :
    Context Γ (imp I₁ (imp I₂ (imp (imp (both G₁ G₂) (both (imp M N) (imp N M)))
      (imp (both H₁ H₂) (both (imp N M) (imp M N)))))))
  exact .mp hh (.mp hp (.mp hi₂ (.mp hi₁ hc)))

theorem reverse_guarded_certificate (X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N : Nat) :
    theoremCode (certificate (reverse_guarded X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N)) =
      imp (imp H₁ G₁) (imp (imp H₂ G₂)
        (imp (imp (both X₁ (both X₂ (both Y₁ (both Y₂ (both G₁ G₂)))))
          (both (imp M N) (imp N M)))
          (imp (both Y₁ (both Y₂ (both X₁ (both X₂ (both H₁ H₂)))))
            (both (imp N M) (imp M N))))) :=
  certificate_correct (reverse_guarded X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N)

/-- The exact instantiated candidate graph and membership order. -/
def candidate_reverse_guarded : KDerivation
    (let X₁ := member 0 2; let X₂ := member 0 4
     let Y₁ := member 1 3; let Y₂ := member 1 5
     let G₁ := (graphFormula 6 2 3).encode; let G₂ := (graphFormula 6 4 5).encode
     let H₁ := (graphFormula 8 3 2).encode; let H₂ := (graphFormula 8 5 4).encode
     let M := member 4 2; let N := member 5 3
     imp (imp H₁ G₁) (imp (imp H₂ G₂)
       (imp (imp (both X₁ (both X₂ (both Y₁ (both Y₂ (both G₁ G₂)))))
         (both (imp M N) (imp N M)))
         (imp (both Y₁ (both Y₂ (both X₁ (both X₂ (both H₁ H₂)))))
           (both (imp N M) (imp M N)))))) :=
  reverse_guarded _ _ _ _ _ _ _ _ _ _

end PASoundness.PAtoCompactIsoInverseGuard

#print axioms PASoundness.PAtoCompactIsoInverseGuard.reverse_guarded
#print axioms PASoundness.PAtoCompactIsoInverseGuard.reverse_guarded_certificate
#print axioms PASoundness.PAtoCompactIsoInverseGuard.candidate_reverse_guarded
