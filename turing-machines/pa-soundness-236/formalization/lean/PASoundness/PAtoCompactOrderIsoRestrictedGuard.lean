import PASoundness.PAtoCompactIsoInverseGuard

/-! Guarded inverse-order transfer: the reverse-to-forward graph implications
are assumed only for displayed pairs in both input domains. This is a local
K proof, not a graph-construction or symmetry theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactOrderIsoRestrictedGuard
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactIsoInverseGuard
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Four domain facts in the reverse-order guard discharge the two restricted
inverse-edge premises; the remaining calculation is the exact guarded order
transfer. All arguments are literal compact codes. -/
def restricted_reverse_guarded (X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N : Nat) :
    KDerivation (imp (imp (both Y₁ X₁) (imp H₁ G₁))
      (imp (imp (both Y₂ X₂) (imp H₂ G₂))
        (imp (imp (both X₁ (both X₂ (both Y₁ (both Y₂ (both G₁ G₂)))))
          (both (imp M N) (imp N M)))
          (imp (both Y₁ (both Y₂ (both X₁ (both X₂ (both H₁ H₂)))))
            (both (imp N M) (imp M N)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let I₁ := imp (both Y₁ X₁) (imp H₁ G₁)
  let I₂ := imp (both Y₂ X₂) (imp H₂ G₂)
  let F := imp (both X₁ (both X₂ (both Y₁ (both Y₂ (both G₁ G₂)))))
    (both (imp M N) (imp N M))
  let R := both Y₁ (both Y₂ (both X₁ (both X₂ (both H₁ H₂))))
  let Γ := [R,F,I₂,I₁]
  have hr : Context Γ R := Context.head _ _
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hc₁ : Context Γ I₁ := .hypothesis (by simp [Γ])
  have hc₂ : Context Γ I₂ := .hypothesis (by simp [Γ])
  have hy₁ : Context Γ Y₁ := Context.conjunctionLeft hr
  have hy₂ : Context Γ Y₂ := Context.conjunctionLeft (Context.conjunctionRight hr)
  have hx₁ : Context Γ X₁ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hr))
  have hx₂ : Context Γ X₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr)))
  have hi₁ : Context Γ (imp H₁ G₁) := .mp (Context.conjunctionIntro hy₁ hx₁) hc₁
  have hi₂ : Context Γ (imp H₂ G₂) := .mp (Context.conjunctionIntro hy₂ hx₂) hc₂
  have ht := (.closed (reverse_guarded X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N) : Context Γ
    (imp (imp H₁ G₁) (imp (imp H₂ G₂) (imp F (imp R (both (imp N M) (imp M N)))))))
  exact .mp hr (.mp hf (.mp hi₂ (.mp hi₁ ht)))

theorem restricted_reverse_guarded_certificate (X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N : Nat) :
    theoremCode (certificate (restricted_reverse_guarded X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N)) =
      imp (imp (both Y₁ X₁) (imp H₁ G₁)) (imp (imp (both Y₂ X₂) (imp H₂ G₂))
        (imp (imp (both X₁ (both X₂ (both Y₁ (both Y₂ (both G₁ G₂)))))
          (both (imp M N) (imp N M)))
          (imp (both Y₁ (both Y₂ (both X₁ (both X₂ (both H₁ H₂)))))
            (both (imp N M) (imp M N))))) :=
  certificate_correct (restricted_reverse_guarded X₁ X₂ Y₁ Y₂ G₁ G₂ H₁ H₂ M N)

end PASoundness.PAtoCompactOrderIsoRestrictedGuard

#print axioms PASoundness.PAtoCompactOrderIsoRestrictedGuard.restricted_reverse_guarded
#print axioms PASoundness.PAtoCompactOrderIsoRestrictedGuard.restricted_reverse_guarded_certificate
