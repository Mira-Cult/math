import PASoundness.CompactDerivations

/-! Finite K proof composition with the step schema restricted to the
successor witness. All inputs are explicit K derivations; this does not prove
candidate existence, a PA induction instance, or any input schema. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateRestrictedCompose
open PASoundness.CompactProof PASoundness.CompactDerivations
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Assemble a conditional induction instance when the global step schema is
available only under a condition that each successor witness implies. -/
def restricted_from_components (y D B S W C L T : Nat)
    (hsucc : KDerivation (imp D (existsCode y W)))
    (hbase : KDerivation (imp B (allCode y B)))
    (hstep : KDerivation (imp S (allCode y (imp C L))))
    (hresult : KDerivation (imp T (allCode y T)))
    (hlocal : KDerivation (imp B (imp L (imp W T))))
    (hWc : KDerivation (imp W C)) :
    KDerivation (imp D (imp B (imp S T))) := by
  have hrestricted : KDerivation (imp B (imp (imp C L) (imp W T))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [W, imp C L, B]
    have hw : Context Γ W := .hypothesis (by simp [Γ])
    have hcl : Context Γ (imp C L) := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hc : Context Γ C := .mp hw (.closed hWc)
    have hl : Context Γ L := .mp hc hcl
    exact .mp hw (.mp hl (.mp hb (.closed hlocal)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [S,B,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hex : Context Γ (existsCode y W) := .mp hd (.closed hsucc)
  have hallB : Context Γ (allCode y B) := .mp hb (.closed hbase)
  have hallCL : Context Γ (allCode y (imp C L)) := .mp hs (.closed hstep)
  have hall : Context Γ (allCode y (imp B (imp (imp C L) (imp W T)))) :=
    .closed (.generalize y hrestricted)
  have hpoint : Context Γ (allCode y (imp W T)) :=
    Context.allMP hallCL (Context.allMP hallB hall)
  exact Context.existsElim hresult hpoint hex

theorem restricted_from_components_certificate (y D B S W C L T : Nat)
    (hsucc : KDerivation (imp D (existsCode y W)))
    (hbase : KDerivation (imp B (allCode y B)))
    (hstep : KDerivation (imp S (allCode y (imp C L))))
    (hresult : KDerivation (imp T (allCode y T)))
    (hlocal : KDerivation (imp B (imp L (imp W T))))
    (hWc : KDerivation (imp W C)) :
    theoremCode (certificate (restricted_from_components y D B S W C L T
      hsucc hbase hstep hresult hlocal hWc)) = imp D (imp B (imp S T)) :=
  certificate_correct (restricted_from_components y D B S W C L T
    hsucc hbase hstep hresult hlocal hWc)

end PASoundness.PAtoCompactCandidateRestrictedCompose

#print axioms PASoundness.PAtoCompactCandidateRestrictedCompose.restricted_from_components
#print axioms PASoundness.PAtoCompactCandidateRestrictedCompose.restricted_from_components_certificate
