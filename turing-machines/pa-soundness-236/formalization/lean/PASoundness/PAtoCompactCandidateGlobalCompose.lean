import PASoundness.CompactDerivations

/-! Proof-rule assembly for a candidate successor induction argument. Every
successor, schema, and vacuity input is itself an explicit finite K derivation;
this module proves no candidate existence, global schema, or PA translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateGlobalCompose
open PASoundness.CompactProof PASoundness.CompactDerivations
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Assemble a conditional global instance from derivations of successor
existence, base vacuity, global-step instantiation, conclusion vacuity, and
the displayed local implication. This is a proof constructor, not an
assertion that its arguments exist. -/
def global_from_components (y D B S W L T : Nat)
    (hsucc : KDerivation (imp D (existsCode y W)))
    (hbase : KDerivation (imp B (allCode y B)))
    (hstep : KDerivation (imp S (allCode y L)))
    (hresult : KDerivation (imp T (allCode y T)))
    (hlocal : KDerivation (imp B (imp L (imp W T)))) :
    KDerivation (imp D (imp B (imp S T))) := by
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
  have hallL : Context Γ (allCode y L) := .mp hs (.closed hstep)
  have hall : Context Γ (allCode y (imp B (imp L (imp W T)))) :=
    .closed (.generalize y hlocal)
  have hpoint : Context Γ (allCode y (imp W T)) :=
    Context.allMP hallL (Context.allMP hallB hall)
  exact Context.existsElim hresult hpoint hex

theorem global_from_components_certificate (y D B S W L T : Nat)
    (hsucc : KDerivation (imp D (existsCode y W)))
    (hbase : KDerivation (imp B (allCode y B)))
    (hstep : KDerivation (imp S (allCode y L)))
    (hresult : KDerivation (imp T (allCode y T)))
    (hlocal : KDerivation (imp B (imp L (imp W T)))) :
    theoremCode (certificate (global_from_components y D B S W L T
      hsucc hbase hstep hresult hlocal)) = imp D (imp B (imp S T)) :=
  certificate_correct (global_from_components y D B S W L T hsucc hbase hstep hresult hlocal)

end PASoundness.PAtoCompactCandidateGlobalCompose

#print axioms PASoundness.PAtoCompactCandidateGlobalCompose.global_from_components
#print axioms PASoundness.PAtoCompactCandidateGlobalCompose.global_from_components_certificate
