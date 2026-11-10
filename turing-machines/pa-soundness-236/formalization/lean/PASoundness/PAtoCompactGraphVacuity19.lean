import PASoundness.PAtoCompactGraphWitnessRules

/-! K vacuity for the graph's bound pair-witness name. This is a syntactic
alpha-conversion and does not assert graph existence or quotient properties. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGraphVacuity19
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactGraphWitnessRules

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The name 19 is bound by the literal graph existential. K proves it is
vacuous in the full graph formula, by renaming that witness to a genuinely
fresh name. No restrictions on the numeric parameters are needed for the
syntactic statement; the intended three-parameter graph reading separately
requires avoiding the internal binder labels. -/
def graph_vacuity_19 (g u v : Nat) :
    KDerivation (imp (graphFormula g u v).encode (allCode 19 (graphFormula g u v).encode)) := by
  let f := graphBody g u v
  let w := max 19 (f.names.sup id) + 1
  have h19w : 19 ≠ w := by dsimp [w]; omega
  have hbind : 19 ∉ f.binders := by
    change 19 ∉ ({20, 21, 22} : Finset Nat)
    decide
  have hwfresh : w ∉ f.names := by
    intro hw
    have hs : w ≤ f.names.sup id := Finset.le_sup (f := id) hw
    dsimp [w] at hs
    omega
  let G : CompactNamed.Formula := .ex w (CompactNamed.replace 19 w f)
  have hreplace : 19 ∉ (CompactNamed.replace 19 w f).names :=
    CompactNamed.replace_avoids 19 w f h19w hbind
  have hfresh : 19 ∉ G.names := by
    simp [G, CompactNamed.Formula.names, h19w, hreplace]
  have ha := CompactNamed.existentialAlpha 19 w f h19w hbind hwfresh
  have hv := G.vacuity 19 hfresh
  have h : KDerivation (imp (existsCode 19 f.encode)
      (allCode 19 (existsCode 19 f.encode))) :=
    compose ha.1 (compose hv (allCongr 19 ha.2))
  simpa only [f, ← graph_code] using h

theorem graph_vacuity_19_certificate (g u v : Nat) :
    theoremCode (certificate (graph_vacuity_19 g u v)) =
      imp (graphFormula g u v).encode (allCode 19 (graphFormula g u v).encode) :=
  certificate_correct (graph_vacuity_19 g u v)

end PASoundness.PAtoCompactGraphVacuity19

#print axioms PASoundness.PAtoCompactGraphVacuity19.graph_vacuity_19
#print axioms PASoundness.PAtoCompactGraphVacuity19.graph_vacuity_19_certificate
