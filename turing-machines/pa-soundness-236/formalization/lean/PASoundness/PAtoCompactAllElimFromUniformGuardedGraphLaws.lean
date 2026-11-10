import PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
import PASoundness.PAtoCompactUnarySubstitutionReduce
import PASoundness.PAtoCompactAllTermsTotalityClosed
import PASoundness.PAtoCompactGuardedOutputFormula
import PASoundness.PAtoCompactGuardedTwoLogical

/-! Construct guarded universal elimination and equality substitution from
uniform guard-conditioned finite K term-graph laws. Those output-transport and
functionality families remain explicit proof-data inputs. Graph existence is
used only when the eliminated variable occurs in the source formula. -/

namespace PASoundness.PAtoCompactAllElimFromUniformGuardedGraphLaws

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactUnaryGuardedCanonical PASoundness.PAtoCompactUnarySubstitutionReduce
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactGuardedOutputFormula PASoundness.PAtoCompactEqSubstFromUniformGraphLaws

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Every guarded universal-elimination axiom follows from the explicit
uniform guarded K graph-output transport and functionality proof families. -/
noncomputable def allElim (output : UniformOutput) (functional : UniformFunctionality)
    (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  apply allElim_of_variable_graph φ x t
  · intro hx
    apply PAtoCompactAllTermsTotalityClosed.canonical_total id (allElimFormula φ x t) t
    intro a ha
    simpa only [id_eq] using termVars_in_axiom_of_occurs φ x t hx ha
  · intro hx
    let A := allElimFormula φ x t
    let q := outputName A
    let d := allocatorBase A
    let g := guardFormula A
    have hcover : ∀ a ∈ t.varFinset, a ∈ A.freeVarFinset := by
      intro a ha
      exact termVars_in_axiom_of_occurs φ x t hx ha
    have hlt : ∀ a ∈ t.varFinset, a < guardBase A := by
      intro a ha
      have hle : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) (hcover a ha)
      unfold guardBase
      omega
    have hqd : q < d := by dsimp [q, d, allocatorBase]; omega
    have htd : ∀ a ∈ t.varFinset, a < d := by
      intro a ha
      have h := hlt a ha
      dsimp [d, allocatorBase, outputName]
      omega
    have hdom (a : Nat) (ha : a ∈ t.varFinset) :
        KDerivation (imp g.encode (domainAt d a).encode) := by
      have h := PASoundness.PAtoCompactGuardedEqualityReflexivity.guardFormula_projection
        A a (hcover a ha)
      exact compose h (domainAt_transport (guardBase A) d a (by have := hlt a ha; omega)
        (by have := htd a ha; omega))
    have halign := (formula_replacement_substitution g t x q d hqd htd hdom
      (output g t) (functional g t) φ).1
    change KDerivation (imp g.encode (imp (termGraph id t q d).encode
      (imp (code (FOL.substAt φ x (.var q))) (code (FOL.substAt φ x t)))))
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let G := (termGraph id t q d).encode
    let V := code (FOL.substAt φ x (.var q))
    let Γ := [V, G, g.encode]
    have hv : Context Γ V := Context.head _ _
    have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
    have hG : Context Γ G := .hypothesis (by simp [Γ])
    have hret : Context Γ (retained g t q d).encode := by
      have hh := Context.conjunctionIntro hg hG
      simpa [retained, andF, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, both, neg, G] using hh
    exact .mp hv (.mp hret (.closed halign))

theorem allElim_certificate (output : UniformOutput) (functional : UniformFunctionality)
    (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    theoremCode (certificate (allElim output functional φ x t)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

/-- The same two explicit graph-law families supply both remaining logical
handlers; guarded equality reflexivity is supplied by the existing compiler. -/
noncomputable def twoLogical (output : UniformOutput) (functional : UniformFunctionality) :
    PAtoCompactGuardedTwoLogical.TwoLogical where
  allElim := fun φ x t => by
    simpa only [allElimFormula] using allElim output functional φ x t
  eqSubst := PAtoCompactEqSubstFromUniformGraphLaws.handler output functional

end PASoundness.PAtoCompactAllElimFromUniformGuardedGraphLaws

#print axioms PASoundness.PAtoCompactAllElimFromUniformGuardedGraphLaws.allElim
#print axioms PASoundness.PAtoCompactAllElimFromUniformGuardedGraphLaws.allElim_certificate
#print axioms PASoundness.PAtoCompactAllElimFromUniformGuardedGraphLaws.twoLogical
