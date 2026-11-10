import PASoundness.PAtoCompactGuardedEqualityMatrixFormulaSubst
import PASoundness.PAtoCompactEqSubstFrameElimination
import PASoundness.PAtoCompactEqSubstWitnessCoverage

/-! A conditional finite K construction of the full guarded PA equality-
substitution axiom. Guarded output transport and guarded functionality for
both replacement-term graphs remain explicit proof-data inputs. The fresh
frame, guard projections and equality-witness elimination are constructed. -/

namespace PASoundness.PAtoCompactEqSubstGuardedGraphReduction

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactGuardedEqualityMatrixFormulaSubst PASoundness.PAtoCompactEqSubstFrameElimination
open PASoundness.PAtoCompactEqSubstScopedReduction PASoundness.PAtoCompactEqSubstWitnessCoverage

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The exact guarded equality-substitution axiom for arbitrary PA formulas,
conditional on finite K output transport and functionality for each of the
two replacement-term graphs under this axiom's actual guard. -/
noncomputable def eqSubst_of_guarded_graph_laws
    (φ : Peano.Formula) (x : Nat) (t u : Peano.Term)
    (htout : GuardedOutputTransport (guardFormula (axiomFormula φ x t u)) t)
    (htfunc : GuardFunctionality (guardFormula (axiomFormula φ x t u)) t)
    (huout : GuardedOutputTransport (guardFormula (axiomFormula φ x t u)) u)
    (hufunc : GuardFunctionality (guardFormula (axiomFormula φ x t u)) u) :
    KDerivation (guardedCode (axiomFormula φ x t u)) := by
  let A := axiomFormula φ x t u
  let G := guardFormula A
  let S := formula (FOL.substAt φ x t)
  let T := formula (FOL.substAt φ x u)
  let b := max (guardBase A) (max (G.free.sup id) (max (S.free.sup id) (T.free.sup id))) + 1
  have hbase : guardBase A < b := by dsimp [b]; omega
  have hA : ∀ a ∈ A.freeVarFinset, a < guardBase A := by
    intro a ha
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) ha
    unfold guardBase
    omega
  have ht : ∀ a ∈ t.varFinset, a < b := by
    intro a ha
    have hc : a ∈ A.freeVarFinset := by
      simpa only [A, id_eq] using left_coverage φ x t u a ha
    have hh := hA a hc
    omega
  have hu : ∀ a ∈ u.varFinset, a < b := by
    intro a ha
    have hc : a ∈ A.freeVarFinset := by
      simpa only [A, id_eq] using right_coverage φ x t u a ha
    have hh := hA a hc
    omega
  have hg : ∀ a ∈ G.free, a < b := by
    intro a ha
    have hh : a ≤ G.free.sup id := Finset.le_sup (f := id) ha
    dsimp [b]
    omega
  have hs : ∀ a ∈ S.free, a < b := by
    intro a ha
    have hh : a ≤ S.free.sup id := Finset.le_sup (f := id) ha
    dsimp [b]
    omega
  have hT : ∀ a ∈ T.free, a < b := by
    intro a ha
    have hh : a ≤ T.free.sup id := Finset.le_sup (f := id) ha
    dsimp [b]
    omega
  have htdom : ∀ a ∈ t.varFinset,
      KDerivation (imp G.encode (domainAt (b+2) a).encode) := by
    intro a ha
    have hc : a ∈ A.freeVarFinset := by
      simpa only [A, id_eq] using left_coverage φ x t u a ha
    have ha0 := hA a hc
    have hab := ht a ha
    exact compose (left_guard φ x t u a ha)
      (domainAt_transport (guardBase A) (b+2) a (by omega) (by omega))
  have hudom : ∀ a ∈ u.varFinset,
      KDerivation (imp G.encode (domainAt (b+2) a).encode) := by
    intro a ha
    have hc : a ∈ A.freeVarFinset := by
      simpa only [A, id_eq] using right_coverage φ x t u a ha
    have ha0 := hA a hc
    have hab := hu a ha
    exact compose (right_guard φ x t u a ha)
      (domainAt_transport (guardBase A) (b+2) a (by omega) (by omega))
  have hpoint := matrix_formula_substitution G t u φ x b (b+1)
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost u) (b+2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro a ha; have := ht a ha; omega)
    (by intro a ha; have := ht a ha; omega)
    (by intro a ha; have := hu a ha; omega)
    (by intro a ha; have := hu a ha; omega)
    (by intro a ha; have := hg a ha; omega)
    htdom hudom htout htfunc huout hufunc
  apply guarded_of_matrix φ x t u b ht hu
    (by simpa only [A, G, axiomFormula] using hg)
    (by simpa only [S] using hs)
    (by simpa only [T] using hT)
  simpa only [A, G, axiomFormula] using hpoint

theorem eqSubst_of_guarded_graph_laws_certificate
    (φ : Peano.Formula) (x : Nat) (t u : Peano.Term)
    (htout : GuardedOutputTransport (guardFormula (axiomFormula φ x t u)) t)
    (htfunc : GuardFunctionality (guardFormula (axiomFormula φ x t u)) t)
    (huout : GuardedOutputTransport (guardFormula (axiomFormula φ x t u)) u)
    (hufunc : GuardFunctionality (guardFormula (axiomFormula φ x t u)) u) :
    theoremCode (certificate (eqSubst_of_guarded_graph_laws φ x t u htout htfunc huout hufunc)) =
      guardedCode (axiomFormula φ x t u) := certificate_correct _

end PASoundness.PAtoCompactEqSubstGuardedGraphReduction

#print axioms PASoundness.PAtoCompactEqSubstGuardedGraphReduction.eqSubst_of_guarded_graph_laws
#print axioms PASoundness.PAtoCompactEqSubstGuardedGraphReduction.eqSubst_of_guarded_graph_laws_certificate
