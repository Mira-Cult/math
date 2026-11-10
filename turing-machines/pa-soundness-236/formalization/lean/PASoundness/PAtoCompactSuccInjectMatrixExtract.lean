import PASoundness.PAtoCompactSuccGraphExtractSpareWitness
import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Projections from the actual equality matrix for PA successor injectivity.
This supplies two child-witness existentials and the successor-output
comparison, but proves neither quotient cancellation nor the PA axiom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccInjectMatrixExtract

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactSuccTermSpareAlpha PASoundness.PAtoCompactSuccGraphExtractSpareWitness

/-- The equality-value matrix with both original PA terms under successor.
The two result witnesses are b and b+1; their private allocations and the
equivalence allocation are the exact ordinary equality-frame layout. -/
def sourceMatrix (t u : Peano.Term) (b : Nat) : Formula :=
  matrix id (Peano.succ t) (Peano.succ u) b (b+1) (b+2)
    (b+2+termCost (Peano.succ t))
    (b+2+termCost (Peano.succ t)+termCost (Peano.succ u))

/-- Project the first successor's actual child-graph witness at spare a.
Every variable of t must lie below a, which places a above the source names. -/
def first_child (t u : Peano.Term) (b a : Nat)
    (ha : a < b) (hvars : ∀ x ∈ t.varFinset, x < a) :
    KDerivation (imp (sourceMatrix t u b).encode
      (existsCode a (spareBody id t b (b+2) a).encode)) := by
  let M := (sourceMatrix t u b).encode
  let T := (termGraph id (Peano.succ t) b (b+2)).encode
  have hgraph : KDerivation (imp M T) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hh := Context.head [] M
    have hm : Context [M] (both T
      (both (termGraph id (Peano.succ u) (b+1) (b+2+termCost (Peano.succ t))).encode
        (equivAt (b+2+termCost (Peano.succ t)+termCost (Peano.succ u)) b (b+1)).encode)) := by
      simpa [M,T,sourceMatrix,matrix,andF,CompactNamed.Formula.not,CompactNamed.Formula.encode,both,neg] using hh
    exact Context.conjunctionLeft hm
  have hext := extract_spare id t b (b+2) a (by omega) (by omega) (by omega)
    (by intro x hx; have := hvars x hx; simp only [id_eq]; omega)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [M]
  have ht : Context Γ T := .mp (Context.head [] M) (.closed hgraph)
  have he := Context.mp ht (.closed hext)
  exact Context.conjunctionRight he

/-- Project the second successor's actual child-graph witness at spare c. -/
def second_child (t u : Peano.Term) (b c : Nat)
    (hc : c < b) (hvars : ∀ x ∈ u.varFinset, x < c) :
    KDerivation (imp (sourceMatrix t u b).encode
      (existsCode c (spareBody id u (b+1) (b+2+termCost (Peano.succ t)) c).encode)) := by
  let M := (sourceMatrix t u b).encode
  let T := (termGraph id (Peano.succ u) (b+1) (b+2+termCost (Peano.succ t))).encode
  have hgraph : KDerivation (imp M T) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hh := Context.head [] M
    have hm : Context [M] (both (termGraph id (Peano.succ t) b (b+2)).encode
      (both T (equivAt (b+2+termCost (Peano.succ t)+termCost (Peano.succ u)) b (b+1)).encode)) := by
      simpa [M,T,sourceMatrix,matrix,andF,CompactNamed.Formula.not,CompactNamed.Formula.encode,both,neg] using hh
    exact Context.conjunctionLeft (Context.conjunctionRight hm)
  have hext := extract_spare id u (b+1) (b+2+termCost (Peano.succ t)) c
    (by omega) (by omega) (by omega)
    (by intro x hx; have := hvars x hx; simp only [id_eq]; omega)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [M]
  have ht : Context Γ T := .mp (Context.head [] M) (.closed hgraph)
  have he := Context.mp ht (.closed hext)
  exact Context.conjunctionRight he

/-- Project the successor-output comparison at the actual matrix allocation. -/
def output_equiv (t u : Peano.Term) (b : Nat) :
    KDerivation (imp (sourceMatrix t u b).encode
      (equivAt (b+2+termCost (Peano.succ t)+termCost (Peano.succ u)) b (b+1)).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let M := (sourceMatrix t u b).encode
  have hh := Context.head [] M
  have hm : Context [M] (both (termGraph id (Peano.succ t) b (b+2)).encode
    (both (termGraph id (Peano.succ u) (b+1) (b+2+termCost (Peano.succ t))).encode
      (equivAt (b+2+termCost (Peano.succ t)+termCost (Peano.succ u)) b (b+1)).encode)) := by
    simpa [M,sourceMatrix,matrix,andF,CompactNamed.Formula.not,CompactNamed.Formula.encode,both,neg] using hh
  exact Context.conjunctionRight (Context.conjunctionRight hm)

end PASoundness.PAtoCompactSuccInjectMatrixExtract

#print axioms PASoundness.PAtoCompactSuccInjectMatrixExtract.first_child
#print axioms PASoundness.PAtoCompactSuccInjectMatrixExtract.second_child
#print axioms PASoundness.PAtoCompactSuccInjectMatrixExtract.output_equiv
