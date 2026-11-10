import PASoundness.PAtoCompactFirstFactorDiamondBody
import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactFreeVacuity

/-! Named syntax, binder bounds, and bound-variable vacuity for the explicit
first-factor multiplication diamond. These facts do not construct witnesses. -/
namespace PASoundness.PAtoCompactFirstFactorDiamondVacuity

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFirstFactorDiamondBody

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The formula-level nine-condition diamond at explicit witness labels. -/
def diamondF (t u : Peano.Term) (e x y p sx q : Nat) : Formula :=
  andF (domainAt e sx) (andF (domainAt e p)
    (andF (domainAt e q) (andF (termGraph id t x e)
      (andF (termGraph id u y e) (andF (succAt e x sx)
        (andF (mulAt e x y p) (andF (addAt e p y q) (mulAt e sx y q))))))))

/-- The canonical allocated formula encodes the existing diamond exactly. -/
theorem diamond_encode (t u : Peano.Term) (q : Nat) :
    (diamondF t u (q+100) (q+1) (q+2) (q+3) (q+4) q).encode = diamond t u q := by
  simp [diamondF, diamond, andF, CompactNamed.Formula.not, Formula.encode, both, neg]

/-- The five syntactically distinct output and intermediate witness labels. -/
def closedDiamondF (t u : Peano.Term) (q : Nat) : Formula :=
  .ex (q+1) (.ex (q+2) (.ex (q+3) (.ex (q+4) (.ex q
    (diamondF t u (q+100) (q+1) (q+2) (q+3) (q+4) q)))))

theorem closedDiamond_encode (t u : Peano.Term) (q : Nat) :
    (closedDiamondF t u q).encode =
      existsCode (q+1) (existsCode (q+2) (existsCode (q+3) (existsCode (q+4)
        (existsCode q (diamond t u q))))) := by
  simp only [closedDiamondF, Formula.encode, diamond_encode, existsCode]

/-- Private binders of each conjunct are at least e, independently of its
free witness names. -/
theorem diamond_not_binder (t u : Peano.Term) (e x y p sx q k : Nat) (hk : k < e) :
    k ∉ (diamondF t u e x y p sx q).binders := by
  intro h
  simp only [diamondF, andF_binders, Finset.mem_union] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · have hh := domainAt_private e sx k h; omega
  · have hh := domainAt_private e p k h; omega
  · have hh := domainAt_private e q k h; omega
  · exact termGraph_below_not_binder id t x e k hk h
  · exact termGraph_below_not_binder id u y e k hk h
  · have hh := succAt_private e x sx k h; omega
  · have hh := mulAt_private e x y p k h; omega
  · have hh := addAt_private e p y q k h; omega
  · have hh := mulAt_private e sx y q k h; omega

/-- Each existentially bound witness label is absent from the closed
package's free-name set, including when source terms contain that name. -/
theorem closedDiamond_bound_not_free (t u : Peano.Term) (q k : Nat)
    (hk : k = q ∨ k = q+1 ∨ k = q+2 ∨ k = q+3 ∨ k = q+4) :
    k ∉ (closedDiamondF t u q).free := by
  simp only [closedDiamondF, Formula.free, Finset.mem_erase, not_and]
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega

/-- Finite-K vacuity derived from the bound-name fact. -/
def closedDiamond_vacuity (t u : Peano.Term) (q k : Nat)
    (hk : k = q ∨ k = q+1 ∨ k = q+2 ∨ k = q+3 ∨ k = q+4) :
    KDerivation (imp (closedDiamondF t u q).encode
      (allCode k (closedDiamondF t u q).encode)) :=
  free_vacuity k (closedDiamondF t u q) (closedDiamond_bound_not_free t u q k hk)

end PASoundness.PAtoCompactFirstFactorDiamondVacuity

#print axioms PASoundness.PAtoCompactFirstFactorDiamondVacuity.diamondF
#print axioms PASoundness.PAtoCompactFirstFactorDiamondVacuity.diamond_encode
#print axioms PASoundness.PAtoCompactFirstFactorDiamondVacuity.closedDiamondF
#print axioms PASoundness.PAtoCompactFirstFactorDiamondVacuity.closedDiamond_encode
#print axioms PASoundness.PAtoCompactFirstFactorDiamondVacuity.diamond_not_binder
#print axioms PASoundness.PAtoCompactFirstFactorDiamondVacuity.closedDiamond_bound_not_free
#print axioms PASoundness.PAtoCompactFirstFactorDiamondVacuity.closedDiamond_vacuity
