import PASoundness.PAtoCompactPAAddSuccSharedDiamondPack
import PASoundness.PAtoCompactTermGraphBinderRange

/-! Syntactic and finite-K vacuity facts for the nested shared-output
addition-successor diamond. These do not construct the diamond or term values. -/
namespace PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactPAAddSuccSharedDiamondPack
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Formula-level representation of the exact numeric-code diamond. -/
def diamondF (t u : Peano.Term) (e x y z sy q : Nat) : Formula :=
  andF (domainAt e sy) (andF (domainAt e z)
    (andF (domainAt e q) (andF (termGraph id t x e)
      (andF (termGraph id u y e) (andF (succAt e y sy)
        (andF (addAt e x y z) (andF (succAt e z q) (addAt e x sy q))))))))

theorem diamond_encode (t u : Peano.Term) (e x y z sy q : Nat) :
    (diamondF t u e x y z sy q).encode = diamond t u e x y z sy q := by
  simp [diamondF, diamond, andF, CompactNamed.Formula.not, Formula.encode, both, neg]

/-- Canonical nested witness order. Syntactic q+offset binders are distinct. -/
def closedDiamondF (t u : Peano.Term) (q : Nat) : Formula :=
  .ex (q+1) (.ex (q+2) (.ex (q+3) (.ex (q+4) (.ex q
    (diamondF t u (q+100) (q+1) (q+2) (q+3) (q+4) q)))))

theorem closedDiamond_encode (t u : Peano.Term) (q : Nat) :
    (closedDiamondF t u q).encode =
      existsCode (q+1) (existsCode (q+2) (existsCode (q+3) (existsCode (q+4)
        (existsCode q (diamond t u (q+100) (q+1) (q+2) (q+3) (q+4) q))))) := by
  simp only [closedDiamondF, Formula.encode, diamond_encode, existsCode]

/-- Every name strictly below e avoids all private binders of the diamond. -/
theorem diamond_not_binder (t u : Peano.Term) (e x y z sy q k : Nat) (hk : k < e) :
    k ∉ (diamondF t u e x y z sy q).binders := by
  intro h
  simp only [diamondF, andF_binders, Finset.mem_union] at h
  rcases h with h | h | h | h | h | h | h | h | h
  · have hh := domainAt_private e sy k h; omega
  · have hh := domainAt_private e z k h; omega
  · have hh := domainAt_private e q k h; omega
  · exact termGraph_below_not_binder id t x e k hk h
  · exact termGraph_below_not_binder id u y e k hk h
  · have hh := succAt_private e y sy k h; omega
  · have hh := addAt_private e x y z k h; omega
  · have hh := succAt_private e z q k h; omega
  · have hh := addAt_private e x sy q k h; omega

/-- A nested diamond is vacuous in each of its five bound labels. -/
theorem closedDiamond_bound_not_free (t u : Peano.Term) (q k : Nat)
    (hk : k = q ∨ k = q+1 ∨ k = q+2 ∨ k = q+3 ∨ k = q+4) :
    k ∉ (closedDiamondF t u q).free := by
  simp only [closedDiamondF, Formula.free, Finset.mem_erase, not_and]
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega

def closedDiamond_vacuity (t u : Peano.Term) (q k : Nat)
    (hk : k = q ∨ k = q+1 ∨ k = q+2 ∨ k = q+3 ∨ k = q+4) :
    KDerivation (imp (closedDiamondF t u q).encode
      (allCode k (closedDiamondF t u q).encode)) :=
  free_vacuity k (closedDiamondF t u q) (closedDiamond_bound_not_free t u q k hk)

/-- Guard names strictly below q are vacuous in each name at least q. -/
def guard_vacuity (g : Formula) (q k : Nat)
    (hg : ∀ a ∈ g.free, a < q) (hk : q ≤ k) :
    KDerivation (imp g.encode (allCode k g.encode)) := by
  apply free_vacuity
  intro h
  have := hg k h
  omega

/-- A source graph whose variables are below q is vacuous at any k≥q other
than its output label. No existence or functionality is assumed. -/
def graph_vacuity (t : Peano.Term) (q e out k : Nat)
    (ht : ∀ a ∈ t.varFinset, a < q) (hk : q ≤ k) (hko : k ≠ out) :
    KDerivation (imp (termGraph id t out e).encode
      (allCode k (termGraph id t out e).encode)) := by
  apply free_vacuity
  intro h
  have hf := termGraph_free_subset id t out e h
  rcases Finset.mem_union.mp hf with hf | hf
  · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hf
    have hh := ht a ha
    simp only [id_eq] at he
    omega
  · exact hko (Finset.mem_singleton.mp hf)

/-- Candidate guards are vacuous away from their named object. -/
def domain_vacuity (e a k : Nat) (hka : k ≠ a) :
    KDerivation (imp (domainAt e a).encode (allCode k (domainAt e a).encode)) := by
  apply free_vacuity
  intro h
  have hf := domainAt_free e a h
  exact hka (Finset.mem_singleton.mp hf)

/-- Addition relations are vacuous away from their three operand names. -/
def add_vacuity (e x y z k : Nat) (hkx : k ≠ x) (hky : k ≠ y) (hkz : k ≠ z) :
    KDerivation (imp (addAt e x y z).encode (allCode k (addAt e x y z).encode)) := by
  apply free_vacuity
  intro h
  have hf := addAt_free e x y z h
  simp [hkx, hky, hkz] at hf

end PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity.closedDiamond_vacuity
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity.graph_vacuity
