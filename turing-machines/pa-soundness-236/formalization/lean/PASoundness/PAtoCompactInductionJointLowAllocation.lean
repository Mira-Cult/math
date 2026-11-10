import PASoundness.PAtoCompactInductionScopeLowNames
import PASoundness.PAtoCompactGuardedAllElim

/-! A source-dependent low-name allocation for PA induction. The three names
are below the actual universal-instantiation label but above the source ceiling;
this records only syntactic freshness and does not discharge the full engine. -/
namespace PASoundness.PAtoCompactInductionJointLowAllocation
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactGuardedAllImp PASoundness.PAtoCompactGuardedAllImpAlignment PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactInductionScopeLowNames

/-- Source names and the universal ceiling lie strictly below this bound. -/
def lowBound (φ : Peano.Formula) (x : Nat) : Nat :=
  max (universalCeiling φ x)
    (max ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id)) + 1

/-- The low point, predecessor, and base witness have the required source and
scoped-formula freshness. The actual instance binder is exactly m+1. -/
theorem low_allocation (φ : Peano.Formula) (x : Nat) :
    let N := lowBound φ x
    let v := N+1
    let point := N+2
    let m := N+100
    let t := instanceBinder φ x m
    t = N+101 ∧ topName x φ < point ∧ point < t ∧ v < t ∧ m < t ∧
    point ∉ (originalChild φ x).names ∧
    point ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    v ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    m ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    point ∉ (scopeAt φ x t).names ∧
    v ∉ (scopeAt φ x t).names ∧ m ∉ (scopeAt φ x t).names ∧
    t ∉ (scopeAt φ x t).binders := by
  dsimp only
  let N := lowBound φ x
  let v := N+1
  let point := N+2
  let m := N+100
  let t := instanceBinder φ x m
  have hc : universalCeiling φ x < N := by
    dsimp [N, lowBound]
    have h := Nat.le_max_left (universalCeiling φ x)
      (max ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id))
    omega
  have hn : (originalChild φ x).names.sup id < N := by
    dsimp [N, lowBound]
    have h1 := Nat.le_max_left ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id)
    have h2 := Nat.le_max_right (universalCeiling φ x)
      (max ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id))
    omega
  have hi : (Peano.inductionAxiom φ x).freeVarFinset.sup id < N := by
    dsimp [N, lowBound]
    have h1 := Nat.le_max_right ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id)
    have h2 := Nat.le_max_right (universalCeiling φ x)
      (max ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id))
    omega
  have heq : t = N+101 := by
    dsimp [t, instanceBinder, m]
    omega
  have htop : topName x φ < N := by
    have h := ceiling_top φ x
    omega
  have hsrc : ∀ n, N ≤ n → n ∉ (allAtBody x φ).freeVarFinset := by
    intro n hn' hmem
    have hh := free_lt_scopeBase (FOL.allAt x φ) Fin.elim0 n (by
      change n ∈ (allAtBody x φ).freeVarFinset
      exact hmem)
    change n < topName x φ at hh
    omega
  have hp : point ∉ (originalChild φ x).names := by
    intro hp'
    have hh : point ≤ (originalChild φ x).names.sup id := Finset.le_sup (f := id) hp'
    dsimp [point] at *
    omega
  have hI : ∀ n, N ≤ n → n ∉ (Peano.inductionAxiom φ x).freeVarFinset := by
    intro n hn' hn''
    have hh : n ≤ (Peano.inductionAxiom φ x).freeVarFinset.sup id := Finset.le_sup (f := id) hn''
    omega
  have hp' : point ∉ (scopeAt φ x t).names := scope_low_name_fresh φ x t point (by dsimp [point]; omega) (hsrc point (by dsimp [point]; omega))
  have hv' : v ∉ (scopeAt φ x t).names := scope_low_name_fresh φ x t v (by dsimp [v]; omega) (hsrc v (by dsimp [v]; omega))
  have hm' : m ∉ (scopeAt φ x t).names := scope_low_name_fresh φ x t m (by dsimp [m]; omega) (hsrc m (by dsimp [m]; omega))
  have ht' := scope_active_not_binder φ x t
  dsimp only [N, v, point, m, t] at *
  exact ⟨heq, by omega, by omega, by omega, by omega, hp, hI _ (by omega),
    hI _ (by omega), hI _ (by omega), hp', hv', hm', ht'⟩

end PASoundness.PAtoCompactInductionJointLowAllocation

#print axioms PASoundness.PAtoCompactInductionJointLowAllocation.low_allocation
