import PASoundness.PAtoCompactGuardAssembly
import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Assemble the original parameter guard together with one additional
candidate-domain condition into the guard for a PA formula mentioning that
variable. This is finite K proof data and does not assume standard soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionAugmentedGuard
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardAssembly PASoundness.PAtoCompactVacuousEqualityAlignment

/-- The guard of this PA formula covers the free variables of ψ and y. -/
def augmented (ψ : Peano.Formula) (y : Nat) : Peano.Formula :=
  ((.var y : Peano.Term).equal (.var y)).imp ψ

theorem augmented_free (ψ : Peano.Formula) (y : Nat) :
    (augmented ψ y).freeVarFinset = {y} ∪ ψ.freeVarFinset := by
  simp [augmented, BoundedFormula.freeVarFinset, eq_free, Term.varFinset]

/-- A singleton guard is derivable from its one candidate condition. -/
def singleton_guard (base y : Nat) :
    KDerivation (imp (domainAt base y).encode (guardList base [y]).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(domainAt base y).encode]
  have hy : Context Γ (domainAt base y).encode := Context.head [] _
  have ht : Context Γ (guardList base []).encode := .closed (by simpa [guardList, CompactNamed.Formula.encode] using KDerivation.truth)
  have hh := Context.conjunctionIntro hy ht
  simpa [guardList, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not, both, neg] using hh

/-- The original guard and the explicit domain guard yield the augmented
guard, even if y is already free in ψ. The bound prevents target-name capture
in the supplied domain block. -/
def augmented_guard (ψ : Peano.Formula) (y base : Nat) (hy : y < base + 32) :
    KDerivation (imp (guardFormula ψ).encode (imp (domainAt base y).encode
      (guardFormula (augmented ψ y)).encode)) := by
  let xs := ψ.freeVarFinset.sort (· ≤ ·)
  let zs := (augmented ψ y).freeVarFinset.sort (· ≤ ·)
  have hxs : ∀ v ∈ xs, v < guardBase ψ + 32 := by
    intro v hv
    have hm : v ∈ ψ.freeVarFinset := (Finset.mem_sort (· ≤ ·)).mp hv
    have hh : v ≤ ψ.freeVarFinset.sup id := Finset.le_sup (f := id) hm
    unfold guardBase
    omega
  have hys : ∀ v ∈ [y], v < base + 32 := by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; subst v; exact hy
  have hzs : ∀ v ∈ zs, v < guardBase (augmented ψ y) + 32 := by
    intro v hv
    have hm : v ∈ (augmented ψ y).freeVarFinset := (Finset.mem_sort (· ≤ ·)).mp hv
    have hh : v ≤ (augmented ψ y).freeVarFinset.sup id := Finset.le_sup (f := id) hm
    unfold guardBase
    omega
  have hcover : ∀ v ∈ zs, v ∈ xs ∨ v ∈ [y] := by
    intro v hv
    have hm : v ∈ (augmented ψ y).freeVarFinset := (Finset.mem_sort (· ≤ ·)).mp hv
    rw [augmented_free] at hm
    rcases Finset.mem_union.mp hm with h | h
    · right; simpa using h
    · left; exact (Finset.mem_sort (· ≤ ·)).mpr h
  have hc := guardList_combine (guardBase ψ) base (guardBase (augmented ψ y)) xs [y] zs hxs hys hzs hcover
  have hs := singleton_guard base y
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt base y).encode, (guardFormula ψ).encode]
  have hd : Context Γ (domainAt base y).encode := Context.head _ _
  have hg : Context Γ (guardFormula ψ).encode := .hypothesis (by simp [Γ])
  exact .mp (.mp hd (.closed hs)) (.mp hg (.closed hc))

theorem augmented_guard_certificate (ψ : Peano.Formula) (y base : Nat) (hy : y < base + 32) :
    theoremCode (certificate (augmented_guard ψ y base hy)) =
      imp (guardFormula ψ).encode (imp (domainAt base y).encode
        (guardFormula (augmented ψ y)).encode) := certificate_correct _
end PASoundness.PAtoCompactInductionAugmentedGuard

#print axioms PASoundness.PAtoCompactInductionAugmentedGuard.augmented_free
#print axioms PASoundness.PAtoCompactInductionAugmentedGuard.singleton_guard
#print axioms PASoundness.PAtoCompactInductionAugmentedGuard.augmented_guard
#print axioms PASoundness.PAtoCompactInductionAugmentedGuard.augmented_guard_certificate
