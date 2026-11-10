import Mathlib.Logic.Equiv.Fin.Basic

/-! Elementary standard-natural indexing of a finite lexicographic product.
These are metatheoretic facts, not derivations in K or PA. -/
namespace PASoundness.PAtoCompactProductIndex

theorem linear_lt_iff (n i j i' j' : Nat) (hj : j < n) (hj' : j' < n) :
    i*n+j < i'*n+j' ↔ i < i' ∨ (i = i' ∧ j < j') := by
  have lower {u v : Nat} (h : u < v) : (u+1)*n ≤ v*n :=
    Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr h)
  constructor
  · intro h
    rcases lt_trichotomy i i' with hi | he | hi
    · exact Or.inl hi
    · right
      subst i'
      exact ⟨rfl, by omega⟩
    · have hv := lower hi
      rw [Nat.add_mul, Nat.one_mul] at hv
      omega
  · rintro (hi | ⟨rfl,hjlt⟩)
    · have hv := lower hi
      rw [Nat.add_mul, Nat.one_mul] at hv
      omega
    · omega

theorem linear_lt_product (m n i j : Nat) (hi : i < m) (hj : j < n) :
    i*n+j < m*n := by
  have h := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hi)
  rw [Nat.succ_mul] at h
  omega

theorem linear_unique (n i j i' j' : Nat) (hj : j < n) (hj' : j' < n)
    (h : i*n+j = i'*n+j') : i = i' ∧ j = j' := by
  rcases lt_trichotomy i i' with hi | he | hi
  · have ht := (linear_lt_iff n i j i' j' hj hj').mpr (Or.inl hi)
    omega
  · subst i'
    exact ⟨rfl, by omega⟩
  · have ht := (linear_lt_iff n i' j' i j hj' hj).mpr (Or.inl hi)
    omega

theorem linear_decompose (m n k : Nat) (hk : k < m*n) :
    ∃ i < m, ∃ j < n, k = i*n+j := by
  let x : Fin (m*n) := ⟨k,hk⟩
  let ij : Fin m × Fin n := finProdFinEquiv.symm x
  have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply x)
  refine ⟨ij.1.val,ij.1.isLt,ij.2.val,ij.2.isLt,?_⟩
  simpa [ij, x, finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using h.symm

end PASoundness.PAtoCompactProductIndex

#print axioms PASoundness.PAtoCompactProductIndex.linear_lt_iff
#print axioms PASoundness.PAtoCompactProductIndex.linear_decompose
