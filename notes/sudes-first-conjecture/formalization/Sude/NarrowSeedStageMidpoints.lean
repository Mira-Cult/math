import Sude.NarrowSeedMidpoints
import Sude.NarrowSeedPoolValues

/-! Selected actual seed stages retain their sorted midpoint ranges. -/
namespace Sude
noncomputable section

theorem retainedSeedStageIndex_mem (r P : ℕ) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (j : Fin P) :
    (retainedSeedStageIndex r P kept hsub hkept j).val ∈ kept := by
  apply (mem_retainedSeedGroups r kept hsub _).mp
  exact (retainedSeedGroups r kept hsub).orderEmbOfFin_mem
    (by rw [retainedSeedGroups_card, hkept]) j

/-- Every midpoint in a selected stage is between the first and last
actual pair midpoints of that sorted group. -/
theorem retainedSeedMidpoint_between {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hQ : 0 < Q) (j : Fin P) (i : Fin Q) :
    let group := retainedSeedStageIndex r P kept hsub hkept j
    let midpoint : ℝ := ((retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, i), false)).val +
      (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, i), true)).val : ℕ) / 2
    sortedSeedMidpoint candidates r Q gap hcard group ⟨0, hQ⟩ ≤ midpoint ∧
      midpoint ≤ sortedSeedMidpoint candidates r Q gap hcard group ⟨Q - 1, by omega⟩ := by
  dsimp only
  let group := retainedSeedStageIndex r P kept hsub hkept j
  have hmid : ((retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, i), false)).val +
      (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, i), true)).val : ℕ) / (2 : ℝ) =
      sortedSeedMidpoint candidates r Q gap hcard group i := by
    simp [sortedSeedMidpoint, retainedSeedPoolValues, retainedSeedSlot, group, Nat.cast_add]
  rw [hmid]
  rw [sortedSeedMidpoint_slot, sortedSeedMidpoint_slot, sortedSeedMidpoint_slot]
  have htop : group.val * Q + (Q - 1) < r * Q := by
    have h := (finProdFinEquiv (group, (⟨Q - 1, by omega⟩ : Fin Q))).isLt
    simp only [finProdFinEquiv] at h
    simpa [Nat.mul_comm, Nat.add_comm] using h
  have hbot := sortedSeedReal_mono candidates r Q hcard
    (group.val * Q + 0) (group.val * Q + i.val) (by omega) (by omega)
  have hhigh := sortedSeedReal_mono candidates r Q hcard
    (group.val * Q + i.val) (group.val * Q + (Q - 1)) (by omega) htop
  exact ⟨by linarith, by linarith⟩

/-- Any two physical pair midpoints in the same retained stage differ by
at most that actual sorted group's width. -/
theorem retainedSeedMidpoint_spread {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hQ : 0 < Q) (j : Fin P) (i k : Fin Q) :
    let group := retainedSeedStageIndex r P kept hsub hkept j
    let mid := fun x => (((retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, x), false)).val : ℝ) +
      (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, x), true)).val) / 2
    |mid i - mid k| ≤ sortedSeedReal candidates r Q hcard (group.val * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (group.val * Q) := by
  dsimp only
  have hi := retainedSeedMidpoint_between candidates r P Q gap hcard kept hsub hkept initial hav hQ j i
  have hk := retainedSeedMidpoint_between candidates r P Q gap hcard kept hsub hkept initial hav hQ j k
  have hrange := sortedSeedMidpoint_range candidates r Q gap hcard hQ
    (retainedSeedStageIndex r P kept hsub hkept j)
  push_cast at hi hk
  rw [abs_le]
  constructor <;> linarith

end
end Sude
