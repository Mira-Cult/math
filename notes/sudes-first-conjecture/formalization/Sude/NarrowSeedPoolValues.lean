import Sude.NarrowSeedRetained
import Sude.ScreenedPool

/-! Reindex retained actual seed pairs as prescribed-pool stage values. -/
namespace Sude
noncomputable section

/-- Enumerate the selected stage indices without identifying equal widths. -/
def retainedSeedStageIndex (r P : ℕ) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) : Fin P → Fin r :=
  (retainedSeedGroups r kept hsub).orderEmbOfFin (by rw [retainedSeedGroups_card, hkept])

theorem retainedSeedStageIndex_injective (r P : ℕ) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) :
    Function.Injective (retainedSeedStageIndex r P kept hsub hkept) :=
  ((retainedSeedGroups r kept hsub).orderEmbOfFin (by rw [retainedSeedGroups_card, hkept])).injective

/-- Map every retained stage, pair slot and side to its original sorted label. -/
def retainedSeedSlot (r P Q : ℕ) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (x : (Fin P × Fin Q) × Bool) : (Fin r × Fin Q) × Bool :=
  ((retainedSeedStageIndex r P kept hsub hkept x.1.1, x.1.2), x.2)

theorem retainedSeedSlot_injective (r P Q : ℕ) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) :
    Function.Injective (retainedSeedSlot r P Q kept hsub hkept) := by
  rintro ⟨⟨j, i⟩, b⟩ ⟨⟨j', i'⟩, b'⟩ h
  have hj : j = j' := retainedSeedStageIndex_injective r P kept hsub hkept
    (congrArg (fun x : (Fin r × Fin Q) × Bool => x.1.1) h)
  have hi : i = i' := congrArg (fun x : (Fin r × Fin Q) × Bool => x.1.2) h
  have hb : b = b' := congrArg (fun x : (Fin r × Fin Q) × Bool => x.2) h
  subst j'; subst i'; subst b'
  rfl

/-- Values supplied to the physical allocator are actual prescribed-pool
entries and avoid the earlier value reservation. -/
def retainedSeedPoolValues {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial) :
    (Fin P × Fin Q) × Bool → pool n := fun x =>
  ⟨sortedSeedEndpoint candidates r Q gap hcard (retainedSeedSlot r P Q kept hsub hkept x),
    mem_poolFinset.mp (Finset.mem_sdiff.mp (hav _)).1⟩

theorem retainedSeedPoolValues_injective {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard)) :
    Function.Injective (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav) := by
  intro x y heq
  apply retainedSeedSlot_injective r P Q kept hsub hkept
  apply hinj
  exact congrArg Subtype.val heq

theorem retainedSeedPoolValues_gap {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial) :
    ∀ j i, (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, i), true)).val =
      (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav ((j, i), false)).val + gap := by
  intro j i
  simp [retainedSeedPoolValues, retainedSeedSlot, sortedSeedEndpoint, pairEndpoint]

theorem retainedSeedPoolValues_avoid {n : ℕ} (candidates : Finset ℕ) (r P Q gap : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial) :
    ∀ x, (retainedSeedPoolValues candidates r P Q gap hcard kept hsub hkept initial hav x).val ∉ initial := by
  intro x
  exact (Finset.mem_sdiff.mp (hav _)).2

end
end Sude
