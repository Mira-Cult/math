import Sude.RegularFactorMatching
import Sude.ActualUnusedPool
import Mathlib.Data.Finset.Sort

/-! Put the exact unused pool into a supplied regular factor in sorted blocks. -/
namespace Sude
noncomputable section

/-- Matching-major order: each block consists of the consecutive `n` ranks
assigned to one physical perfect matching. -/
def sortedFactorValue {n k : ℕ} (values : Finset (pool n)) (hcard : values.card = k * n)
    (x : Fin k × Fin n) : pool n :=
  values.orderEmbOfFin hcard (finProdFinEquiv x)

theorem sortedFactorValue_injective {n k : ℕ} (values : Finset (pool n))
    (hcard : values.card = k * n) : Function.Injective (sortedFactorValue values hcard) :=
  (values.orderEmbOfFin hcard).injective.comp finProdFinEquiv.injective

theorem sortedFactorValue_mem {n k : ℕ} (values : Finset (pool n))
    (hcard : values.card = k * n) (x : Fin k × Fin n) : sortedFactorValue values hcard x ∈ values :=
  values.orderEmbOfFin_mem hcard (finProdFinEquiv x)

theorem sortedFactor_index {n k : ℕ} (j : Fin k) (i : Fin n) :
    (finProdFinEquiv (j, i)).val = j.val * n + i.val := by
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- If the whole unreserved cell set is a `k`-regular factor, place the
exact unused prescribed pool into it in consecutive sorted matching blocks.
Every earlier reservation is fixed and every cell and value is used once.
No assertion is made that such a factor exists in a given residual graph. -/
theorem place_sorted_regular_factor {n k : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved E : Finset (Cell n)) (hfree : E = Finset.univ \ reserved)
    (hreg : CellFactorRegular E k) :
    ∃ (ps : List (Equiv.Perm (Fin n))) (_hlen : ps.length = k)
      (_hdecomp : RegularMatchingDecomposition E ps)
      (hcard : (actualUnusedPool a reserved).card = ps.length * n)
      (b : Cell n ≃ Fin (n * n)),
      (∀ x : Fin ps.length × Fin n,
        entry b (regularMatchingSlot ps x) =
          (sortedFactorValue (actualUnusedPool a reserved) hcard x).val) ∧
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ z ∈ E, ∃ x, regularMatchingSlot ps x = z) ∧
      Function.Injective (regularMatchingSlot ps) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  obtain ⟨ps, hlen, hdecomp⟩ := regular_factor_matching_decomposition E hreg
  have hecard : E.card = ps.length * n := by
    have h := Fintype.card_congr (regularMatchingSlotEquiv hdecomp)
    simpa [Fintype.card_prod] using h.symm
  have hcard : (actualUnusedPool a reserved).card = ps.length * n := by
    unfold actualUnusedPool
    rw [Finset.card_image_of_injective _ (entryPool a).injective, ← hfree]
    exact hecard
  let values := sortedFactorValue (actualUnusedPool a reserved) hcard
  have hslot : Function.Injective (regularMatchingSlot ps) :=
    regularMatchingSlot_injective hdecomp.pairwise_disjoint
  have hnew : ∀ x, regularMatchingSlot ps x ∉ reserved := by
    intro x
    have hm := regularMatchingSlot_mem hdecomp x
    rw [hfree] at hm
    exact (Finset.mem_sdiff.mp hm).2
  have hav : ∀ x z, z ∈ reserved → (values x).val ≠ entry a z := by
    intro x z hz
    exact actualUnusedPool_avoids a reserved (values x)
      (sortedFactorValue_mem (actualUnusedPool a reserved) hcard x) z hz
  obtain ⟨b, hplaced, hfixed⟩ := place_distinct_pool_entries_preserving a
    (regularMatchingSlot ps) values reserved hslot
    (sortedFactorValue_injective (actualUnusedPool a reserved) hcard) hnew hav
  exact ⟨ps, hlen, hdecomp, hcard, b, hplaced, hfixed,
    fun z hz => regularMatchingSlot_surjective hdecomp z hz, hslot, entry_range _, entry_injective _⟩

end
end Sude
