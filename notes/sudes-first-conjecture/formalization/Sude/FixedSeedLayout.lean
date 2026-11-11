import Sude.PermutedSeedExhaustive
import Sude.Placement

/-! A fixed physical layout accepts every subsequent stage permutation. -/
namespace Sude
noncomputable section

/-- Fix the cells first. Every later stage permutation can be installed in
those same cells while preserving all previously reserved entries. -/
theorem fixed_seed_layout_accepts_all_permutations {n r P Q gap d layers L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (a : Cell n ≃ Fin (n * n)) (base : Finset (Cell n))
    (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hcells : Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols))
    (hfree : ∀ x, prefixPhysicalCells hrect hs choice rows cols hrows hcols x ∉ base) :
    ∀ ω : Fin P → Equiv.Perm (Fin Q), ∃ b : Cell n ≃ Fin (n * n),
      (∀ x, entry b (prefixPhysicalCells hrect hs choice rows cols hrows hcols x) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ c ∈ base, entry b c = entry a c) ∧
      Finset.univ.image (fun x => entry b
        (prefixPhysicalCells hrect hs choice rows cols hrows hcols x)) =
          retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  intro ω
  let values := permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
  have hv : Function.Injective (fun x => values (prefixPhysicalInput hfit hdiag x)) :=
    (permutedRetainedSeedValues_injective candidates r P Q gap hcard kept hsub hkept initial hav hinj ω).comp
      (prefixPhysicalInput_injective hfit hdiag)
  have havoid : ∀ x c, c ∈ base → (values (prefixPhysicalInput hfit hdiag x)).val ≠ entry a c := by
    intro x c hc heq
    have hn := permutedRetainedSeedValues_avoid candidates r P Q gap hcard kept hsub hkept initial hav ω
      (prefixPhysicalInput hfit hdiag x)
    exact hn (heq ▸ hbase c hc)
  obtain ⟨b, hb, hfixed⟩ := place_distinct_pool_entries_preserving a
    (prefixPhysicalCells hrect hs choice rows cols hrows hcols)
    (fun x => values (prefixPhysicalInput hfit hdiag x)) base hcells hv hfree havoid
  have hused := (permutedPrefixPhysical_realizes_retained candidates hcard kept hsub hkept initial hav hinj ω
    hfit hdiag hexact (prefixPhysicalCells hrect hs choice rows cols hrows hcols) (entry b) hb).2
  exact ⟨b, hb, hfixed, hused⟩

end
end Sude
