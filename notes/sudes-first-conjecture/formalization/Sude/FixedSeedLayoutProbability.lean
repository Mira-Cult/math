import Sude.FixedSeedLayoutExistence
import Sude.PermutedSeedMidpoints
import Sude.StageSquaredInvoice

/-! Probability allocation on geometry fixed before randomization. -/
namespace Sude
noncomputable section

theorem fixed_seed_layout_has_weighted_allocation {n r P Q gap d layers L : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (initial : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates r Q gap hcard x ∈ poolFinset n \ initial)
    (hinj : Function.Injective (sortedSeedEndpoint candidates r Q gap hcard))
    (hQ : 0 < Q) (m : ℕ) (hm : 0 < m)
    (slots : Fin m → Fin P → Finset (Fin Q))
    (weights : Fin m → Fin P → Fin Q → ℝ)
    (V : ℝ) (hV : 0 ≤ V)
    (hnonneg : ∀ l j k, k ∈ slots l j → 0 ≤ weights l j k)
    (hinvoice : ∀ l, (∑ j,
      (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨Q - 1, by omega⟩ -
       retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept j ⟨0, hQ⟩) ^ 2 *
      ∑ k ∈ slots l j, (weights l j k) ^ 2) ≤ V)
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (a : Cell n ≃ Fin (n * n)) (base : Finset (Cell n))
    (hbase : ∀ c ∈ base, entry a c ∈ initial)
    (hcells : Function.Injective (prefixPhysicalCells hrect hs choice rows cols hrows hcols))
    (hfree : ∀ x, prefixPhysicalCells hrect hs choice rows cols hrows hcols x ∉ base) :
    ∃ ω : Fin P → Equiv.Perm (Fin Q), ∃ b : Cell n ≃ Fin (n * n),
      (∀ l, |stageLineCentered slots weights
        (retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept) l ω| ≤
        Real.sqrt (V * Real.log (4 * (m : ℝ)) / 2)) ∧
      (∀ x, entry b (prefixPhysicalCells hrect hs choice rows cols hrows hcols x) =
        (permutedRetainedSeedValues candidates r P Q gap hcard kept hsub hkept initial hav ω
          (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ c ∈ base, entry b c = entry a c) ∧
      Finset.univ.image (fun x => entry b
        (prefixPhysicalCells hrect hs choice rows cols hrows hcols x)) =
          retainedSeedEndpoints candidates r Q gap hcard kept hsub := by
  let values := retainedStageMidpoint candidates r P Q gap hcard kept hsub hkept
  let lo : Fin P → ℝ := fun j => values j ⟨0, hQ⟩
  let upper : Fin P → ℝ := fun j => values j ⟨Q - 1, by omega⟩
  have hvalues : ∀ j k, values j k ∈ Set.Icc (lo j) (upper j) := by
    intro j k
    exact retainedStageMidpoint_bounds candidates r P Q gap hcard kept hsub hkept initial hav hQ j k
  have hlu : ∀ j, lo j ≤ upper j := by
    intro j
    exact (hvalues j ⟨0, hQ⟩).2
  obtain ⟨ω, hbound⟩ := stageLines_exists_of_squared_invoice hm slots weights values lo upper V hV
    hlu hnonneg hvalues hinvoice
  obtain ⟨b, hb, hfixed, hused⟩ := fixed_seed_layout_accepts_all_permutations
    candidates hcard kept hsub hkept initial hav hinj hfit hdiag hexact hrect hs choice
    rows cols hrows hcols a base hbase hcells hfree ω
  exact ⟨ω, b, hbound, hb, hfixed, hused⟩

end
end Sude
