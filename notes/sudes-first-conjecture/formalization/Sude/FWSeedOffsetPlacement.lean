import Sude.FWSeedRectangleOffset
import Sude.NarrowSeedPoolValues
import Sude.NarrowPoolValues

/-! Place supplied retained FW seed pairs in the offset RP1 rectangles,
while preserving explicitly supplied bridge cells. Ordinary seed layers and
later controller geometry remain separate obligations. -/
namespace Sude
noncomputable section

/-- Install the exact supplied retained seed endpoints in the 384 offset
rectangles. The earlier reserved entries must lie in `bridges`, all supplied
seed endpoints must be pool entries avoiding that reservation, and the seed
rectangles must be free of those reserved cells. No seed selection is redone. -/
theorem fw_install_retained_seed_offset_rectangles
    (n L : ℕ) (candidates : Finset ℕ)
    (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (bridges : Finset ℕ)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ bridges)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (base : Finset (Cell n))
    (hbase : ∀ c ∈ base, entry a c ∈ bridges)
    (hfree : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      packedRectangleCorner hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
        (fwSeedRectangle hseed x.1, x.2) ∉ base) :
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ x : Fin (16 * (4 * 6)) × Fin 4,
        entry b (packedRectangleCorner hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
            (fwSeedRectangle hseed x.1, x.2)) =
          sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
            (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput hdiag x))) ∧
      (∀ c ∈ base, entry b c = entry a c) ∧
      (∀ (j : Fin 16) (u : Fin (4 * 6)) (pair : Fin 2),
        entry b (packedRectangleCorner hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
            (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair true)) =
          entry b (packedRectangleCorner hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
            (fwSeedRectangle hseed (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2) := by
  dsimp only
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let values := retainedSeedPoolValues candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav
  let cells : Fin (16 * (4 * 6)) × Fin 4 → Cell n := fun x =>
    packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)
  let v : Fin (16 * (4 * 6)) × Fin 4 → pool n := fun x => values (prefixRectangleInput hdiag x)
  have hc : Function.Injective cells := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have heq := packedRectangleCorner_injective hs choice h
    exact Prod.ext (fwSeedRectangle_injective hseed (congrArg (fun z : Fin L × Fin 4 => z.1) heq))
      (congrArg (fun z : Fin L × Fin 4 => z.2) heq)
  have hv : Function.Injective v :=
    (retainedSeedPoolValues_injective candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav hinj).comp
      (prefixRectangleInput_injective hdiag)
  have havoid : ∀ x c, c ∈ base → (v x).val ≠ entry a c := by
    intro x c hc' heq
    have hnot := retainedSeedPoolValues_avoid candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav
      (prefixRectangleInput hdiag x)
    apply hnot
    change (v x).val ∈ bridges
    rw [heq]
    exact hbase c hc'
  obtain ⟨b, hplaced, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cells v base hc hv hfree havoid
  refine ⟨b, hplaced, hfixed, ?_⟩
  intro j u pair
  rw [hplaced (finProdFinEquiv (j, u), prefixPairCorner pair true),
    hplaced (finProdFinEquiv (j, u), prefixPairCorner pair false)]
  change (values (prefixRectangleInput hdiag (finProdFinEquiv (j, u), prefixPairCorner pair true))).val =
    (values (prefixRectangleInput hdiag (finProdFinEquiv (j, u), prefixPairCorner pair false))).val + 2
  rw [prefixRectangleInput_pair, prefixRectangleInput_pair]
  exact retainedSeedPoolValues_gap candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept bridges hav
    j (prefixDiagonalPairIndex hdiag (u, pair))

end
end Sude
