import Sude.FWSeedExistingReallocation
import Sude.PhysicalLineCenteredIdentity

/-! A supplied seed permutation controls selected physical line contributions. -/
namespace Sude
noncomputable section

/-- A supplied bounded stage permutation gives an actual selected-cell line
bound on the same already-reallocated square. The input line family may be
instantiated with all row, column and diagonal labels. No diagonal-sum
preservation, completion, or prime-line claim is made. -/
theorem fw_seed_reallocation_supplied_concentration {n L m : ℕ}
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry old (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (hcells : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (line : Fin m → Cell n → Prop) [∀ l, DecidablePred (line l)]
    (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8)))) (B : ℝ)
    (hbound : let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      let weights := fun l j q => physicalPairLineWeight cells (line l) (j, q)
      let values := fun j q => (((entry grown (cells ((j, q), false)) : ℝ) +
        entry grown (cells ((j, q), true))) / 2)
      ∀ l, |stageLineCentered (fun _ _ => Finset.univ) weights values l ω| ≤ B) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let weights := fun l j q => physicalPairLineWeight cells (line l) (j, q)
    let values := fun j q => (((entry grown (cells ((j, q), false)) : ℝ) +
      entry grown (cells ((j, q), true))) / 2)
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ j i side, entry b (cells ((j, i), side)) = entry grown (cells ((j, ω j i), side))) ∧
      (∀ c, c ∉ Set.range cells → entry b c = entry grown c) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
        entry b (cells ((j, x.1), x.2))) =
        Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
        entry grown (cells ((j, x.1), x.2)))) ∧
      Finset.univ.image (fun x => entry b (cells x)) =
        retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub ∧
      (∀ j i, entry b (cells ((j, i), true)) = entry b (cells ((j, i), false)) + 2) ∧
      (∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry b c : ℝ)) -
        (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) -
        (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) := by
  classical
  dsimp only at hbound ⊢
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let weights := fun l j q => physicalPairLineWeight cells (line l) (j, q)
  let values := fun j q => (((entry grown (cells ((j, q), false)) : ℝ) +
    entry grown (cells ((j, q), true))) / 2)
  obtain ⟨b, hb, houtside, hstage, himage, hgap⟩ :=
    fw_reallocate_existing_retained_seed_pairs candidates hcard kept hsub hkept hinj
      hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hsd hso ω
  refine ⟨b, hb, houtside, hstage, himage, hgap, ?_⟩
  intro l
  have hmid : ∀ j q, (((entry b (cells ((j, q), false)) : ℝ) +
      entry b (cells ((j, q), true))) / 2) = values j (ω j q) := by
    intro j q
    simp only [values, cells, hb]
  have hrealgap : ∀ j q, (entry b (cells ((j, q), true)) : ℝ) -
      entry b (cells ((j, q), false)) = (2 : ℝ) := by
    intro j q
    have h := hgap j q
    have hr : (entry b (cells ((j, q), true)) : ℝ) =
        (entry b (cells ((j, q), false)) : ℝ) + 2 := by exact_mod_cast h
    linarith
  have heq := physicalPair_line_sum_eq_centered (by omega : 0 < 6 * (n + 8))
    cells hcells line b weights values ω (2 : ℝ) (fun _ _ _ => rfl) hmid hrealgap l
  have hbnd := hbound l
  dsimp only [weights, values, cells] at heq hbnd ⊢
  have : (∑ c ∈ (Finset.univ.image (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)).filter (line l),
      (entry b c : ℝ)) -
      (∑ j, ((∑ q, physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (line l) (j, q)) * ((∑ q, (((entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, q), false)) : ℝ) +
          entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, q), true))) / 2)) /
            ((6 * (n + 8) : ℕ) : ℝ)))) -
      (∑ p, physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (line l) p * ((2 : ℝ) / 2)) =
      stageLineCentered (fun _ _ => Finset.univ)
        (fun l j q => physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (line l) (j, q))
        (fun j q => (((entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, q), false)) : ℝ) +
          entry grown (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j, q), true))) / 2)) l ω := by linarith
  rw [this]
  exact hbnd

end
end Sude
