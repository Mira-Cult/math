import Sude.FWSeedPerpendicularOrientation

/-! The full selected-seed orientation decomposes into the ordinary network
seed band plus explicit rectangle-pair orientations. The perpendicular
ordinary family contributes zero; no rectangle term is assumed to vanish. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- In an actual row, the selected-seed orientation is the row seed band's
orientation plus the explicitly retained rectangle-pair orientations. -/
theorem fw_seed_row_orientation_split {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (r : Fin n) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let orient := physicalPairLineOrientation cells (fun x => x.1 = r)
    (∑ p : Fin 16 × Fin (6 * (n + 8)), orient p) =
      (∑ t ∈ fwSeedJointPairImage br sr wr gr hsr,
        orient (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t)) +
      ∑ j : Fin 16, ∑ x : Fin (4 * 6) × Fin 2,
        orient (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) x) := by
  classical
  dsimp only
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let E := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let orient := physicalPairLineOrientation cells (fun x => x.1 = r)
  have hstage (j : Fin 16) :
      (∑ q : Fin (6 * (n + 8)), orient (j,q)) =
        (∑ x : Fin (4 * 6) × Fin 2, orient (j,prefixDiagonalPairIndex hdiag x)) +
        ∑ k : Fin 3, ∑ e : Fin n, orient (j,prefixOrdinaryPairIndex hfit (0,k,e)) := by
    calc
      _ = ∑ tag : PrefixStagePair 6 3 n, orient (j,E tag) :=
        (E.sum_comp (fun q => orient (j,q))).symm
      _ = _ := by
        simp only [E, Equiv.ofBijective_apply, prefixStagePairSlot,
          Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
        have hzero : (∑ k : Fin 3, ∑ e : Fin n, orient (j,prefixOrdinaryPairIndex hfit (1,k,e))) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          apply Finset.sum_eq_zero
          intro e he
          exact fw_seed_column_pair_row_orientation_zero hseed hs choice sr sc hsr hsc j k e r
        rw [hzero, add_zero]
  have hnet : (∑ t ∈ fwSeedJointPairImage br sr wr gr hsr,
      orient (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t)) =
      ∑ j : Fin 16, ∑ k : Fin 3, ∑ e : Fin n,
        orient (j,prefixOrdinaryPairIndex hfit (0,k,e)) := by
    unfold fwSeedJointPairImage
    rw [Finset.sum_image (fwSeedJointPairIndex_injective br sr wr gr hsr).injOn]
    simp only [Fintype.sum_prod_type, fw_seed_joint_to_ordinary_index]
  change (∑ p : Fin 16 × Fin (6 * (n + 8)), orient p) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hstage, Finset.sum_add_distrib]
  rw [hnet]
  simp only [orient, cells]
  ring

/-- In an actual column, the selected-seed orientation is the column seed
band's orientation plus the explicitly retained rectangle-pair orientations. -/
theorem fw_seed_column_orientation_split {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (c : Fin n) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    (∑ p : Fin 16 × Fin (6 * (n + 8)), physicalPairLineOrientation cells (fun x => x.2 = c) p) =
      (∑ t ∈ fwSeedJointPairImage bc sc wc gc hsc,
        physicalPairLineOrientation cells (fun x => x.2 = c)
          (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t)) +
      ∑ j : Fin 16, ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
        physicalPairLineOrientation cells (fun x => x.2 = c) (j, prefixDiagonalPairIndex hdiag (rect,pair)) := by
  classical
  dsimp only
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let line := fun x : Cell n => x.2 = c
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let eqv := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let o := fun j q => physicalPairLineOrientation cells line (j,q)
  have hstage (j : Fin 16) :
      (∑ q, o j q) =
        (∑ rect : Fin (4 * 6), ∑ pair : Fin 2, o j (prefixDiagonalPairIndex hdiag (rect,pair))) +
        ∑ k : Fin 3, ∑ e : Fin n, o j (prefixOrdinaryPairIndex hfit (1,k,e)) := by
    calc
      ∑ q, o j q = ∑ tag : PrefixStagePair 6 3 n, o j (eqv tag) := (eqv.sum_comp (o j)).symm
      _ = _ := by
        simp only [eqv, Equiv.ofBijective_apply, prefixStagePairSlot, Fintype.sum_sum_type,
          Fintype.sum_prod_type, Fin.sum_univ_two]
        simp only [o, cells, line, fw_seed_row_pair_column_orientation_zero, Finset.sum_const_zero,
          zero_add]
  have hnet : (∑ t ∈ fwSeedJointPairImage bc sc wc gc hsc,
      physicalPairLineOrientation cells line (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t)) =
      ∑ j : Fin 16, ∑ k : Fin 3, ∑ e : Fin n, o j (prefixOrdinaryPairIndex hfit (1,k,e)) := by
    unfold fwSeedJointPairImage
    rw [Finset.sum_image]
    · simp [Fintype.sum_prod_type, fw_seed_joint_to_ordinary_index, o]
    · intro x hx y hy heq
      exact fwSeedJointPairIndex_injective bc sc wc gc hsc heq
  change (∑ p : Fin 16 × Fin (6 * (n + 8)), o p.1 p.2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hstage, Finset.sum_add_distrib]
  rw [hnet]
  simp only [o, cells, line]
  ring

end
end Sude
