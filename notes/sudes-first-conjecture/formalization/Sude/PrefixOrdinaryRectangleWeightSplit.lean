import Sude.FWControllerStageReindex

/-! Exact stage weight split for arbitrary permuted prefix-stage pair slots.
The caller must establish rectangle membership and ordinary exclusion. -/
namespace Sude
noncomputable section

/-- The physical line weight outside the rectangle support is exactly the
weight of ordinary tags after any stage-wise pair permutation. -/
theorem prefix_permuted_ordinary_rectangle_weight_split {n P : ℕ}
    (cells : (Fin P × Fin (6 * (n + 8))) × Bool → Cell n)
    (perm : Equiv.Perm (Fin (6 * (n + 8)))) (j : Fin P)
    (rect : Finset (Cell n)) (line : Cell n → Prop) [DecidablePred line]
    (hdiag : ∀ r : Fin (4 * 6), ∀ p : Fin 2, ∀ side : Bool,
      cells ((j, perm (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (r,p))),side) ∈ rect)
    (hord : ∀ network : Fin 2, ∀ k : Fin 3, ∀ edge : Fin n, ∀ side : Bool,
      cells ((j, perm (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (network,k,edge))),side) ∉ rect) :
    (∑ q, physicalPairLineWeight cells line (j,q)) -
      (∑ q, physicalPairLineWeight cells (fun z => z ∈ rect ∧ line z) (j,q)) =
    ∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      physicalPairLineWeight cells line (j, perm (prefixOrdinaryPairIndex
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))) := by
  classical
  let e := Equiv.ofBijective (prefixStagePairSlot (d := 6) (layers := 3) (n := n)
      (Q := 6 * (n + 8)) (by omega) (by omega))
    (prefixStagePairSlot_bijective (by omega) (by omega) (by omega))
  let w : Fin (6 * (n + 8)) → ℝ := fun q =>
    physicalPairLineWeight cells line (j,perm q) -
      physicalPairLineWeight cells (fun z => z ∈ rect ∧ line z) (j,perm q)
  have hdiag' (r : Fin (4 * 6)) (p : Fin 2) : w (prefixDiagonalPairIndex
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (r,p)) = 0 := by
    dsimp [w, physicalPairLineWeight]
    simp [hdiag]
    ring
  have hord' (network : Fin 2) (k : Fin 3) (edge : Fin n) :
      w (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
        (network,k,edge)) = physicalPairLineWeight cells line (j,perm (prefixOrdinaryPairIndex
          (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))) := by
    dsimp [w, physicalPairLineWeight]
    simp [hord]
  have hperm : (∑ q, physicalPairLineWeight cells line (j,q)) -
      (∑ q, physicalPairLineWeight cells (fun z => z ∈ rect ∧ line z) (j,q)) = ∑ q, w q := by
    dsimp [w]
    rw [Finset.sum_sub_distrib]
    have ht := Equiv.sum_comp perm (fun q => physicalPairLineWeight cells line (j,q))
    have hr := Equiv.sum_comp perm (fun q => physicalPairLineWeight cells (fun z => z ∈ rect ∧ line z) (j,q))
    exact congrArg₂ (· - ·) ht.symm hr.symm
  rw [hperm, ← e.sum_comp w]
  simp only [e, Equiv.ofBijective_apply, PrefixStagePair, Fintype.sum_sum_type,
    Fintype.sum_prod_type, prefixStagePairSlot]
  simp [hdiag', hord']

end
end Sude
