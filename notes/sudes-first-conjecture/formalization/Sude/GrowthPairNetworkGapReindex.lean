import Sude.BTGrowingPhysicalStageTotals
import Sude.VariablePrefixPhysical

/-! Same-square reindexing of stagewise pair gaps to physical network roles.
No placement, network, or bound is constructed. -/
namespace Sude
noncomputable section

/-- A uniform gap within each physical growth stage gives that stage's gap
on every ordinary row and column layer. The stage gaps may differ. -/
theorem growth_pair_gaps_imply_role_network_gaps {P d r n Q L : ℕ}
    (hfit : (4*d)*2+2*(r*n) ≤ Q) (hdiag : (4*d)*2 ≤ Q)
    (hexact : (4*d)*2+2*(r*n) = Q)
    (offset : ℕ) (hoff : offset+P*(4*d) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*r) (hc : cols.length = P*r)
    (a : Cell n ≃ Fin (n*n)) (gaps : Fin P → ℕ)
    (hgap : ∀ j i,
      entry a (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc ((j,i),true)) =
        entry a (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc ((j,i),false)) + gaps j) :
    (∀ (i : Fin (P*r)) (e : Fin n),
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inl (i,(e,true))))) =
        entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inl (i,(e,false))))) +
          variablePrefixNetworkGap gaps rfl i e) ∧
    (∀ (i : Fin (P*r)) (e : Fin n),
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inr (i,(e,true))))) =
        entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc (Sum.inr (Sum.inr (i,(e,false))))) +
          variablePrefixNetworkGap gaps rfl i e) := by
  let e := prefixPhysicalInputEquiv (P := P) (n := n) hfit hdiag hexact
  have hcell (x : PrefixPhysicalInputs P d r n) :
      btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc
        (prefixPhysicalInput hfit hdiag x) =
      btGrowingOffsetCells offset hoff hs choice rows cols hr hc x := by
    change btGrowingOffsetCells offset hoff hs choice rows cols hr hc (e.symm (e x)) = _
    rw [Equiv.symm_apply_apply]
  constructor
  · intro i x
    let p : Fin P × Fin r := finProdFinEquiv.symm i
    have h := hgap p.1 (prefixOrdinaryPairIndex hfit (0,p.2,x))
    have htrue := hcell (Sum.inr (Sum.inl (i,(x,true))))
    have hfalse := hcell (Sum.inr (Sum.inl (i,(x,false))))
    simp only [prefixPhysicalInput, prefixNetworkInput, prefixOrdinaryInput, Fin.cast_refl, id_eq] at htrue hfalse
    dsimp [p] at h
    rw [htrue, hfalse] at h
    simpa [variablePrefixNetworkGap, p] using h
  · intro i x
    let p : Fin P × Fin r := finProdFinEquiv.symm i
    have h := hgap p.1 (prefixOrdinaryPairIndex hfit (1,p.2,x))
    have htrue := hcell (Sum.inr (Sum.inr (i,(x,true))))
    have hfalse := hcell (Sum.inr (Sum.inr (i,(x,false))))
    simp only [prefixPhysicalInput, prefixNetworkInput, prefixOrdinaryInput, Fin.cast_refl, id_eq] at htrue hfalse
    dsimp [p] at h
    rw [htrue, hfalse] at h
    simpa [variablePrefixNetworkGap, p] using h

end
end Sude
