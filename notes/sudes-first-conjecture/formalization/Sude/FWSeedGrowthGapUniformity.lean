import Sude.FWSeedGrowthBandProducts

/-! Seed and growth gap data give one edge-independent gap per selected layer.
This is a finite-index argument, independent of placement or network creation. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- If all seed pairs have gap 2 and all growth edges at each stage carry the
stage's gap, then a single layer-gap function covers both bands. The proof also
handles `n = 0`, where the edge hypotheses are vacuous. -/
theorem fw_seed_growth_layer_gap_uniformity {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hgr : gr.length = P * 3)
    (gap : Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n → ℕ)
    (d : Fin P → ℕ)
    (hseed : ∀ t ∈ fwSeedJointPairImage br sr wr gr hsr, gap t = 2)
    (hgrowth : ∀ (j : Fin P) (k : Fin 3) (e : Fin n),
      gap (fwGrowthJointLayerIndex br sr wr gr hgr j k,e) = d j) :
    ∃ g : Fin (((br ++ sr) ++ wr) ++ gr).length → ℕ,
      ∀ i ∈ fwSeedJointLayerImage br sr wr gr hsr ∪ fwGrowthJointLayerImage br sr wr gr hgr,
        ∀ e, gap (i,e) = g i := by
  classical
  let g : Fin (((br ++ sr) ++ wr) ++ gr).length → ℕ := fun i =>
    if h : 0 < n then gap (i, ⟨0,h⟩) else 0
  refine ⟨g, ?_⟩
  intro i hi e
  have hn : 0 < n := Nat.zero_lt_of_lt e.isLt
  simp only [g, dif_pos hn]
  rcases Finset.mem_union.mp hi with hs | hg
  · obtain ⟨⟨j,k⟩, _, hj⟩ := Finset.mem_image.mp hs
    change fwSeedJointLayerIndex br sr wr gr hsr j k = i at hj
    subst i
    have hs' (e : Fin n) : (fwSeedJointLayerIndex br sr wr gr hsr j k,e) ∈
        fwSeedJointPairImage br sr wr gr hsr :=
      Finset.mem_image.mpr ⟨((j,k),e), Finset.mem_univ _, rfl⟩
    exact (hseed _ (hs' e)).trans (hseed _ (hs' ⟨0,hn⟩)).symm
  · obtain ⟨⟨j,k⟩, _, hj⟩ := Finset.mem_image.mp hg
    change fwGrowthJointLayerIndex br sr wr gr hgr j k = i at hj
    subst i
    rw [hgrowth j k e, hgrowth j k ⟨0,hn⟩]

end
end Sude
