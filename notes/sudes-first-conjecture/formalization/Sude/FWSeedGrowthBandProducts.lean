import Sude.FWResidualNetworkBands

/-! Full-edge product descriptions for the seed and growth layer bands. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- A Cartesian family of pairs whose first coordinate is mapped is the
product of the mapped first-coordinate image and the full second coordinate. -/
theorem image_prod_univ_eq_product {α β γ : Type*} [Fintype α] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] (f : α → β) :
    (Finset.univ : Finset (α × γ)).image (fun x => (f x.1, x.2)) =
      (Finset.univ.image f).product (Finset.univ : Finset γ) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨⟨a,c⟩, _, h⟩ := Finset.mem_image.mp hx
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, congrArg Prod.fst h⟩,
      Finset.mem_univ _⟩
  · intro hx
    obtain ⟨hi, _⟩ := Finset.mem_product.mp hx
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨(a,x.2), Finset.mem_univ _, Prod.ext ha rfl⟩

/-- The seed layer indices in the actual joint list. -/
def fwSeedJointLayerImage {n : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length) :=
  Finset.univ.image (fun x : Fin 16 × Fin 3 => fwSeedJointLayerIndex br sr wr gr hsr x.1 x.2)

/-- The growth layer indices in the actual joint list. -/
def fwGrowthJointLayerImage {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length) :=
  Finset.univ.image (fun x : Fin P × Fin 3 => fwGrowthJointLayerIndex br sr wr gr hgr x.1 x.2)

/-- Each seed layer contributes every edge of that layer. -/
theorem fw_seed_joint_pair_image_product {n : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) :
    fwSeedJointPairImage br sr wr gr hsr =
      (fwSeedJointLayerImage br sr wr gr hsr).product (Finset.univ : Finset (Fin n)) := by
  classical
  exact image_prod_univ_eq_product (fun x : Fin 16 × Fin 3 =>
    fwSeedJointLayerIndex br sr wr gr hsr x.1 x.2)

/-- Each growth layer contributes every edge of that layer. -/
theorem fw_growth_joint_pair_image_product {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n)) (hgr : gr.length = P * 3) :
    fwGrowthJointPairImage br sr wr gr hgr =
      (fwGrowthJointLayerImage br sr wr gr hgr).product (Finset.univ : Finset (Fin n)) := by
  classical
  exact image_prod_univ_eq_product (fun x : Fin P × Fin 3 =>
    fwGrowthJointLayerIndex br sr wr gr hgr x.1 x.2)

end
end Sude
