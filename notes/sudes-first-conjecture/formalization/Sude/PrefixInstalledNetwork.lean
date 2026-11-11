import Sude.PrefixPairAllocation
import Sude.PrefixPhysicalGrid
import Sude.FamilyGrid

/-! Connect the installed prefix pairs to the centered physical network. -/
namespace Sude
noncomputable section

def prefixPhysicalStageSlot {P r n m : ℕ} (hlen : m = P * r)
    (x : (Fin r × Fin n) × Fin P) : Fin m × Fin n :=
  (bridgeStageLayerIndex hlen x.2 x.1.1, x.1.2)

theorem prefixPhysicalStageSlot_injective {P r n m : ℕ} (hlen : m = P * r) :
    Function.Injective (prefixPhysicalStageSlot (n := n) hlen) := by
  rintro ⟨⟨l, e⟩, j⟩ ⟨⟨l', e'⟩, j'⟩ h
  have he : e = e' := congrArg (fun z : Fin m × Fin n => z.2) h
  have hi := congrArg (fun z : Fin m × Fin n => z.1) h
  have hp := finProdFinEquiv.injective (Fin.cast_injective hlen.symm hi)
  have hj : j = j' := congrArg (fun z : Fin P × Fin r => z.1) hp
  have hl : l = l' := congrArg (fun z : Fin P × Fin r => z.2) hp
  exact Prod.ext (Prod.ext hl he) hj

theorem prefixNetworkGap_stage {P r n m : ℕ} (hlen : m = P * r)
    (j : Fin P) (layer : Fin r) (edge : Fin n) :
    prefixNetworkGap hlen (bridgeStageLayerIndex hlen j layer) edge = 2 ^ (j.val + 1) := by
  simp [prefixNetworkGap, bridgeStageLayerIndex]

theorem prefixNetworkGap_cast {P r n m q : ℕ} (h₁ : m = q) (h₂ : q = P * r)
    (i : Fin m) (edge : Fin n) :
    prefixNetworkGap h₂ (Fin.cast h₁ i) edge = prefixNetworkGap (h₁.trans h₂) i edge := by
  simp [prefixNetworkGap]

/-- The actual prefix layers yield all disjoint complete binary grids and
their common endpoints, for the physical pair system installed in the square. -/
def installedPrefixCenteredNetwork {P r n : ℕ}
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = P * r)
    (perms : Fin r → Equiv.Perm (Fin n))
    (hperms : layers.map Prod.fst = bridgeRepeatedPermutations P perms)
    (reserved : Finset (Cell n)) (packed : LayerPacking.PackedLayers reserved layers)
    (a : Cell n ≃ Fin (n * n))
    (hgap : ∀ i e, entry a ((layers.get i).1 e, (layers.get i).2 e) =
      entry a (e, (layers.get i).2 e) + prefixNetworkGap hlen i e) :
    CenteredNetwork (Fin r × Fin n) (Fin layers.length × Fin n)
      (packed.rowPairs a (prefixNetworkGap hlen) hgap) where
  block := prefixPairBlock P (prefixPhysicalStageSlot hlen)
  radius := fun _ => 2 ^ (P + 1) - 2
  source := Prod.snd
  target := fun e => perms e.1 e.2
  disjoint := fun e f h => prefixPairBlock_disjoint P (prefixPhysicalStageSlot hlen)
    (prefixPhysicalStageSlot_injective hlen) e f h
  grid := fun e => prefixPairBlock_grid P (prefixPhysicalStageSlot hlen)
    (prefixPhysicalStageSlot_injective hlen) (packed.rowPairs a (prefixNetworkGap hlen) hgap).gap
    (by intro edge j; exact prefixNetworkGap_stage hlen j edge.1 edge.2) e
  endpoints := by
    intro edge k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨rfl, bridgeStageLayer_endpoints layers hlen perms hperms j edge.1 edge.2⟩

end
end Sude
