import Sude.FamilyGrid

/-! Construct a centered network from globally injective supported grid labels.
The supplied grids and endpoints may come from actual physical slot maps.
No flow or line-demand conclusion is asserted. -/
namespace Sude
noncomputable section

/-- Globally injective supported-label and edge slots define disjoint
reservoirs. The grid and endpoint facts are the supplied physical facts. -/
def centeredNetwork_of_supported_grids {n : ℕ} {E K α : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq K] [DecidableEq α]
    {a : Cell n ≃ Fin (n * n)} (v : RowNetworkPairs K a)
    (labels : Finset α) (slot : {x // x ∈ labels} × E → K)
    (hinj : Function.Injective slot) (radius : E → ℕ)
    (source target : E → Fin n)
    (hgrid : ∀ e, CompleteEvenGrid (labels.attach.image (fun x => slot (x, e))) v.gap (radius e))
    (hend : ∀ (e : E) (x : {x // x ∈ labels}),
      v.low (slot (x, e)) = source e ∧ v.high (slot (x, e)) = target e) :
    CenteredNetwork E K v where
  block e := labels.attach.image (fun x => slot (x, e))
  radius := radius
  source := source
  target := target
  disjoint := by
    intro e f hne
    apply Finset.disjoint_left.mpr
    intro k hk hl
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hk
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hl
    have h := hinj (hx.trans hy.symm)
    exact hne (congrArg Prod.snd h)
  grid := hgrid
  endpoints := by
    intro e k hk
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hk
    exact hend e x

end
end Sude
