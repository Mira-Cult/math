import Sude.LayerSequence

/-! Reuse already packed layers under smaller reservations and concatenate
successive packings. These are geometric statements only. -/
namespace Sude.LayerPacking
noncomputable section

/-- Physical supports commute with list concatenation. -/
theorem layersSupport_append {n : ℕ} (xs ys : List (Layer n)) :
    layersSupport (xs ++ ys) = layersSupport xs ∪ layersSupport ys := by
  induction xs with
  | nil => simp [layersSupport]
  | cons x xs ih => simp [layersSupport, ih, Finset.union_assoc]

/-- A packing which avoids a larger reservation also avoids any subset. -/
theorem PackedLayers.weaken_reservation {n : ℕ} {small large : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers large layers) (hsub : small ⊆ large) :
    PackedLayers small layers := by
  induction h generalizing small with
  | nil => exact PackedLayers.nil _
  | @cons large π f rest hinj hsafe hrows hcols htail ih =>
    refine PackedLayers.cons hinj ?_ hrows hcols ?_
    · intro z hz
      obtain ⟨hnot, hm, ha⟩ := hsafe z hz
      exact ⟨fun hs => hnot (hsub hs), hm, ha⟩
    · apply ih
      intro z hz
      rcases Finset.mem_union.mp hz with hs | hf
      · exact Finset.mem_union_left _ (hsub hs)
      · exact Finset.mem_union_right _ hf

/-- A disjoint extra reservation can be added without changing the packing. -/
theorem PackedLayers.extend_reservation {n : ℕ} {reserved extra : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers reserved layers)
    (hd : Disjoint extra (layersSupport layers)) :
    PackedLayers (reserved ∪ extra) layers := by
  induction h generalizing extra with
  | nil => exact PackedLayers.nil _
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    have hdhead : Disjoint extra (layerCells π f) := by
      apply hd.mono_right
      intro z hz
      exact Finset.mem_union_left _ hz
    have hdtail : Disjoint extra (layersSupport rest) := by
      apply hd.mono_right
      intro z hz
      exact Finset.mem_union_right _ hz
    refine PackedLayers.cons hinj ?_ hrows hcols ?_
    · intro z hz
      obtain ⟨hnot, hm, ha⟩ := hsafe z hz
      exact ⟨by
        intro hz'
        rcases Finset.mem_union.mp hz' with hr | he
        · exact hnot hr
        · exact Finset.disjoint_left.mp hdhead he hz, hm, ha⟩
    · have hp := ih hdtail
      simpa [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hp

/-- Two successive packings form a packed concatenated list when the second
avoids the first list and the original reservation. -/
theorem PackedLayers.append_packed {n : ℕ} {reserved : Finset (Cell n)}
    {xs ys : List (Layer n)} (hx : PackedLayers reserved xs)
    (hy : PackedLayers (reserved ∪ layersSupport xs) ys) :
    PackedLayers reserved (xs ++ ys) := by
  induction hx with
  | nil => simpa [layersSupport] using hy
  | @cons reserved π f rest hinj hsafe hrows hcols htail ih =>
    apply PackedLayers.cons hinj hsafe hrows hcols
    apply ih
    simpa [layersSupport, layerSupport, Finset.union_assoc] using hy

end
end Sude.LayerPacking
