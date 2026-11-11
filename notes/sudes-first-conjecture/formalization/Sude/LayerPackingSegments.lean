import Sude.LayerPackingConcatenate

/-! Consecutive sublists of a packed layer sequence remain packed under the
original reservation. -/
namespace Sude.LayerPacking
noncomputable section

theorem PackedLayers.prefix {n : ℕ} {reserved : Finset (Cell n)}
    (xs ys : List (Layer n)) (h : PackedLayers reserved (xs ++ ys)) :
    PackedLayers reserved xs := by
  induction xs generalizing reserved with
  | nil => exact PackedLayers.nil _
  | cons x xs ih =>
    cases h with
    | cons hinj hsafe hrows hcols htail =>
      exact PackedLayers.cons hinj hsafe hrows hcols (ih htail)

theorem PackedLayers.suffix {n : ℕ} {reserved : Finset (Cell n)}
    (xs ys : List (Layer n)) (h : PackedLayers reserved (xs ++ ys)) :
    PackedLayers reserved ys := by
  induction xs generalizing reserved with
  | nil => simpa using h
  | cons x xs ih =>
    cases h with
    | @cons reserved π f rest hinj hsafe hrows hcols htail =>
      exact (ih htail).weaken_reservation Finset.subset_union_left

theorem PackedLayers.segment {n : ℕ} {reserved : Finset (Cell n)}
    (xs ys zs : List (Layer n)) (h : PackedLayers reserved ((xs ++ ys) ++ zs)) :
    PackedLayers reserved ys :=
  (h.prefix (xs ++ ys) zs).suffix xs ys

end
end Sude.LayerPacking
