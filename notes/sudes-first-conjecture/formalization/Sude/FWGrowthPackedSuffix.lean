import Sude.LayerPackingConcatenate

/-! A suffix of a joint layer packing remains packed against its original
reservation. This is a geometric restriction, not an existence theorem. -/
namespace Sude.LayerPacking
noncomputable section

/-- Discarding a packed prefix preserves packing of the remaining layers.
The suffix originally avoids an enlarged reservation; weakening it recovers
the original reservation. -/
theorem packed_layers_suffix {n : ℕ} (xs ys : List (Layer n))
    {reserved : Finset (Cell n)} (h : PackedLayers reserved (xs ++ ys)) :
    PackedLayers reserved ys := by
  induction xs generalizing reserved with
  | nil => simpa using h
  | cons x xs ih =>
    cases x with
    | mk π f =>
      cases h with
      | cons hinj hsafe hrows hcols htail =>
        exact (ih htail).weaken_reservation (Finset.subset_union_left)

end
end Sude.LayerPacking
