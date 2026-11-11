import Sude.NetworkSwitches

/-! Preserve and join physically disjoint systems of network pairs. -/
namespace Sude
noncomputable section

/-- An existing system remains valid after changing the other cells, provided
the entries in both cells of every pair are preserved. -/
def RowNetworkPairs.rebase {n : ℕ} {α : Type*} {a : Cell n ≃ Fin (n * n)}
    (v : RowNetworkPairs α a) (b : Cell n ≃ Fin (n * n))
    (hfixed : ∀ x, entry b (rowNetworkSlot v x) = entry a (rowNetworkSlot v x)) :
    RowNetworkPairs α b where
  low := v.low
  high := v.high
  column := v.column
  rows_ne := v.rows_ne
  gap := v.gap
  gap_at := by
    intro k
    have hh := hfixed (k, true)
    have hl := hfixed (k, false)
    change entry b (v.high k, v.column k) = entry a (v.high k, v.column k) at hh
    change entry b (v.low k, v.column k) = entry a (v.low k, v.column k) at hl
    rw [hh, hl]
    exact v.gap_at k
  slots_injective := v.slots_injective
  low_main := v.low_main
  high_main := v.high_main
  low_anti := v.low_anti
  high_anti := v.high_anti

/-- The disjoint sum uses the actual cells and gaps from each system. The
cross-system condition covers both cells of every pair. -/
def RowNetworkPairs.join {n : ℕ} {α β : Type*} {a : Cell n ≃ Fin (n * n)}
    (u : RowNetworkPairs α a) (v : RowNetworkPairs β a)
    (hdisjoint : ∀ x y, rowNetworkSlot u x ≠ rowNetworkSlot v y) :
    RowNetworkPairs (Sum α β) a where
  low := Sum.elim u.low v.low
  high := Sum.elim u.high v.high
  column := Sum.elim u.column v.column
  rows_ne := by
    intro x
    cases x with
    | inl x => exact u.rows_ne x
    | inr x => exact v.rows_ne x
  gap := Sum.elim u.gap v.gap
  gap_at := by intro x; cases x <;> simp_all [u.gap_at, v.gap_at]
  slots_injective := by
    rintro ⟨x, s⟩ ⟨y, t⟩ h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have h' : rowNetworkSlot u (x, s) = rowNetworkSlot u (y, t) := by
          simpa [rowNetworkSlot] using h
        have heq := rowNetworkSlot_injective u h'
        cases heq
        rfl
      | inr y =>
        exfalso
        apply hdisjoint (x, s) (y, t)
        simpa [rowNetworkSlot] using h
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        apply hdisjoint (y, t) (x, s)
        simpa [rowNetworkSlot] using h.symm
      | inr y =>
        have h' : rowNetworkSlot v (x, s) = rowNetworkSlot v (y, t) := by
          simpa [rowNetworkSlot] using h
        have heq := rowNetworkSlot_injective v h'
        cases heq
        rfl
  low_main := by intro x; cases x <;> simp_all [u.low_main, v.low_main]
  high_main := by intro x; cases x <;> simp_all [u.high_main, v.high_main]
  low_anti := by intro x; cases x <;> simp_all [u.low_anti, v.low_anti]
  high_anti := by intro x; cases x <;> simp_all [u.high_anti, v.high_anti]

/-- A reservation containing every old slot and avoiding every new slot
provides the cross-system disjointness needed for the join. -/
theorem rowNetworkPairs_disjoint_of_reservation {n : ℕ} {α β : Type*}
    {a : Cell n ≃ Fin (n * n)} (u : RowNetworkPairs α a) (v : RowNetworkPairs β a)
    (reserved : Finset (Cell n)) (hold : ∀ x, rowNetworkSlot u x ∈ reserved)
    (hnew : ∀ y, rowNetworkSlot v y ∉ reserved) :
    ∀ x y, rowNetworkSlot u x ≠ rowNetworkSlot v y := by
  intro x y h
  exact hnew y (h ▸ hold x)

/-- Preserve an old physical reservoir inside the reserved cells and join it
to newly installed packed layers. The reservation supplies actual cell
disjointness; no separate abstract disjointness assumption is used. -/
def joinReservedPackedPairs {n : ℕ} {α : Type*} {a : Cell n ≃ Fin (n * n)}
    (old : RowNetworkPairs α a) (b : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (hold : ∀ x, rowNetworkSlot old x ∈ reserved)
    (hfixed : ∀ c ∈ reserved, entry b c = entry a c)
    (layers : List (LayerPacking.Layer n)) (packed : LayerPacking.PackedLayers reserved layers)
    (gap : Fin layers.length → Fin n → ℕ)
    (hgap : ∀ i e, entry b ((layers.get i).1 e, (layers.get i).2 e) =
      entry b (e, (layers.get i).2 e) + gap i e) :
    RowNetworkPairs (Sum α (Fin layers.length × Fin n)) b := by
  let old' := old.rebase b (fun x => hfixed _ (hold x))
  let fresh := packed.rowPairs b gap hgap
  apply old'.join fresh
  apply rowNetworkPairs_disjoint_of_reservation old' fresh reserved
  · exact hold
  · rintro ⟨⟨i, e⟩, side⟩ hmem
    have hs : LayerPacking.sequenceCell layers (i, (e, side)) ∈
        LayerPacking.layersSupport layers :=
      LayerPacking.layerSupport_subset (layers.get i) layers (List.get_mem layers i)
        (LayerPacking.sequenceCell_mem layers i (e, side))
    have hs' : rowNetworkSlot fresh ((i, e), side) ∈ LayerPacking.layersSupport layers := by
      simpa [fresh, rowNetworkSlot, LayerPacking.PackedLayers.rowPairs,
        LayerPacking.sequenceCell, LayerPacking.layerCell] using hs
    exact Finset.disjoint_left.mp packed.reserved_disjoint hmem hs'

end
end Sude
