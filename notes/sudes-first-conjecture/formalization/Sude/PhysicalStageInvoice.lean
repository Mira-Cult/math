import Sude.PrefixStageInvoice
import Sude.LayerSequence
import Sude.LayerIncidenceInvoice

/-! Connect the ordinary stage invoice to actual packed network layers. -/
namespace Sude
noncomputable section

/-- Every packed layer's edge permutation is a derangement. -/
theorem LayerPacking.PackedLayers.get_derange {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (packed : LayerPacking.PackedLayers reserved layers)
    (j : Fin layers.length) (i : Fin n) : (layers.get j).1 i ≠ i := by
  intro heq
  have hinj := (packed.each_layer (layers.get j) (List.get_mem _ _)).1
  have hc : LayerPacking.layerCell (layers.get j).1 (layers.get j).2 (i, false) =
      LayerPacking.layerCell (layers.get j).1 (layers.get j).2 (i, true) := by
    change (i, (layers.get j).2 i) = ((layers.get j).1 i, (layers.get j).2 i)
    exact congrArg (fun t => (t, (layers.get j).2 i)) heq.symm
  have hfalse : false = true := congrArg Prod.snd (hinj hc)
  cases hfalse

/-- One layer of the actual packed list, indexed by prefix stage and layer. -/
def prefixStageLayer {P layers n : ℕ} (network : List (LayerPacking.Layer n))
    (hlen : network.length = P * layers) (j : Fin P) (k : Fin layers) : LayerPacking.Layer n :=
  network.get (Fin.cast hlen.symm (finProdFinEquiv (j, k)))

/-- Ordinary row incidence weights of the actual row and transposed-column
network layers belonging to one stage. -/
def physicalRowStageInvoice {P layers n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (j : Fin P) (r : Fin n) : ℝ :=
  ∑ k : Fin layers,
    ((∑ i, (LayerPacking.layerRowWeight (prefixStageLayer rows hrows j k).1
      (prefixStageLayer rows hrows j k).2 r i) ^ 2) +
    ∑ i, (LayerPacking.layerColumnWeight (prefixStageLayer cols hcols j k).1
      (prefixStageLayer cols hcols j k).2 r i) ^ 2)

/-- Ordinary column incidence weights of the same actual network layers. -/
def physicalColumnStageInvoice {P layers n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hrows : rows.length = P * layers) (hcols : cols.length = P * layers)
    (j : Fin P) (c : Fin n) : ℝ :=
  ∑ k : Fin layers,
    ((∑ i, (LayerPacking.layerColumnWeight (prefixStageLayer rows hrows j k).1
      (prefixStageLayer rows hrows j k).2 c i) ^ 2) +
    ∑ i, (LayerPacking.layerRowWeight (prefixStageLayer cols hcols j k).1
      (prefixStageLayer cols hcols j k).2 c i) ^ 2)

/-- The actual packed ordinary networks contribute exactly `3d` to each row
at every stage when there are `d/2` layers in each orientation. -/
theorem physicalRowStageInvoice_eq {P layers n d : ℕ} (hd : d = 2 * layers)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved rows) (j : Fin P) (r : Fin n) :
    physicalRowStageInvoice rows cols hrows hcols j r = 3 * (d : ℝ) := by
  apply LayerPacking.ordinary_stage_row_squared_invoice hd
  intro k i
  exact packed.get_derange (Fin.cast hrows.symm (finProdFinEquiv (j, k))) i

/-- The actual packed ordinary networks contribute exactly `3d` to each
column at every stage. -/
theorem physicalColumnStageInvoice_eq {P layers n d : ℕ} (hd : d = 2 * layers)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved cols) (j : Fin P) (c : Fin n) :
    physicalColumnStageInvoice rows cols hrows hcols j c = 3 * (d : ℝ) := by
  apply LayerPacking.ordinary_stage_column_squared_invoice hd
  intro k i
  exact packed.get_derange (Fin.cast hcols.symm (finProdFinEquiv (j, k))) i

/-- The actual packed networks and selected rectangle geometry jointly obey
the source-form width invoice for a row. -/
theorem physical_prefix_row_width_invoice {P layers n d L : ℕ} (hd : d = 2 * layers)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved rows) (r : Fin n) (width : Fin P → ℝ) (z : ℝ)
    (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * (physicalRowStageInvoice rows cols hrows hcols j r +
      prefixRectangleStageInvoice hrect hs choice (fun c => c.1 = r) j)) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  apply prefix_row_combined_width_invoice hrect hs choice r width _ z _ hwidth
  intro j
  exact le_of_eq (physicalRowStageInvoice_eq hd rows cols hrows hcols reserved packed j r)

/-- The corresponding physical column invoice. -/
theorem physical_prefix_column_width_invoice {P layers n d L : ℕ} (hd : d = 2 * layers)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved cols) (c : Fin n) (width : Fin P → ℝ) (z : ℝ)
    (hwidth : ∀ j, (width j) ^ 2 ≤ z ^ 2) :
    (∑ j, (width j) ^ 2 * (physicalColumnStageInvoice rows cols hrows hcols j c +
      prefixRectangleStageInvoice hrect hs choice (fun x => x.2 = c) j)) ≤
      3 * (d : ℝ) * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
  apply prefix_column_combined_width_invoice hrect hs choice c width _ z _ hwidth
  intro j
  exact le_of_eq (physicalColumnStageInvoice_eq hd rows cols hrows hcols reserved packed j c)

end
end Sude
