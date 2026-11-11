import Sude.LayerTranspose

/-! Sequential row and column network installation. The caller supplies the
actual globally disjoint pool values and derangements; graph expansion,
prime-population certification and later corrections remain separate. -/
namespace Sude.LayerPacking
noncomputable section

/-- Install two finite layer networks in the same actual square. The column
network reserves every row-layer cell before it is placed, and the proof
retains all earlier entries and gap equations. -/
theorem pack_and_install_two_networks {n L : ℕ}
    (rowPerms colPerms : List (Equiv.Perm (Fin n))) (reserved : Finset (Cell n))
    (hrowDerange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcolDerange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (hrowLoad : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcolLoad : ∀ i, (colUsed reserved i).card ≤ L)
    (hn : 4 * (L + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n))
    (rowValues : (Fin rowPerms.length × (Fin n × Bool)) → pool n)
    (colValues : (Fin colPerms.length × (Fin n × Bool)) → pool n)
    (hrowValues : Function.Injective rowValues)
    (hcolValues : Function.Injective colValues)
    (hseparate : ∀ x y, (rowValues x).val ≠ (colValues y).val)
    (hrowAvoid : ∀ x c, c ∈ reserved → (rowValues x).val ≠ entry a c)
    (hcolAvoid : ∀ x c, c ∈ reserved → (colValues x).val ≠ entry a c)
    (rowGap : Fin rowPerms.length → Fin n → ℕ)
    (colGap : Fin colPerms.length → Fin n → ℕ)
    (hrowGap : ∀ i e, (rowValues (i, (e, true))).val =
      (rowValues (i, (e, false))).val + rowGap i e)
    (hcolGap : ∀ i e, (colValues (i, (e, true))).val =
      (colValues (i, (e, false))).val + colGap i e) :
    ∃ (rows cols : List (Layer n)) (hrlen : rows.length = rowPerms.length)
      (hclen : cols.length = colPerms.length) (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      PackedLayers reserved rows ∧
      PackedLayers (transposeCells (reserved ∪ layersSupport rows)) cols ∧
      Disjoint (layersSupport rows) (transposeCells (layersSupport cols)) ∧
      (∀ z ∈ layersSupport rows, z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ z ∈ transposeCells (layersSupport cols), z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ x, entry b (sequenceCell rows x) =
        (rowValues (Fin.cast hrlen x.1, x.2)).val) ∧
      (∀ x, entry b (sequenceCell cols x).swap =
        (colValues (Fin.cast hclen x.1, x.2)).val) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + rowGap (Fin.cast hrlen i) e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + colGap (Fin.cast hclen i) e) ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      (∀ r, ((layersSupport rows).filter (fun z => z.1 = r)).card = 2 * rowPerms.length ∧
        ((transposeCells (layersSupport cols)).filter (fun z => z.1 = r)).card = 2 * colPerms.length) ∧
      (∀ c, ((layersSupport rows).filter (fun z => z.2 = c)).card = 2 * rowPerms.length ∧
        ((transposeCells (layersSupport cols)).filter (fun z => z.2 = c)).card = 2 * colPerms.length) ∧
      (∀ r, (((layersSupport rows) ∪ transposeCells (layersSupport cols)).filter
        (fun z => z.1 = r)).card = 2 * (rowPerms.length + colPerms.length)) ∧
      (∀ c, (((layersSupport rows) ∪ transposeCells (layersSupport cols)).filter
        (fun z => z.2 = c)).card = 2 * (rowPerms.length + colPerms.length)) := by
  have hnRow : 4 * (L + 2 * rowPerms.length) + 8 < n := by omega
  obtain ⟨rows, hrlen, br, hrmap, hrpacked, hrphysical, hrplaced, hrfixed, hrrows, hrcols⟩ :=
    pack_and_install_finite_layers rowPerms reserved hrowDerange hrowLoad hcolLoad hnRow
      a rowValues hrowValues hrowAvoid rowGap hrowGap
  obtain ⟨hrload', hcload'⟩ := hrpacked.union_load hrowLoad hcolLoad
  have hrowLoad' : ∀ i, (rowUsed (reserved ∪ layersSupport rows) i).card ≤ L + 2 * rowPerms.length := by
    simpa [hrlen] using hrload'
  have hcolLoad' : ∀ i, (colUsed (reserved ∪ layersSupport rows) i).card ≤ L + 2 * rowPerms.length := by
    simpa [hrlen] using hcload'
  have hcolAvoid' : ∀ x c, c ∈ reserved ∪ layersSupport rows → (colValues x).val ≠ entry br c := by
    intro x c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rw [hrfixed c hc]
      exact hcolAvoid x c hc
    · obtain ⟨y, hy⟩ := sequenceCell_covers rows c hc
      subst c
      rw [hrplaced y]
      exact (hseparate (Fin.cast hrlen y.1, y.2) x).symm
  obtain ⟨cols, hclen, b, hcmap, hcpacked, hcphysical, hcplaced, hcfixed,
      hcsafe, hcrows, hccols⟩ :=
    pack_and_install_column_layers colPerms (reserved ∪ layersSupport rows) hcolDerange
      hrowLoad' hcolLoad' hn br colValues hcolValues hcolAvoid' colGap hcolGap
  have hdisjoint : Disjoint (layersSupport rows) (transposeCells (layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hzr hzc
    exact (hcsafe z hzc).1 (Finset.mem_union_right reserved hzr)
  refine ⟨rows, cols, hrlen, hclen, b, hrmap, hcmap, hrpacked, hcpacked, hdisjoint,
    ?_, ?_, ?_, hcplaced, ?_, hcphysical, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hoff := hrpacked.support_off_diagonals z hz
    refine ⟨?_, hoff.1, hoff.2⟩
    intro hr
    exact Finset.disjoint_left.mp hrpacked.reserved_disjoint hr hz
  · intro z hz
    obtain ⟨hnot, hm, ha⟩ := hcsafe z hz
    exact ⟨fun hr => hnot (Finset.mem_union_left _ hr), hm, ha⟩
  · intro x
    have hmem : sequenceCell rows x ∈ layersSupport rows :=
      layerSupport_subset (rows.get x.1) rows (List.get_mem rows x.1) (sequenceCell_mem rows x.1 x.2)
    rw [hcfixed _ (Finset.mem_union_right reserved hmem), hrplaced]
  · intro i e
    have hlow : (e, (rows.get i).2 e) ∈ layersSupport rows := by
      have h := layerSupport_subset (rows.get i) rows (List.get_mem rows i)
        (sequenceCell_mem rows i (e, false))
      simpa [sequenceCell, layerCell] using h
    have hhigh : ((rows.get i).1 e, (rows.get i).2 e) ∈ layersSupport rows := by
      have h := layerSupport_subset (rows.get i) rows (List.get_mem rows i)
        (sequenceCell_mem rows i (e, true))
      simpa [sequenceCell, layerCell] using h
    rw [hcfixed _ (Finset.mem_union_right reserved hhigh),
      hcfixed _ (Finset.mem_union_right reserved hlow)]
    exact hrphysical i e
  · intro c hc
    exact (hcfixed c (Finset.mem_union_left _ hc)).trans (hrfixed c hc)
  · intro r
    exact ⟨hrrows r, hcrows r⟩
  · intro c
    exact ⟨hrcols c, hccols c⟩
  · intro r
    have hd : Disjoint ((layersSupport rows).filter (fun z => z.1 = r))
        ((transposeCells (layersSupport cols)).filter (fun z => z.1 = r)) :=
      hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [Finset.filter_union, Finset.card_union_of_disjoint hd, hrrows r, hcrows r]
    omega
  · intro c
    have hd : Disjoint ((layersSupport rows).filter (fun z => z.2 = c))
        ((transposeCells (layersSupport cols)).filter (fun z => z.2 = c)) :=
      hdisjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [Finset.filter_union, Finset.card_union_of_disjoint hd, hrcols c, hccols c]
    omega

/-- PB8--PB9's final source load pays for both network sequences when their
combined number of layers is `d*S`. This is an integer identity and does
not assume any of the controller's numerical gates. -/
theorem pb9_capacity_for_two_networks (n d S h kr kc : ℕ)
    (hcount : kr + kc = d * S)
    (hpb : 4 * (2 * d * S + 6 * (h - 1) + 2) + 8 < n) :
    4 * ((6 * (h - 1) + 2) + 2 * kr + 2 * kc) + 8 < n := by
  have heq : 2 * d * S = 2 * (kr + kc) := by rw [hcount, Nat.mul_assoc]
  rw [heq] at hpb
  omega

end
end Sude.LayerPacking
