import Sude.BridgeRectangles

/-! A finite sequence of independent RP1 rectangle trades. -/
namespace Sude
noncomputable section

def packedTrade {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (i : Fin L) : Cell n ≃ Fin (n * n) :=
  rectangleTrade a (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
    (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i)

def packedTradeSequence {L n : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) : List (Fin L) → Cell n ≃ Fin (n * n)
  | [] => a
  | i :: rest => packedTradeSequence hs choice (packedTrade hs choice a i) rest

/-- One packed trade has its complete row, column and both-diagonal effect. -/
theorem packedTrade_effect {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n)) (i : Fin L) (gap : ℕ)
    (htop : entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap)
    (hbot : entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap) :
    (∀ r, rowSum (packedTrade hs choice a i) r = rowSum a r) ∧
    (∀ c, columnSum (packedTrade hs choice a i) c = columnSum a c) ∧
    (mainSum (packedTrade hs choice a i) : ℤ) = (mainSum a : ℤ) +
      (if choice i then (gap : ℤ) else 0) ∧
    (antiSum (packedTrade hs choice a i) : ℤ) = (antiSum a : ℤ) +
      (if choice i then 0 else (gap : ℤ)) := by
  have hr := RectanglePacking.firstRow_ne_secondRow hs i i
  have hc := RectanglePacking.firstColumn_ne_secondColumn hs choice i i
  have ho1 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice i
  have ho2 := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice i
  have ho3 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice i
  have hrows := rectangleTrade_rows a _ _ _ _ gap hr hc htop hbot
  have hcols := rectangleTrade_columns a _ _ _ _ gap hr hc htop hbot
  cases hchoice : choice i with
  | true =>
    have hcorner := (RectanglePacking.designated_corner_geometry hs choice i).1 hchoice
    have hm := rectangleTrade_main a _ _ _ _ gap hr hc htop hbot
      hcorner.1 ho1.1 ho2.1 ho3.1 hcorner.2 ho1.2 ho2.2 ho3.2
    refine ⟨hrows, hcols, ?_, ?_⟩
    · simpa [packedTrade, hchoice] using hm.1
    · simp [packedTrade, hm.2]
  | false =>
    have hcorner := (RectanglePacking.designated_corner_geometry hs choice i).2 hchoice
    have ha := rectangleTrade_anti a _ _ _ _ gap hr hc htop hbot
      hcorner.1 ho1.2 ho2.2 ho3.2 hcorner.2 ho1.1 ho2.1 ho3.1
    refine ⟨hrows, hcols, ?_, ?_⟩
    · simp [packedTrade, ha.2]
    · simpa [packedTrade, hchoice] using ha.1

/-- A packed trade fixes every cell outside its actual four-cell support. -/
theorem packedTrade_fixes_outside {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n)) (i : Fin L) (c : Cell n)
    (hc : c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
      (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i)) :
    entry (packedTrade hs choice a i) c = entry a c := by
  simp only [mem_rectangleCells, not_or] at hc
  exact rectangleTrade_outside a _ _ _ _ c hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- An arbitrary finite sequence fixes any cell outside every traded
rectangle, including reserved cells and the center when applicable. -/
theorem packedTradeSequence_fixes_outside {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n)) (labels : List (Fin L))
    (c : Cell n) (hc : ∀ i ∈ labels, c ∉
      rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i)) :
    entry (packedTradeSequence hs choice a labels) c = entry a c := by
  induction labels generalizing a with
  | nil => rfl
  | cons i rest ih =>
    have htail : ∀ j ∈ rest, c ∉ rectangleCells (RectanglePacking.firstRow hs j)
        (RectanglePacking.secondRow hs j) (RectanglePacking.firstColumn hs choice j)
        (RectanglePacking.secondColumn hs choice j) := by
      intro j hj
      exact hc j (by simp [hj])
    have hhead := packedTrade_fixes_outside hs choice a i c (hc i (by simp))
    exact (ih (packedTrade hs choice a i) htail).trans hhead

def packedMainGain {L : ℕ} (choice : Fin L → Bool) (gap : Fin L → ℕ)
    (labels : List (Fin L)) : ℤ :=
  (labels.map fun i => if choice i then (gap i : ℤ) else 0).sum

def packedAntiGain {L : ℕ} (choice : Fin L → Bool) (gap : Fin L → ℕ)
    (labels : List (Fin L)) : ℤ :=
  (labels.map fun i => if choice i then 0 else (gap i : ℤ)).sum

/-- All distinct packed rectangles can be switched in sequence. Every row
and column remains fixed; each full diagonal gains exactly the sum of the
gaps assigned to it. The later trades use their actual unchanged entries. -/
theorem packedTradeSequence_effect {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n * n)) (gap : Fin L → ℕ)
    (labels : List (Fin L)) (hnodup : labels.Nodup)
    (hgaps : ∀ i ∈ labels,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i) :
    (∀ r, rowSum (packedTradeSequence hs choice a labels) r = rowSum a r) ∧
    (∀ c, columnSum (packedTradeSequence hs choice a labels) c = columnSum a c) ∧
    (mainSum (packedTradeSequence hs choice a labels) : ℤ) =
      (mainSum a : ℤ) + packedMainGain choice gap labels ∧
    (antiSum (packedTradeSequence hs choice a labels) : ℤ) =
      (antiSum a : ℤ) + packedAntiGain choice gap labels := by
  induction labels generalizing a with
  | nil => simp [packedTradeSequence, packedMainGain, packedAntiGain]
  | cons i rest ih =>
    have ⟨hnot, htailNodup⟩ := List.nodup_cons.mp hnodup
    have hfirst := hgaps i (by simp)
    have hsingle := packedTrade_effect hs hL choice a i (gap i) hfirst.1 hfirst.2
    have htailGaps : ∀ j ∈ rest,
        entry (packedTrade hs choice a i)
            (RectanglePacking.firstRow hs j, RectanglePacking.secondColumn hs choice j) =
          entry (packedTrade hs choice a i)
            (RectanglePacking.firstRow hs j, RectanglePacking.firstColumn hs choice j) + gap j ∧
        entry (packedTrade hs choice a i)
            (RectanglePacking.secondRow hs j, RectanglePacking.firstColumn hs choice j) =
          entry (packedTrade hs choice a i)
            (RectanglePacking.secondRow hs j, RectanglePacking.secondColumn hs choice j) + gap j := by
      intro j hj
      have hij : i ≠ j := by intro h; subst j; exact hnot hj
      have hd := RectanglePacking.rectangle_cells_disjoint hs choice i j hij
      have hjgap := hgaps j (by simp [hj])
      exact rectangleTrade_other_gaps_unchanged a _ _ _ _ _ _ _ _ (gap j) hd hjgap.1 hjgap.2
    have hrec := ih (packedTrade hs choice a i) htailNodup htailGaps
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      exact (hrec.1 r).trans (hsingle.1 r)
    · intro c
      exact (hrec.2.1 c).trans (hsingle.2.1 c)
    · change (mainSum (packedTradeSequence hs choice (packedTrade hs choice a i) rest) : ℤ) = _
      rw [hrec.2.2.1, hsingle.2.2.1]
      simp [packedMainGain, add_assoc, add_comm, add_left_comm]
    · change (antiSum (packedTradeSequence hs choice (packedTrade hs choice a i) rest) : ℤ) = _
      rw [hrec.2.2.2, hsingle.2.2.2]
      simp [packedAntiGain, add_assoc, add_comm, add_left_comm]

/-- Switch any duplicate-free list of installed bridge rectangles. The
full diagonal gains use their actual selected gaps; every reserved cell,
the center, and every unselected packed rectangle remains unchanged. -/
theorem selected_bridge_trade_sequence {n k J L D : ℕ}
    (batches : ℕ → List DoublePair) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (select : Fin D → Fin J × Fin k)
    (rectangle : Fin D → Fin L) (hrectangle : Function.Injective rectangle)
    (a : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hfree : ∀ d, Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (rectangle d))
        (RectanglePacking.secondRow hs (rectangle d))
        (RectanglePacking.firstColumn hs choice (rectangle d))
        (RectanglePacking.secondColumn hs choice (rectangle d))) reservedCells)
    (hgap : ∀ d,
      entry a (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) =
        entry a (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) +
            selectedBridgeGap batches (select d).2 (select d).1 ∧
      entry a (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) =
        entry a (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) +
            selectedBridgeGap batches (select d).2 (select d).1)
    (labels : List (Fin D)) (hnodup : labels.Nodup) (hn : 0 < n) :
    let result := packedTradeSequence hs choice a (labels.map rectangle)
    (∀ r, rowSum result r = rowSum a r) ∧
    (∀ c, columnSum result c = columnSum a c) ∧
    (mainSum result : ℤ) = (mainSum a : ℤ) +
      (labels.map fun d => if choice (rectangle d) then
        (selectedBridgeGap batches (select d).2 (select d).1 : ℤ) else 0).sum ∧
    (antiSum result : ℤ) = (antiSum a : ℤ) +
      (labels.map fun d => if choice (rectangle d) then 0 else
        (selectedBridgeGap batches (select d).2 (select d).1 : ℤ)).sum ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
    entry result (centerIndex n hn, centerIndex n hn) = entry a (centerIndex n hn, centerIndex n hn) ∧
    (∀ c ∈ reservedCells, entry result c = entry a c) ∧
    (∀ d, d ∉ labels → ∀ side,
      entry result (packedRectangleCorner hs choice (rectangle d, side)) =
        entry a (packedRectangleCorner hs choice (rectangle d, side))) := by
  let chosenGap : Fin D → ℕ := fun d => selectedBridgeGap batches (select d).2 (select d).1
  let allGap : Fin L → ℕ := Function.extend rectangle chosenGap (fun _ => 0)
  have hext : ∀ d, allGap (rectangle d) = chosenGap d := by
    intro d
    exact hrectangle.extend_apply chosenGap (fun _ => 0) d
  have hnodup' : (labels.map rectangle).Nodup := hnodup.map hrectangle
  have hgaps : ∀ i ∈ labels.map rectangle,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + allGap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + allGap i := by
    intro i hi
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
    simpa only [hext] using hgap d
  have heffect := packedTradeSequence_effect hs hL choice a allGap (labels.map rectangle) hnodup' hgaps
  have hmain : packedMainGain choice allGap (labels.map rectangle) =
      (labels.map fun d => if choice (rectangle d) then (chosenGap d : ℤ) else 0).sum := by
    simp [packedMainGain, List.map_map, Function.comp_def, hext]
  have hanti : packedAntiGain choice allGap (labels.map rectangle) =
      (labels.map fun d => if choice (rectangle d) then 0 else (chosenGap d : ℤ)).sum := by
    simp [packedAntiGain, List.map_map, Function.comp_def, hext]
  refine ⟨heffect.1, heffect.2.1, ?_, ?_, entry_range _, entry_injective _, ?_, ?_, ?_⟩
  · simpa only [hmain] using heffect.2.2.1
  · simpa only [hanti] using heffect.2.2.2
  · apply packedTradeSequence_fixes_outside
    intro i _
    exact RectanglePacking.rectangle_avoids_center hs hn choice i
  · intro c hc
    apply packedTradeSequence_fixes_outside
    intro i hi
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
    intro hm
    exact Finset.disjoint_left.mp (hfree d) hm hc
  · intro d hd side
    apply packedTradeSequence_fixes_outside
    intro i hi
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hi
    have hne : rectangle e ≠ rectangle d := by
      intro h
      have : e = d := hrectangle h
      exact hd (this ▸ he)
    have hdisj := RectanglePacking.rectangle_cells_disjoint hs choice (rectangle e) (rectangle d) hne
    intro hm
    exact Finset.disjoint_left.mp hdisj hm (packedRectangleCorner_mem hs choice (rectangle d) side)

/-- Comparing two actual orientations yields signed changes on both
diagonals while keeping all rows, columns, reserved cells and the center
fixed. The two orientations may select different subsets of rectangles. -/
theorem selected_bridge_orientation_difference {n k J L D : ℕ}
    (batches : ℕ → List DoublePair) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (select : Fin D → Fin J × Fin k)
    (rectangle : Fin D → Fin L) (hrectangle : Function.Injective rectangle)
    (a : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hfree : ∀ d, Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (rectangle d))
        (RectanglePacking.secondRow hs (rectangle d))
        (RectanglePacking.firstColumn hs choice (rectangle d))
        (RectanglePacking.secondColumn hs choice (rectangle d))) reservedCells)
    (hgap : ∀ d,
      entry a (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) =
        entry a (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) +
            selectedBridgeGap batches (select d).2 (select d).1 ∧
      entry a (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) =
        entry a (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) +
            selectedBridgeGap batches (select d).2 (select d).1)
    (before after : List (Fin D)) (hbefore : before.Nodup) (hafter : after.Nodup)
    (hn : 0 < n) :
    let base := packedTradeSequence hs choice a (before.map rectangle)
    let result := packedTradeSequence hs choice a (after.map rectangle)
    (∀ r, rowSum result r = rowSum base r) ∧
    (∀ c, columnSum result c = columnSum base c) ∧
    (mainSum result : ℤ) - (mainSum base : ℤ) =
      (after.map fun d => if choice (rectangle d) then
        (selectedBridgeGap batches (select d).2 (select d).1 : ℤ) else 0).sum -
      (before.map fun d => if choice (rectangle d) then
        (selectedBridgeGap batches (select d).2 (select d).1 : ℤ) else 0).sum ∧
    (antiSum result : ℤ) - (antiSum base : ℤ) =
      (after.map fun d => if choice (rectangle d) then 0 else
        (selectedBridgeGap batches (select d).2 (select d).1 : ℤ)).sum -
      (before.map fun d => if choice (rectangle d) then 0 else
        (selectedBridgeGap batches (select d).2 (select d).1 : ℤ)).sum ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
    entry result (centerIndex n hn, centerIndex n hn) =
      entry base (centerIndex n hn, centerIndex n hn) ∧
    (∀ c ∈ reservedCells, entry result c = entry base c) := by
  have hb := selected_bridge_trade_sequence batches hs hL choice select rectangle hrectangle
    a reservedCells hfree hgap before hbefore hn
  have ha := selected_bridge_trade_sequence batches hs hL choice select rectangle hrectangle
    a reservedCells hfree hgap after hafter hn
  refine ⟨?_, ?_, ?_, ?_, ha.2.2.2.2.1, ha.2.2.2.2.2.1, ?_, ?_⟩
  · intro r
    exact (ha.1 r).trans (hb.1 r).symm
  · intro c
    exact (ha.2.1 c).trans (hb.2.1 c).symm
  · linarith [ha.2.2.1, hb.2.2.1]
  · linarith [ha.2.2.2.1, hb.2.2.2.1]
  · exact ha.2.2.2.2.2.2.1.trans hb.2.2.2.2.2.2.1.symm
  · intro c hc
    exact (ha.2.2.2.2.2.2.2.1 c hc).trans (hb.2.2.2.2.2.2.2.1 c hc).symm

/-- The selected actual-pool bridge blocks can be installed in RP1
rectangles and any subset switched with the proved full line effects.
This does not place the remaining ordinary bridge pairs. -/
theorem install_and_trade_selected_bridge_rectangles (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (k J L D : ℕ) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (select : Fin D → Fin J × Fin k) (hselect : Function.Injective select)
    (rectangle : Fin D → Fin L) (hrectangle : Function.Injective rectangle)
    (a : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial)
    (hfree : ∀ d, Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (rectangle d))
        (RectanglePacking.secondRow hs (rectangle d))
        (RectanglePacking.firstColumn hs choice (rectangle d))
        (RectanglePacking.secondColumn hs choice (rectangle d))) reservedCells) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ d side, entry a' (packedRectangleCorner hs choice (rectangle d, side)) =
        bridgeStageEndpoint n initial radii batches k J hvalid (select d, side)) ∧
      (∀ c ∈ reservedCells, entry a' c = entry a c) ∧
      (∀ labels : List (Fin D), labels.Nodup →
        let result := packedTradeSequence hs choice a' (labels.map rectangle)
        (∀ r, rowSum result r = rowSum a' r) ∧
        (∀ c, columnSum result c = columnSum a' c) ∧
        (mainSum result : ℤ) = (mainSum a' : ℤ) +
          (labels.map fun d => if choice (rectangle d) then
            (selectedBridgeGap batches (select d).2 (select d).1 : ℤ) else 0).sum ∧
        (antiSum result : ℤ) = (antiSum a' : ℤ) +
          (labels.map fun d => if choice (rectangle d) then 0 else
            (selectedBridgeGap batches (select d).2 (select d).1 : ℤ)).sum ∧
        Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
        entry result (centerIndex n (by omega), centerIndex n (by omega)) =
          entry a' (centerIndex n (by omega), centerIndex n (by omega)) ∧
        (∀ c ∈ reservedCells, entry result c = entry a c) ∧
        (∀ d, d ∉ labels → ∀ side,
          entry result (packedRectangleCorner hs choice (rectangle d, side)) =
            entry a' (packedRectangleCorner hs choice (rectangle d, side)))) := by
  obtain ⟨a', hplace, hfixed, hgaps⟩ := install_selected_bridge_rectangles bmor upper n initial
    radii batches k J L D hvalid hn hnmax hpositive hs choice select hselect rectangle hrectangle
    a reservedCells hreserved hfree
  refine ⟨a', hplace, hfixed, ?_⟩
  intro labels hnodup
  have hpair : ∀ d,
      entry a' (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) =
        entry a' (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) +
            selectedBridgeGap batches (select d).2 (select d).1 ∧
      entry a' (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) =
        entry a' (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) +
            selectedBridgeGap batches (select d).2 (select d).1 := fun d => (hgaps d).2
  have ht := selected_bridge_trade_sequence batches hs hL choice select rectangle hrectangle
    a' reservedCells hfree hpair labels hnodup (by omega)
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1,
    ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ?_, ht.2.2.2.2.2.2.2.2⟩
  intro c hc
  exact (ht.2.2.2.2.2.2.2.1 c hc).trans (hfixed c hc)

end
end Sude
