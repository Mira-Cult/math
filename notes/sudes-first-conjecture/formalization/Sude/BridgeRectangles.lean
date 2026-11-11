import Sude.BridgePhysical
import Sude.RectanglePacking

/-! Install selected bridge blocks into the source's packed diagonal
rectangles. Ordinary bridge pairs are not assigned by this module. -/
namespace Sude
noncomputable section

/-- The four RP1 cells in the orientation required by a rectangle trade. -/
def packedRectangleCorner {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (x : Fin L × Fin 4) : Cell n :=
  ![(RectanglePacking.firstRow hs x.1, RectanglePacking.firstColumn hs choice x.1),
    (RectanglePacking.firstRow hs x.1, RectanglePacking.secondColumn hs choice x.1),
    (RectanglePacking.secondRow hs x.1, RectanglePacking.firstColumn hs choice x.1),
    (RectanglePacking.secondRow hs x.1, RectanglePacking.secondColumn hs choice x.1)] x.2

theorem packedRectangleCorner_mem {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (i : Fin L) (side : Fin 4) :
    packedRectangleCorner hs choice (i, side) ∈
      rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i) := by
  fin_cases side <;> simp [packedRectangleCorner, rectangleCells]

/-- RP1 gives four distinct cells per rectangle and disjoint supports for
different rectangles. -/
theorem packedRectangleCorner_injective {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) : Function.Injective (packedRectangleCorner hs choice) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ heq
  by_cases hij : i = j
  · subst j
    have hr := RectanglePacking.firstRow_ne_secondRow hs i i
    have hc := RectanglePacking.firstColumn_ne_secondColumn hs choice i i
    have hst : s = t := by
      fin_cases s <;> fin_cases t <;> simp_all [packedRectangleCorner, Prod.mk.injEq]
    cases hst
    rfl
  · have hd := RectanglePacking.rectangle_cells_disjoint hs choice i j hij
    have hi := packedRectangleCorner_mem hs choice i s
    have hj := packedRectangleCorner_mem hs choice j t
    rw [← heq] at hj
    exact False.elim (Finset.disjoint_left.mp hd hi hj)

/-- Place an injectively selected subset of bridge blocks into an
injectively selected subset of the RP1 rectangles. Other bridge entries
remain in the pool and are not treated as rectangle blocks. -/
theorem install_selected_bridge_rectangles (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (k J L D : ℕ) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
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
      (∀ d, 0 < selectedBridgeGap batches (select d).2 (select d).1 ∧
        entry a' (RectanglePacking.firstRow hs (rectangle d),
            RectanglePacking.secondColumn hs choice (rectangle d)) =
          entry a' (RectanglePacking.firstRow hs (rectangle d),
            RectanglePacking.firstColumn hs choice (rectangle d)) +
              selectedBridgeGap batches (select d).2 (select d).1 ∧
        entry a' (RectanglePacking.secondRow hs (rectangle d),
            RectanglePacking.firstColumn hs choice (rectangle d)) =
          entry a' (RectanglePacking.secondRow hs (rectangle d),
            RectanglePacking.secondColumn hs choice (rectangle d)) +
              selectedBridgeGap batches (select d).2 (select d).1) := by
  let cells : Fin D × Fin 4 → Cell n := fun x =>
    packedRectangleCorner hs choice (rectangle x.1, x.2)
  let slots : Fin D × Fin 4 → (Fin J × Fin k) × Fin 4 := fun x => (select x.1, x.2)
  have hcells : Function.Injective cells := by
    rintro ⟨d, s⟩ ⟨e, t⟩ heq
    have heq' := packedRectangleCorner_injective hs choice heq
    have hde : d = e := hrectangle (congrArg Prod.fst heq')
    subst e
    have hst : s = t := congrArg Prod.snd heq'
    cases hst
    rfl
  have hslots : Function.Injective slots := by
    rintro ⟨d, s⟩ ⟨e, t⟩ heq
    have hde : d = e := hselect (congrArg Prod.fst heq)
    subst e
    have hst : s = t := congrArg Prod.snd heq
    cases hst
    rfl
  let values : (Fin D × Fin 4) → pool n := fun x =>
    ⟨bridgeStageEndpoint n initial radii batches k J hvalid (slots x),
      (bridgeStageEndpoint_pool_avoids bmor upper n initial radii batches k J hvalid
        hn hnmax hpositive (slots x)).1⟩
  have hvalues : Function.Injective values := by
    intro x y heq
    apply hslots
    apply bridgeStageEndpoint_injective n initial radii batches k J hvalid hpositive
    exact congrArg Subtype.val heq
  have hnew : ∀ x, cells x ∉ reservedCells := by
    rintro ⟨d, side⟩ hc
    exact Finset.disjoint_left.mp (hfree d) (packedRectangleCorner_mem hs choice (rectangle d) side) hc
  have hav : ∀ x c, c ∈ reservedCells → (values x).val ≠ entry a c := by
    intro x c hc heq
    have ha := (bridgeStageEndpoint_pool_avoids bmor upper n initial radii batches k J hvalid
      hn hnmax hpositive (slots x)).2
    apply ha
    change (values x).val ∈ initial
    rw [heq]
    exact hreserved c hc
  obtain ⟨a', hplace, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cells values reservedCells hcells hvalues hnew hav
  refine ⟨a', ?_, hfixed, ?_⟩
  · intro d side
    exact hplace (d, side)
  · intro d
    let j := (select d).1
    let i := (select d).2
    have hv := bridgeStageBlock_valid n initial radii batches k J hvalid j i
    rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
    have hgap := bridgeStageBlock_gap n initial radii batches k J hvalid j i
    refine ⟨by rw [hgap]; omega, ?_, ?_⟩
    · have ha := hplace (d, 1)
      have hb := hplace (d, 0)
      change entry a' (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) = _ at ha
      change entry a' (RectanglePacking.firstRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) = _ at hb
      rw [ha, hb, hgap]
      change (bridgeStageBlock n initial radii batches k J hvalid j i).high₁ =
        (bridgeStageBlock n initial radii batches k J hvalid j i).low₁ +
          ((bridgeStageBlock n initial radii batches k J hvalid j i).high₁ -
            (bridgeStageBlock n initial radii batches k J hvalid j i).low₁)
      omega
    · have ha := hplace (d, 2)
      have hb := hplace (d, 3)
      change entry a' (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.firstColumn hs choice (rectangle d)) = _ at ha
      change entry a' (RectanglePacking.secondRow hs (rectangle d),
          RectanglePacking.secondColumn hs choice (rectangle d)) = _ at hb
      rw [ha, hb, hgap]
      change (bridgeStageBlock n initial radii batches k J hvalid j i).high₂ =
        (bridgeStageBlock n initial radii batches k J hvalid j i).low₂ +
          ((bridgeStageBlock n initial radii batches k J hvalid j i).high₁ -
            (bridgeStageBlock n initial radii batches k J hvalid j i).low₁)
      omega

/-- A bridge block not assigned to one of the selected rectangles has no
endpoint in an old reserved cell or in any newly installed rectangle cell. -/
theorem unselected_bridge_endpoints_remain_available (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (radii : ℕ → ℝ) (batches : ℕ → List DoublePair)
    (k J L D : ℕ) (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18) (hpositive : ∀ j < J, 0 < radii j)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (select : Fin D → Fin J × Fin k) (rectangle : Fin D → Fin L)
    (a a' : Cell n ≃ Fin (n * n)) (reservedCells : Finset (Cell n))
    (hreserved : ∀ c ∈ reservedCells, entry a c ∈ initial)
    (hfixed : ∀ c ∈ reservedCells, entry a' c = entry a c)
    (hplace : ∀ d side, entry a' (packedRectangleCorner hs choice (rectangle d, side)) =
      bridgeStageEndpoint n initial radii batches k J hvalid (select d, side))
    (x : (Fin J × Fin k) × Fin 4) (hunselected : ∀ d, x.1 ≠ select d) :
    (∀ c ∈ reservedCells, bridgeStageEndpoint n initial radii batches k J hvalid x ≠ entry a' c) ∧
      (∀ d side, bridgeStageEndpoint n initial radii batches k J hvalid x ≠
        entry a' (packedRectangleCorner hs choice (rectangle d, side))) := by
  constructor
  · intro c hc heq
    have havoid := (bridgeStageEndpoint_pool_avoids bmor upper n initial radii batches k J hvalid
      hn hnmax hpositive x).2
    apply havoid
    rw [heq, hfixed c hc]
    exact hreserved c hc
  · intro d side heq
    have heq' := heq.trans (hplace d side)
    have hslots := bridgeStageEndpoint_injective n initial radii batches k J hvalid hpositive heq'
    exact hunselected d (congrArg Prod.fst hslots)

/-- Two installed bridge rectangles, one for each labelled diagonal,
perform the full physical trades while preserving rows, columns, the
central entry and all previously reserved cells. -/
theorem selected_bridge_main_then_anti {n k J L D : ℕ}
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
    (d e : Fin D) (hne : d ≠ e) (hmain : choice (rectangle d) = true)
    (hanti : choice (rectangle e) = false) (hn : 0 < n) (hodd : Odd n) :
    let result := rectangleTrade
      (rectangleTrade a (RectanglePacking.firstRow hs (rectangle d))
        (RectanglePacking.secondRow hs (rectangle d))
        (RectanglePacking.firstColumn hs choice (rectangle d))
        (RectanglePacking.secondColumn hs choice (rectangle d)))
      (RectanglePacking.firstRow hs (rectangle e)) (RectanglePacking.secondRow hs (rectangle e))
      (RectanglePacking.firstColumn hs choice (rectangle e))
      (RectanglePacking.secondColumn hs choice (rectangle e))
    (∀ r, rowSum result r = rowSum a r) ∧
    (∀ r, columnSum result r = columnSum a r) ∧
    (mainSum result : ℤ) = (mainSum a : ℤ) + selectedBridgeGap batches (select d).2 (select d).1 ∧
    (antiSum result : ℤ) = (antiSum a : ℤ) + selectedBridgeGap batches (select e).2 (select e).1 ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
    entry result (centerIndex n hn, centerIndex n hn) = entry a (centerIndex n hn, centerIndex n hn) ∧
    (∀ c ∈ reservedCells, entry result c = entry a c) ∧
    (∀ f, f ≠ d → f ≠ e → ∀ side,
      entry result (packedRectangleCorner hs choice (rectangle f, side)) =
        entry a (packedRectangleCorner hs choice (rectangle f, side))) := by
  have hindices : rectangle d ≠ rectangle e := fun h => hne (hrectangle h)
  have htrade := RectanglePacking.packed_main_then_anti hs hL choice (rectangle d) (rectangle e)
    hindices hmain hanti a (selectedBridgeGap batches (select d).2 (select d).1)
    (selectedBridgeGap batches (select e).2 (select e).1)
    (hgap d).1 (hgap d).2 (hgap e).1 (hgap e).2
  have hcenter := RectanglePacking.packed_main_then_anti_center hs hL choice (rectangle d)
    (rectangle e) hmain hanti a hn hodd
  refine ⟨htrade.1, htrade.2.1, htrade.2.2.1, htrade.2.2.2.1,
    htrade.2.2.2.2.1, htrade.2.2.2.2.2, hcenter, ?_, ?_⟩
  · intro c hc
    have hnotD : c ∉ rectangleCells (RectanglePacking.firstRow hs (rectangle d))
        (RectanglePacking.secondRow hs (rectangle d))
        (RectanglePacking.firstColumn hs choice (rectangle d))
        (RectanglePacking.secondColumn hs choice (rectangle d)) := by
      intro hm
      exact Finset.disjoint_left.mp (hfree d) hm hc
    have hnotE : c ∉ rectangleCells (RectanglePacking.firstRow hs (rectangle e))
        (RectanglePacking.secondRow hs (rectangle e))
        (RectanglePacking.firstColumn hs choice (rectangle e))
        (RectanglePacking.secondColumn hs choice (rectangle e)) := by
      intro hm
      exact Finset.disjoint_left.mp (hfree e) hm hc
    simp only [mem_rectangleCells, not_or] at hnotD hnotE
    have hfirst := rectangleTrade_outside a _ _ _ _ c hnotD.1 hnotD.2.1 hnotD.2.2.1 hnotD.2.2.2
    have hsecond := rectangleTrade_outside
      (rectangleTrade a (RectanglePacking.firstRow hs (rectangle d))
        (RectanglePacking.secondRow hs (rectangle d))
        (RectanglePacking.firstColumn hs choice (rectangle d))
        (RectanglePacking.secondColumn hs choice (rectangle d))) _ _ _ _ c
      hnotE.1 hnotE.2.1 hnotE.2.2.1 hnotE.2.2.2
    exact hsecond.trans hfirst
  · intro f hfd hfe side
    have hdf : rectangle d ≠ rectangle f := fun h => hfd (hrectangle h).symm
    have hef : rectangle e ≠ rectangle f := fun h => hfe (hrectangle h).symm
    have hdisjD := RectanglePacking.rectangle_cells_disjoint hs choice (rectangle d) (rectangle f) hdf
    have hdisjE := RectanglePacking.rectangle_cells_disjoint hs choice (rectangle e) (rectangle f) hef
    have hmem := packedRectangleCorner_mem hs choice (rectangle f) side
    have hfirst := rectangleTrade_other_cells_unchanged a
      (RectanglePacking.firstRow hs (rectangle d)) (RectanglePacking.secondRow hs (rectangle d))
      (RectanglePacking.firstColumn hs choice (rectangle d))
      (RectanglePacking.secondColumn hs choice (rectangle d))
      (RectanglePacking.firstRow hs (rectangle f)) (RectanglePacking.secondRow hs (rectangle f))
      (RectanglePacking.firstColumn hs choice (rectangle f))
      (RectanglePacking.secondColumn hs choice (rectangle f)) hdisjD _ hmem
    have hsecond := rectangleTrade_other_cells_unchanged
      (rectangleTrade a (RectanglePacking.firstRow hs (rectangle d))
        (RectanglePacking.secondRow hs (rectangle d))
        (RectanglePacking.firstColumn hs choice (rectangle d))
        (RectanglePacking.secondColumn hs choice (rectangle d)))
      (RectanglePacking.firstRow hs (rectangle e)) (RectanglePacking.secondRow hs (rectangle e))
      (RectanglePacking.firstColumn hs choice (rectangle e))
      (RectanglePacking.secondColumn hs choice (rectangle e))
      (RectanglePacking.firstRow hs (rectangle f)) (RectanglePacking.secondRow hs (rectangle f))
      (RectanglePacking.firstColumn hs choice (rectangle f))
      (RectanglePacking.secondColumn hs choice (rectangle f)) hdisjE _ hmem
    exact hsecond.trans hfirst

end
end Sude
