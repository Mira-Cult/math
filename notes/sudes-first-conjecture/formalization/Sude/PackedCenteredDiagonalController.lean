import Sude.RectangleCenteredChoices
import Sude.PackedOrientationDifference
import Sude.PackedTradeRollback
import Sude.PackedTradeSupportAgreement

/-! A centered physical two-diagonal rectangle controller, including an
intervening placement that preserves the rectangle cells. All grids, gap
invoices and support-preservation premises are explicit. -/
namespace Sude
noncomputable section

/-- Center the two supplied rectangle families once. A later exact-pool
placement agreeing with that centered square on every active rectangle can be
reoriented to realize independently supplied even signed diagonal differences,
without changing that later placement's rows, columns or protected cells.
No prime targets or completeness of the physical grids are constructed here. -/
theorem packed_centered_diagonal_controller_with_reference_gains {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : 0 < n)
    (choice : Fin L → Bool) (gap : Fin L → ℕ) (active : Finset (Fin L))
    (Rm Ra : ℕ) (a : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (hm : CompleteEvenGrid (active.filter fun i => choice i = true) gap Rm)
    (ha : CompleteEvenGrid (active.filter fun i => choice i = false) gap Ra)
    (hgaps : ∀ i ∈ active,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i)
    (hprotect : ∀ c ∈ reserved, ∀ i ∈ active,
      c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i)) :
    ∃ before : Finset (Fin L), before ⊆ active ∧
      let reference := packedTradeSequence hs choice a before.toList
      (∀ r, rowSum reference r = rowSum a r) ∧
      (∀ c, columnSum reference c = columnSum a c) ∧
      (mainSum reference : ℤ) - (mainSum a : ℤ) = evenGridCenter Rm ∧
      (antiSum reference : ℤ) - (antiSum a : ℤ) = evenGridCenter Ra ∧
      (∀ b : Cell n ≃ Fin (n*n),
        (∀ z ∈ packedLabelSupport hs choice active, entry b z = entry reference z) →
        ∀ tm ta : ℤ, (2 : ℤ) ∣ tm → (2 : ℤ) ∣ ta →
          -(evenGridCenter Rm : ℤ) ≤ tm → tm ≤ evenGridCenter Rm →
          -(evenGridCenter Ra : ℤ) ≤ ta → ta ≤ evenGridCenter Ra →
          ∃ result : Cell n ≃ Fin (n*n),
            (∀ r, rowSum result r = rowSum b r) ∧
            (∀ c, columnSum result c = columnSum b c) ∧
            (mainSum result : ℤ) - (mainSum b : ℤ) = tm ∧
            (antiSum result : ℤ) - (antiSum b : ℤ) = ta ∧
            Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
            entry result (centerIndex n hn, centerIndex n hn) =
              entry b (centerIndex n hn, centerIndex n hn) ∧
            (∀ c ∈ reserved, entry result c = entry b c)) := by
  classical
  obtain ⟨before, hbefore, hcenterMain, hcenterAnti, hchoose⟩ := rectangle_centered_choices active choice gap Rm Ra hm ha
  have hbeforeList : ∀ i ∈ before.toList, i ∈ active := by
    intro i hi
    exact hbefore (Finset.mem_toList.mp hi)
  have hbeforeEffect := packedTradeSequence_effect hs hL choice a gap before.toList before.nodup_toList
    (by intro i hi; exact hgaps i (hbeforeList i hi))
  have hmainGain : packedMainGain choice gap before.toList = evenGridCenter Rm := by
    have hinter : before ∩ (active.filter fun i => choice i = true) =
        before.filter (fun i => choice i = true) := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨hi, _, hp⟩; exact ⟨hi, hp⟩
      · rintro ⟨hi, hp⟩; exact ⟨hi, hbefore hi, hp⟩
    rw [hinter] at hcenterMain
    push_cast at hcenterMain
    rw [Finset.sum_filter] at hcenterMain
    have hsum : packedMainGain choice gap before.toList =
        ∑ i ∈ before, if choice i then (gap i : ℤ) else 0 := by
      simpa [packedMainGain] using
        (List.sum_toFinset (fun i : Fin L => if choice i then (gap i : ℤ) else 0) before.nodup_toList).symm
    exact hsum.trans hcenterMain
  have hantiGain : packedAntiGain choice gap before.toList = evenGridCenter Ra := by
    have hinter : before ∩ (active.filter fun i => choice i = false) =
        before.filter (fun i => choice i = false) := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨hi, _, hp⟩; exact ⟨hi, hp⟩
      · rintro ⟨hi, hp⟩; exact ⟨hi, hbefore hi, hp⟩
    rw [hinter] at hcenterAnti
    push_cast at hcenterAnti
    rw [Finset.sum_filter] at hcenterAnti
    have hsum : (∑ i ∈ before, if choice i = false then (gap i : ℤ) else 0) =
        ∑ i ∈ before, if choice i then 0 else (gap i : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      cases hci : choice i <;> simp [hci]
    rw [hsum] at hcenterAnti
    have hsum' : packedAntiGain choice gap before.toList =
        ∑ i ∈ before, if choice i then 0 else (gap i : ℤ) := by
      simpa [packedAntiGain] using
        (List.sum_toFinset (fun i : Fin L => if choice i then 0 else (gap i : ℤ)) before.nodup_toList).symm
    exact hsum'.trans hcenterAnti
  refine ⟨before, hbefore, hbeforeEffect.1, hbeforeEffect.2.1, ?_, ?_, ?_⟩
  · rw [hmainGain] at hbeforeEffect
    linarith [hbeforeEffect.2.2.1]
  · rw [hantiGain] at hbeforeEffect
    linarith [hbeforeEffect.2.2.2]
  intro b hagree tm ta htm hta hml hmu hal hau
  obtain ⟨after, hafter, hmain, hanti⟩ := hchoose tm ta htm hta hml hmu hal hau
  let reference := packedTradeSequence hs choice a before.toList
  let undo := packedTradeSequence hs choice b before.toList.reverse
  have hlabels : ∀ i ∈ before.toList.reverse, i ∈ active := by
    intro i hi
    exact hbeforeList i (List.mem_reverse.mp hi)
  have hundo : ∀ z ∈ packedLabelSupport hs choice active, entry undo z = entry a z := by
    have h := packedTradeSequence_preserves_support_agreement hs choice active before.toList.reverse
      hlabels b reference hagree
    simpa only [undo, reference, packedTradeSequence_reverse] using h
  have hgapUndo : ∀ i ∈ active,
      entry undo (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry undo (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry undo (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry undo (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i := by
    intro i hi
    have h1 := hundo (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp [packedLabelSupport]⟩)
    have h2 := hundo (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp [packedLabelSupport]⟩)
    have h3 := hundo (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp [packedLabelSupport]⟩)
    have h4 := hundo (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp [packedLabelSupport]⟩)
    rw [h1, h2, h3, h4]
    exact hgaps i hi
  have hrestore : packedTradeSequence hs choice undo before.toList = b := by
    simpa only [undo, List.reverse_reverse] using
      (packedTradeSequence_reverse hs choice b before.toList.reverse)
  have hdiff := packed_orientation_difference hs hL hn choice gap undo active before after reserved
    hbefore hafter hgapUndo hprotect
  dsimp only at hdiff
  rw [hrestore] at hdiff
  have hsumMain (T : Finset (Fin L)) (hT : T ⊆ active) :
      (∑ i ∈ T, if choice i then (gap i : ℤ) else 0) =
        ((∑ i ∈ T ∩ (active.filter fun i => choice i = true), gap i : ℕ) : ℤ) := by
    have hinter : T ∩ (active.filter fun i => choice i = true) =
        T.filter (fun i => choice i = true) := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨hi, _, hp⟩; exact ⟨hi, hp⟩
      · rintro ⟨hi, hp⟩; exact ⟨hi, hT hi, hp⟩
    rw [hinter]
    push_cast
    rw [Finset.sum_filter]
  have hsumAnti (T : Finset (Fin L)) (hT : T ⊆ active) :
      (∑ i ∈ T, if choice i then 0 else (gap i : ℤ)) =
        ((∑ i ∈ T ∩ (active.filter fun i => choice i = false), gap i : ℕ) : ℤ) := by
    have hinter : T ∩ (active.filter fun i => choice i = false) =
        T.filter (fun i => choice i = false) := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_filter]
      constructor
      · rintro ⟨hi, _, hp⟩; exact ⟨hi, hp⟩
      · rintro ⟨hi, hp⟩; exact ⟨hi, hT hi, hp⟩
    rw [hinter]
    push_cast
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases hci : choice i <;> simp [hci]
  refine ⟨packedTradeSequence hs choice undo after.toList, hdiff.1, hdiff.2.1, ?_, ?_,
    hdiff.2.2.2.2.1, hdiff.2.2.2.2.2.1, hdiff.2.2.2.2.2.2.1,
    hdiff.2.2.2.2.2.2.2⟩
  · have hh := hdiff.2.2.1
    rw [hsumMain after hafter, hsumMain before hbefore] at hh
    exact hh.trans hmain
  · have hh := hdiff.2.2.2.1
    rw [hsumAnti after hafter, hsumAnti before hbefore] at hh
    exact hh.trans hanti

/-- Backward-compatible controller interface; the strengthened theorem also
exposes both centered reference gains. -/
theorem packed_centered_diagonal_controller {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : 0 < n)
    (choice : Fin L → Bool) (gap : Fin L → ℕ) (active : Finset (Fin L))
    (Rm Ra : ℕ) (a : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (hm : CompleteEvenGrid (active.filter fun i => choice i = true) gap Rm)
    (ha : CompleteEvenGrid (active.filter fun i => choice i = false) gap Ra)
    (hgaps : ∀ i ∈ active,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i)
    (hprotect : ∀ c ∈ reserved, ∀ i ∈ active,
      c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i)) :
    ∃ before : Finset (Fin L), before ⊆ active ∧
      let reference := packedTradeSequence hs choice a before.toList
      (∀ r, rowSum reference r = rowSum a r) ∧
      (∀ c, columnSum reference c = columnSum a c) ∧
      (∀ b : Cell n ≃ Fin (n*n),
        (∀ z ∈ packedLabelSupport hs choice active, entry b z = entry reference z) →
        ∀ tm ta : ℤ, (2 : ℤ) ∣ tm → (2 : ℤ) ∣ ta →
          -(evenGridCenter Rm : ℤ) ≤ tm → tm ≤ evenGridCenter Rm →
          -(evenGridCenter Ra : ℤ) ≤ ta → ta ≤ evenGridCenter Ra →
          ∃ result : Cell n ≃ Fin (n*n),
            (∀ r, rowSum result r = rowSum b r) ∧
            (∀ c, columnSum result c = columnSum b c) ∧
            (mainSum result : ℤ) - (mainSum b : ℤ) = tm ∧
            (antiSum result : ℤ) - (antiSum b : ℤ) = ta ∧
            Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
            entry result (centerIndex n hn, centerIndex n hn) =
              entry b (centerIndex n hn, centerIndex n hn) ∧
            (∀ c ∈ reserved, entry result c = entry b c)) := by
  obtain ⟨before, hbefore, hrows, hcols, _, _, hcontroller⟩ :=
    packed_centered_diagonal_controller_with_reference_gains hs hL hn choice gap active Rm Ra a reserved
      hm ha hgaps hprotect
  exact ⟨before, hbefore, hrows, hcols, hcontroller⟩

end
end Sude
