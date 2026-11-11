import Sude.PackedCenteredDiagonalController

/-! Adapt the centered controller to an intervening placement before centering.
Support and initial diagonal-sum agreement remain explicit assumptions. -/
namespace Sude
noncomputable section

/-- Center an intervening placement with the same trades; when it agrees on
support and diagonal sums, its reference diagonals agree as well. -/
theorem packed_centered_diagonal_adapter_with_reference_gains {L n : ℕ}
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
      (mainSum reference : ℤ) - (mainSum a : ℤ) = evenGridCenter Rm ∧
      (antiSum reference : ℤ) - (antiSum a : ℤ) = evenGridCenter Ra ∧
      (∀ b : Cell n ≃ Fin (n*n),
        (∀ z ∈ packedLabelSupport hs choice active, entry b z = entry a z) →
        mainSum b = mainSum a → antiSum b = antiSum a →
        ∀ tm ta : ℤ, (2 : ℤ) ∣ tm → (2 : ℤ) ∣ ta →
          -(evenGridCenter Rm : ℤ) ≤ tm → tm ≤ evenGridCenter Rm →
          -(evenGridCenter Ra : ℤ) ≤ ta → ta ≤ evenGridCenter Ra →
          ∃ result : Cell n ≃ Fin (n*n),
            (∀ r, rowSum result r = rowSum b r) ∧
            (∀ c, columnSum result c = columnSum b c) ∧
            (mainSum result : ℤ) - (mainSum reference : ℤ) = tm ∧
            (antiSum result : ℤ) - (antiSum reference : ℤ) = ta ∧
            Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
            entry result (centerIndex n hn, centerIndex n hn) =
              entry b (centerIndex n hn, centerIndex n hn) ∧
            (∀ c ∈ reserved, entry result c = entry b c)) := by
  classical
  obtain ⟨before, hbefore, _, _, hmainGain, hantiGain, hcontroller⟩ :=
    packed_centered_diagonal_controller_with_reference_gains hs hL hn choice gap active Rm Ra a reserved hm ha hgaps hprotect
  refine ⟨before, hbefore, hmainGain, hantiGain, ?_⟩
  intro b hagree hmain hanti tm ta htm hta hml hmu hal hau
  let reference := packedTradeSequence hs choice a before.toList
  let centered := packedTradeSequence hs choice b before.toList
  have hlabels : ∀ i ∈ before.toList, i ∈ active := by
    intro i hi
    exact hbefore (Finset.mem_toList.mp hi)
  have hcenterAgree : ∀ z ∈ packedLabelSupport hs choice active,
      entry centered z = entry reference z :=
    packedTradeSequence_preserves_support_agreement hs choice active before.toList hlabels b a hagree
  have hgapB : ∀ i ∈ before.toList,
      entry b (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry b (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry b (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry b (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i := by
    intro i hi
    have hi' := hlabels i hi
    have h1 := hagree (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi', by simp [packedLabelSupport]⟩)
    have h2 := hagree (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi', by simp [packedLabelSupport]⟩)
    have h3 := hagree (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi', by simp [packedLabelSupport]⟩)
    have h4 := hagree (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi', by simp [packedLabelSupport]⟩)
    rw [h1, h2, h3, h4]
    exact hgaps i hi'
  have hb := packedTradeSequence_effect hs hL choice b gap before.toList before.nodup_toList hgapB
  have ha' := packedTradeSequence_effect hs hL choice a gap before.toList before.nodup_toList
    (by intro i hi; exact hgaps i (hlabels i hi))
  have hmref : (mainSum centered : ℤ) = mainSum reference := by
    dsimp only [centered, reference]
    have hb' := hb.2.2.1
    have ha'' := ha'.2.2.1
    exact_mod_cast (by linarith : (mainSum (packedTradeSequence hs choice b before.toList) : ℤ) =
      mainSum (packedTradeSequence hs choice a before.toList))
  have haref : (antiSum centered : ℤ) = antiSum reference := by
    dsimp only [centered, reference]
    have hb' := hb.2.2.2
    have ha'' := ha'.2.2.2
    exact_mod_cast (by linarith : (antiSum (packedTradeSequence hs choice b before.toList) : ℤ) =
      antiSum (packedTradeSequence hs choice a before.toList))
  obtain ⟨result, hrows, hcols, hmd, had, hpool, hinj, hc, hp⟩ :=
    hcontroller centered hcenterAgree tm ta htm hta hml hmu hal hau
  refine ⟨result, ?_, ?_, ?_, ?_, hpool, hinj, ?_, ?_⟩
  · intro r
    exact (hrows r).trans (hb.1 r)
  · intro c
    exact (hcols c).trans (hb.2.1 c)
  · linarith
  · linarith
  · apply hc.trans
    exact packedTradeSequence_fixes_outside hs choice b before.toList _ (by
      intro i _; exact RectanglePacking.rectangle_avoids_center hs hn choice i)
  · intro c hc'
    apply (hp c hc').trans
    exact packedTradeSequence_fixes_outside hs choice b before.toList c (by
      intro i hi; exact hprotect c hc' i (hlabels i hi))

/-- Backward-compatible adapter interface; the strengthened theorem also
exposes both centered reference gains. -/
theorem packed_centered_diagonal_adapter {L n : ℕ}
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
      (∀ b : Cell n ≃ Fin (n*n),
        (∀ z ∈ packedLabelSupport hs choice active, entry b z = entry a z) →
        mainSum b = mainSum a → antiSum b = antiSum a →
        ∀ tm ta : ℤ, (2 : ℤ) ∣ tm → (2 : ℤ) ∣ ta →
          -(evenGridCenter Rm : ℤ) ≤ tm → tm ≤ evenGridCenter Rm →
          -(evenGridCenter Ra : ℤ) ≤ ta → ta ≤ evenGridCenter Ra →
          ∃ result : Cell n ≃ Fin (n*n),
            (∀ r, rowSum result r = rowSum b r) ∧
            (∀ c, columnSum result c = columnSum b c) ∧
            (mainSum result : ℤ) - (mainSum reference : ℤ) = tm ∧
            (antiSum result : ℤ) - (antiSum reference : ℤ) = ta ∧
            Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
            entry result (centerIndex n hn, centerIndex n hn) =
              entry b (centerIndex n hn, centerIndex n hn) ∧
            (∀ c ∈ reserved, entry result c = entry b c)) := by
  obtain ⟨before, hbefore, _, _, hcontroller⟩ :=
    packed_centered_diagonal_adapter_with_reference_gains hs hL hn choice gap active Rm Ra a reserved
      hm ha hgaps hprotect
  exact ⟨before, hbefore, hcontroller⟩

end
end Sude
