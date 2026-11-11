import Sude.PackedTradeSequence

/-! Bounds for the diagonal gains of any subset of a supplied packed family.
The physical gap equations are hypotheses; no grid or target is constructed. -/
namespace Sude
noncomputable section

/-- Any subset of the installed rectangles increases each full diagonal by
exactly the sum of its own family's selected gaps. In particular, that gain
lies between zero and the sum of all available gaps in that family. This
applies to any reference subset, including the one selected by a separate
centered controller. -/
theorem packed_reference_gain_bounds {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (gap : Fin L → ℕ)
    (active before : Finset (Fin L)) (a : Cell n ≃ Fin (n*n))
    (hbefore : before ⊆ active)
    (hgaps : ∀ i ∈ active,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i) :
    let reference := packedTradeSequence hs choice a before.toList
    (mainSum reference : ℤ) - mainSum a =
      ((∑ i ∈ before.filter (fun i => choice i = true), gap i : ℕ) : ℤ) ∧
    (antiSum reference : ℤ) - antiSum a =
      ((∑ i ∈ before.filter (fun i => choice i = false), gap i : ℕ) : ℤ) ∧
    0 ≤ (mainSum reference : ℤ) - mainSum a ∧
    (mainSum reference : ℤ) - mainSum a ≤
      ((∑ i ∈ active.filter (fun i => choice i = true), gap i : ℕ) : ℤ) ∧
    0 ≤ (antiSum reference : ℤ) - antiSum a ∧
    (antiSum reference : ℤ) - antiSum a ≤
      ((∑ i ∈ active.filter (fun i => choice i = false), gap i : ℕ) : ℤ) := by
  classical
  dsimp only
  have heffect := packedTradeSequence_effect hs hL choice a gap before.toList before.nodup_toList
    (by intro i hi; exact hgaps i (hbefore (Finset.mem_toList.mp hi)))
  have hmain : packedMainGain choice gap before.toList =
      ((∑ i ∈ before.filter (fun i => choice i = true), gap i : ℕ) : ℤ) := by
    rw [packedMainGain, ← List.sum_toFinset (fun i : Fin L => if choice i then (gap i : ℤ) else 0) before.nodup_toList]
    simp only [Finset.toList_toFinset]
    push_cast
    rw [Finset.sum_filter]
  have hanti : packedAntiGain choice gap before.toList =
      ((∑ i ∈ before.filter (fun i => choice i = false), gap i : ℕ) : ℤ) := by
    rw [packedAntiGain, ← List.sum_toFinset (fun i : Fin L => if choice i then 0 else (gap i : ℤ)) before.nodup_toList]
    simp only [Finset.toList_toFinset]
    push_cast
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases hci : choice i <;> simp
  have hmbound : (∑ i ∈ before.filter (fun i => choice i = true), gap i : ℕ) ≤
      ∑ i ∈ active.filter (fun i => choice i = true), gap i := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.filter_subset_filter _ hbefore
  have habound : (∑ i ∈ before.filter (fun i => choice i = false), gap i : ℕ) ≤
      ∑ i ∈ active.filter (fun i => choice i = false), gap i := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.filter_subset_filter _ hbefore
  have hm := heffect.2.2.1
  have ha := heffect.2.2.2
  rw [hmain] at hm
  rw [hanti] at ha
  have hmbound' : (((∑ i ∈ before.filter (fun i => choice i = true), gap i : ℕ) : ℤ)) ≤
      ((∑ i ∈ active.filter (fun i => choice i = true), gap i : ℕ) : ℤ) := by exact_mod_cast hmbound
  have habound' : (((∑ i ∈ before.filter (fun i => choice i = false), gap i : ℕ) : ℤ)) ≤
      ((∑ i ∈ active.filter (fun i => choice i = false), gap i : ℕ) : ℤ) := by exact_mod_cast habound
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end
end Sude
