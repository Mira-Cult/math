import Sude.PackedTradeSequence

/-! Compare two sets of disjoint packed rectangle trades, with their actual
stage-dependent gaps. This uses one underlying square; it does not yet carry
an orientation choice through later changes outside the rectangles. -/
namespace Sude
noncomputable section

/-- Two subsets of the same installed rectangle family preserve all rows,
columns, protected cells and the exact pool. Their diagonal difference is the
signed difference of the actual selected gap sums. -/
theorem packed_orientation_difference {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : 0 < n)
    (choice : Fin L → Bool) (gap : Fin L → ℕ)
    (a : Cell n ≃ Fin (n*n)) (active before after : Finset (Fin L))
    (reservedCells : Finset (Cell n))
    (hbefore : before ⊆ active) (hafter : after ⊆ active)
    (hgaps : ∀ i ∈ active,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i)
    (hprotect : ∀ c ∈ reservedCells, ∀ i ∈ active,
      c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i)) :
    let base := packedTradeSequence hs choice a before.toList
    let result := packedTradeSequence hs choice a after.toList
    (∀ r, rowSum result r = rowSum base r) ∧
    (∀ c, columnSum result c = columnSum base c) ∧
    (mainSum result : ℤ) - (mainSum base : ℤ) =
      (∑ i ∈ after, if choice i then (gap i : ℤ) else 0) -
      (∑ i ∈ before, if choice i then (gap i : ℤ) else 0) ∧
    (antiSum result : ℤ) - (antiSum base : ℤ) =
      (∑ i ∈ after, if choice i then 0 else (gap i : ℤ)) -
      (∑ i ∈ before, if choice i then 0 else (gap i : ℤ)) ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
    entry result (centerIndex n hn, centerIndex n hn) =
      entry base (centerIndex n hn, centerIndex n hn) ∧
    (∀ c ∈ reservedCells, entry result c = entry base c) := by
  classical
  dsimp only
  have hb := packedTradeSequence_effect hs hL choice a gap before.toList before.nodup_toList
    (by intro i hi; exact hgaps i (hbefore (Finset.mem_toList.mp hi)))
  have ha := packedTradeSequence_effect hs hL choice a gap after.toList after.nodup_toList
    (by intro i hi; exact hgaps i (hafter (Finset.mem_toList.mp hi)))
  have hmain (S : Finset (Fin L)) : packedMainGain choice gap S.toList =
      ∑ i ∈ S, if choice i then (gap i : ℤ) else 0 := by
    simpa [packedMainGain] using
      (List.sum_toFinset (fun i : Fin L => if choice i then (gap i : ℤ) else 0) S.nodup_toList).symm
  have hanti (S : Finset (Fin L)) : packedAntiGain choice gap S.toList =
      ∑ i ∈ S, if choice i then 0 else (gap i : ℤ) := by
    simpa [packedAntiGain] using
      (List.sum_toFinset (fun i : Fin L => if choice i then 0 else (gap i : ℤ)) S.nodup_toList).symm
  rw [hmain] at hb ha
  rw [hanti] at hb ha
  refine ⟨?_, ?_, ?_, ?_, entry_range _, entry_injective _, ?_, ?_⟩
  · intro r
    exact (ha.1 r).trans (hb.1 r).symm
  · intro c
    exact (ha.2.1 c).trans (hb.2.1 c).symm
  · linarith [ha.2.2.1, hb.2.2.1]
  · linarith [ha.2.2.2, hb.2.2.2]
  · have hbfix := packedTradeSequence_fixes_outside hs choice a before.toList
      (centerIndex n hn, centerIndex n hn) (by
        intro i _; exact RectanglePacking.rectangle_avoids_center hs hn choice i)
    have hafix := packedTradeSequence_fixes_outside hs choice a after.toList
      (centerIndex n hn, centerIndex n hn) (by
        intro i _; exact RectanglePacking.rectangle_avoids_center hs hn choice i)
    exact hafix.trans hbfix.symm
  · intro c hc
    have hbfix := packedTradeSequence_fixes_outside hs choice a before.toList c (by
      intro i hi; exact hprotect c hc i (hbefore (Finset.mem_toList.mp hi)))
    have hafix := packedTradeSequence_fixes_outside hs choice a after.toList c (by
      intro i hi; exact hprotect c hc i (hafter (Finset.mem_toList.mp hi)))
    exact hafix.trans hbfix.symm

end
end Sude
