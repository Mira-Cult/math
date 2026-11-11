import Sude.PackedTradeSequence

/-! Agreement on a labelled packed-rectangle support survives trades within
that support. This does not assert that an intervening construction agrees
on the support or that any diagonal target is attainable. -/
namespace Sude
noncomputable section

/-- The actual cells belonging to a supplied set of packed rectangles. -/
def packedLabelSupport {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (S : Finset (Fin L)) : Finset (Cell n) :=
  S.biUnion (fun i => rectangleCells (RectanglePacking.firstRow hs i)
    (RectanglePacking.secondRow hs i) (RectanglePacking.firstColumn hs choice i)
    (RectanglePacking.secondColumn hs choice i))

private theorem swap_mem_of_endpoints {α : Type*} [DecidableEq α]
    (S : Finset α) {x y z : α} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) :
    Equiv.swap x y z ∈ S := by
  by_cases hzx : z = x
  · subst z
    simpa using hy
  · by_cases hzy : z = y
    · subst z
      simpa using hx
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
      exact hz

/-- A labelled trade preserves agreement on the entire labelled support. -/
theorem packedTrade_preserves_support_agreement {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (S : Finset (Fin L)) (i : Fin L) (hi : i ∈ S)
    (a b : Cell n ≃ Fin (n*n))
    (h : ∀ z ∈ packedLabelSupport hs choice S, entry a z = entry b z) :
    ∀ z ∈ packedLabelSupport hs choice S,
      entry (packedTrade hs choice a i) z = entry (packedTrade hs choice b i) z := by
  classical
  let r := RectanglePacking.firstRow hs i
  let r' := RectanglePacking.secondRow hs i
  let c := RectanglePacking.firstColumn hs choice i
  let c' := RectanglePacking.secondColumn hs choice i
  have hx : (r,c) ∈ packedLabelSupport hs choice S := by
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [r, r', c, c']⟩
  have hy : (r,c') ∈ packedLabelSupport hs choice S := by
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [r, r', c, c']⟩
  have hu : (r',c) ∈ packedLabelSupport hs choice S := by
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [r, r', c, c']⟩
  have hv : (r',c') ∈ packedLabelSupport hs choice S := by
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [r, r', c, c']⟩
  intro z hz
  have hz' := swap_mem_of_endpoints (packedLabelSupport hs choice S) hu hv hz
  have hz'' := swap_mem_of_endpoints (packedLabelSupport hs choice S) hx hy hz'
  have he := h _ hz''
  simpa only [packedTrade, rectangleTrade, entry_swapPlacement, r, r', c, c'] using he

/-- Any list of trades drawn from a labelled support preserves agreement there,
including when the list contains repeated labels. -/
theorem packedTradeSequence_preserves_support_agreement {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (S : Finset (Fin L)) (labels : List (Fin L)) (hlabels : ∀ i ∈ labels, i ∈ S)
    (a b : Cell n ≃ Fin (n*n))
    (h : ∀ z ∈ packedLabelSupport hs choice S, entry a z = entry b z) :
    ∀ z ∈ packedLabelSupport hs choice S,
      entry (packedTradeSequence hs choice a labels) z =
        entry (packedTradeSequence hs choice b labels) z := by
  induction labels generalizing a b with
  | nil => simpa [packedTradeSequence] using h
  | cons i rest ih =>
    have hi : i ∈ S := hlabels i (by simp)
    have hrest : ∀ j ∈ rest, j ∈ S := by
      intro j hj
      exact hlabels j (by simp [hj])
    have h' := packedTrade_preserves_support_agreement hs choice S i hi a b h
    exact ih hrest _ _ h'

end
end Sude
