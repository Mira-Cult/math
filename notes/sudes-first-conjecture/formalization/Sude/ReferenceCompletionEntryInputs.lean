import Sude.PhysicalNetworkCompletionTransport

/-! Translate physical entry equality and value-image facts to the index
interfaces required by reference completion transport. -/
namespace Sude
noncomputable section

/-- Equality of prescribed entries at one cell is equality of their indices. -/
theorem entry_eq_implies_index_eq {n : ℕ} (a b : Cell n ≃ Fin (n*n)) (x : Cell n)
    (h : entry a x = entry b x) : a x = b x := by
  apply Fin.ext
  exact oddPrime_injective h

/-- Equal active entry-value images give equal images of the prime indices. -/
theorem entry_image_eq_implies_index_image_eq {n : ℕ} (a b : Cell n ≃ Fin (n*n))
    (active : Finset (Cell n)) (h : active.image (entry a) = active.image (entry b)) :
    active.image a = active.image b := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have h' : entry a x ∈ active.image (entry b) := h ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h'
    apply Finset.mem_image.mpr
    exact ⟨y, hy, Fin.ext (oddPrime_injective he)⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have h' : entry b x ∈ active.image (entry a) := h.symm ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp h'
    apply Finset.mem_image.mpr
    exact ⟨y, hy, Fin.ext (oddPrime_injective he)⟩

/-- Diagonal sum equalities transfer to the synchronized reference. The
original diagonal equality remains an explicit premise. -/
theorem reference_completion_diagonal_sums {n : ℕ}
    (a b c d : Cell n ≃ Fin (n*n)) (active : Finset (Cell n))
    (hactive : ∀ x ∈ active, entry c x = entry a x)
    (href : ∀ x ∈ active, entry d x = entry b x)
    (hoff : ∀ x ∉ active, entry b x = entry a x)
    (hcomplete : ∀ x ∉ active, entry d x = entry c x) :
    (mainSum b = mainSum a → mainSum d = mainSum c) ∧
    (antiSum b = antiSum a → antiSum d = antiSum c) := by
  have hdiff (x : Cell n) : (entry d x : ℤ) - entry c x =
      (entry b x : ℤ) - entry a x := by
    by_cases h : x ∈ active
    · rw [href x h, hactive x h]
    · rw [hcomplete x h, hoff x h]
      simp
  have hm : (∑ i : Fin n, ((entry d (i,i) : ℤ) - entry c (i,i))) =
      ∑ i : Fin n, ((entry b (i,i) : ℤ) - entry a (i,i)) := by
    exact Finset.sum_congr rfl (fun i _ => hdiff (i,i))
  have ha : (∑ i : Fin n, ((entry d (i,i.rev) : ℤ) - entry c (i,i.rev))) =
      ∑ i : Fin n, ((entry b (i,i.rev) : ℤ) - entry a (i,i.rev)) := by
    exact Finset.sum_congr rfl (fun i _ => hdiff (i,i.rev))
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum] at hm ha
  change (mainSum d : ℤ) - (mainSum c : ℤ) = (mainSum b : ℤ) - (mainSum a : ℤ) at hm
  change (antiSum d : ℤ) - (antiSum c : ℤ) = (antiSum b : ℤ) - (antiSum a : ℤ) at ha
  constructor
  · intro h
    have hc : (mainSum b : ℤ) = mainSum a := by exact_mod_cast h
    have hd : (mainSum d : ℤ) = mainSum c := by omega
    exact_mod_cast hd
  · intro h
    have hc : (antiSum b : ℤ) = antiSum a := by exact_mod_cast h
    have hd : (antiSum d : ℤ) = antiSum c := by omega
    exact_mod_cast hd

/-- Physical entry hypotheses construct one reference for both the row and
column network invoice transfers. Their actual endpoint sets must be contained
in the same active set. No flow or numerical bound is asserted. -/
theorem physical_reference_completion_both_invoices {n : ℕ} {ER EC KR KC : Type*}
    [Fintype ER] [DecidableEq ER] [DecidableEq KR]
    [Fintype EC] [DecidableEq EC] [DecidableEq KC]
    (a b c : Cell n ≃ Fin (n*n)) (active : Finset (Cell n))
    (vr : RowNetworkPairs KR a) (br : CenteredNetwork ER KR vr)
    (vc : RowNetworkPairs KC (LayerPacking.transposePlacement a)) (bc : CenteredNetwork EC KC vc)
    (hactive : ∀ x ∈ active, entry c x = entry a x)
    (hoff : ∀ x ∉ active, entry b x = entry a x)
    (himage : active.image (entry b) = active.image (entry a))
    (hrowSlots : ∀ k side, rowNetworkSlot vr (k,side) ∈ active)
    (hcolSlots : ∀ k side, (rowNetworkSlot vc (k,side)).swap ∈ active) :
    ∃ d : Cell n ≃ Fin (n*n),
      (∀ x ∈ active, entry d x = entry b x) ∧ (∀ x ∉ active, entry d x = entry c x) ∧
      ∃ hr : ∀ k side, entry c (rowNetworkSlot vr (k,side)) = entry a (rowNetworkSlot vr (k,side)),
      ∃ hc : ∀ k side, entry (LayerPacking.transposePlacement c) (rowNetworkSlot vc (k,side)) =
          entry (LayerPacking.transposePlacement a) (rowNetworkSlot vc (k,side)),
        (∀ r, 2 * (rowSum d r : ℤ) -
            physicalNetworkMidpointTwice (rowNetworkPairsRebase vr c hr)
              (centeredNetworkRebase vr br c hr) r =
          2 * (rowSum b r : ℤ) - physicalNetworkMidpointTwice vr br r) ∧
        (∀ j, 2 * (columnSum d j : ℤ) -
            physicalNetworkMidpointTwice (rowNetworkPairsRebase vc (LayerPacking.transposePlacement c) hc)
              (centeredNetworkRebase vc bc (LayerPacking.transposePlacement c) hc) j =
          2 * (columnSum b j : ℤ) - physicalNetworkMidpointTwice vc bc j) := by
  classical
  have hactive' : ∀ x ∈ active, c x = a x := fun x hx => entry_eq_implies_index_eq c a x (hactive x hx)
  have hoff' : ∀ x ∉ active, b x = a x := fun x hx => entry_eq_implies_index_eq b a x (hoff x hx)
  have himage' := entry_image_eq_implies_index_image_eq b a active himage
  obtain ⟨d, hd, hdo, hr, hrows⟩ := physical_network_reference_completion_invoice a b c active vr br
    hactive' hoff' himage' hrowSlots
  obtain ⟨hc, hcols⟩ := physical_network_reference_completion_column_invoice a b c d active vc bc
    hactive' hd hoff' hdo hcolSlots
  refine ⟨d, ?_, ?_, hr, hc, hrows, hcols⟩
  · intro x hx
    unfold entry
    rw [hd x hx]
  · intro x hx
    unfold entry
    rw [hdo x hx]

end
end Sude
