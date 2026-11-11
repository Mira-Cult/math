import Sude.FlowOutputCompletionSync
import Sude.FamilyGrid

/-! Carry an already-supplied family of bounded physical flow outputs to the
same completed square and synchronized reference. This does not construct the
input flow family, choose flows, or establish a prime target. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- For each row and column flow within the original exact box, retain the
original output and all its facts, together with a synchronized output for
the same completed square and the same supplied reference. The theta capacity
is obtained by taking `N = (n / 450) * poolMaximum n`. -/
theorem fw_completed_supplied_flows {n N : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (a b₀ c d : Cell n ≃ Fin (n*n)) (active full reserved : Finset (Cell n))
    (hactiveFull : active ⊆ full)
    (hcompleted : ∀ z ∈ full, entry c z = entry a z)
    (hreferenceOff : ∀ z ∉ active, entry b₀ z = entry a z)
    (hdActive : ∀ z ∈ active, entry d z = entry b₀ z)
    (hdOff : ∀ z ∉ active, entry d z = entry c z)
    (hflows : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b j : ℤ) - (columnSum b₀ j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ z ∈ reserved, entry b z = entry b₀ z) ∧
        (∀ z ∉ active, entry b z = entry a z) ∧
        active.image (entry b) = active.image (entry a) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b)) :
    ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b b' : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b j : ℤ) - (columnSum b₀ j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ z ∈ reserved, entry b z = entry b₀ z) ∧
        (∀ z ∉ active, entry b z = entry a z) ∧
        active.image (entry b) = active.image (entry a) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧
        (∀ z ∈ active, entry b' z = entry b z) ∧
        (∀ z ∉ active, entry b' z = entry c z) ∧
        (∀ r, (rowSum b' r : ℤ) - (rowSum d r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ j, (columnSum b' j : ℤ) - (columnSum d j : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun e => e.2) (fun e => p e.1 e.2) fc e j) ∧
        mainSum b' = mainSum d ∧ antiSum b' = antiSum d ∧
        (∀ z ∈ reserved, entry b' z = entry d z) ∧
        active.image (entry b') = active.image (entry c) ∧
        Set.range (entry b') = pool n ∧ Function.Injective (entry b') := by
  classical
  intro fr hfr fc hfc
  obtain ⟨b, hr, hc, hm, ha, hreserved, hoff, himage, hpool, hinj⟩ := hflows fr hfr fc hfc
  obtain ⟨b', hbActive, hbOff, hrow, hcol, hm', ha', hreserved', himage', hpool', hinj'⟩ :=
    flow_output_completion_sync a b₀ b c d active full reserved hactiveFull hcompleted
      hreferenceOff hoff himage hdActive hdOff hreserved hm ha
  have hac : active.image (entry a) = active.image (entry c) := by
    apply Finset.image_congr
    intro z hz
    exact (hcompleted z (hactiveFull hz)).symm
  refine ⟨b, b', hr, hc, hm, ha, hreserved, hoff, himage, hpool, hinj,
    hbActive, hbOff, ?_, ?_, hm', ha', hreserved', himage'.trans (himage.trans hac), hpool', hinj'⟩
  · intro r
    exact (hrow r).trans (hr r)
  · intro j
    exact (hcol j).trans (hc j)

end
end Sude
