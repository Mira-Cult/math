import Sude.FamilyGrid

/-! The signed centering invoice is close to its half-radius reference.
This is only a radius identity: interpreting that reference as the sum of
physical pair midpoints requires proving that each radius is the actual total
gap of its block, plus the appropriate physical line decomposition. -/
namespace Sude
noncomputable section

/-- The rounding left after centering an even radius is nonnegative and at
most two. -/
theorem fw_radius_centering_remainder (R : ℕ) (heven : 2 ∣ R) :
    0 ≤ (R : ℤ) - 2 * evenGridCenter R ∧
    (R : ℤ) - 2 * evenGridCenter R ≤ 2 := by
  obtain ⟨hl, hu⟩ := evenGridCenter_midpoint_error R heven
  have hl' : (2 : ℤ) * evenGridCenter R ≤ R := by exact_mod_cast hl
  have hu' : (R : ℤ) ≤ 2 * evenGridCenter R + 2 := by
    have h : R ≤ 2 * evenGridCenter R + 2 := by omega
    exact_mod_cast h
  constructor <;> omega

/-- Each of three permutations supplies exactly one incoming and one outgoing
edge at a given vertex. -/
theorem fw_three_permutation_transfer {n : ℕ} (p : Fin 3 → Equiv.Perm (Fin n))
    (t : Fin 3 × Fin n → ℤ) (r : Fin n) :
    (∑ e : Fin 3 × Fin n,
      edgeTransfer Prod.snd (fun e => p e.1 e.2) t e r) =
      ∑ k : Fin 3, (t (k, r) - t (k, (p k).symm r)) := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simp [edgeTransfer, Finset.sum_sub_distrib, ← Equiv.eq_symm_apply]

/-- For even radii, centering on the actual graph changes a line sum to
within three of the half-radius reference. The initial and final line sums
must satisfy the same-witness signed invoice supplied by the caller. -/
theorem fw_three_permutation_centered_invoice {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n)) (R : Fin 3 × Fin n → ℕ)
    (initial centered : Fin n → ℤ)
    (heven : ∀ e, 2 ∣ R e)
    (hinvoice : ∀ r, centered r - initial r =
      ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => p e.1 e.2)
        (fun e => (evenGridCenter (R e) : ℤ)) e r) (r : Fin n) :
    |2 * centered r - (2 * initial r +
      ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => p e.1 e.2)
        (fun e => (R e : ℤ)) e r)| ≤ 6 := by
  classical
  let rem : Fin 3 × Fin n → ℤ := fun e => (R e : ℤ) - 2 * evenGridCenter (R e)
  have hrem : ∀ e, 0 ≤ rem e ∧ rem e ≤ 2 := by
    intro e
    exact fw_radius_centering_remainder (R e) (heven e)
  have hdiff : ∀ k : Fin 3, -2 ≤ rem (k,r) - rem (k,(p k).symm r) ∧
      rem (k,r) - rem (k,(p k).symm r) ≤ 2 := by
    intro k
    have h₁ := hrem (k,r)
    have h₂ := hrem (k,(p k).symm r)
    omega
  have hlo : (-6 : ℤ) ≤ ∑ k : Fin 3, (rem (k,r) - rem (k,(p k).symm r)) := by
    calc
      (-6 : ℤ) = ∑ _ : Fin 3, (-2 : ℤ) := by norm_num
      _ ≤ _ := Finset.sum_le_sum (fun k _ => (hdiff k).1)
  have hhi : (∑ k : Fin 3, (rem (k,r) - rem (k,(p k).symm r))) ≤ 6 := by
    calc
      _ ≤ ∑ _ : Fin 3, (2 : ℤ) := Finset.sum_le_sum (fun k _ => (hdiff k).2)
      _ = 6 := by norm_num
  have hi := hinvoice r
  rw [fw_three_permutation_transfer] at hi
  rw [fw_three_permutation_transfer]
  rw [abs_le]
  simp only [rem, Finset.sum_sub_distrib, ← Finset.mul_sum] at hlo hhi
  simp only [Finset.sum_sub_distrib] at hi ⊢
  constructor <;> omega

end
end Sude
