import Sude.FWRadiusCentering

/-! Radius centering without assuming the chosen grid radius is even. The
reference is algebraic; identification with physical pair midpoints is a
separate obligation. -/
namespace Sude
noncomputable section

theorem fw_radius_centering_remainder_any (R : ℕ) :
    0 ≤ (R : ℤ) - 2 * evenGridCenter R ∧
    (R : ℤ) - 2 * evenGridCenter R ≤ 3 := by
  have h : R ≤ 2 * evenGridCenter R + 3 := by
    dsimp [evenGridCenter]
    omega
  have hl := evenGridCenter_twice_le R
  have hl' : (2 : ℤ) * evenGridCenter R ≤ R := by exact_mod_cast hl
  have hu' : (R : ℤ) ≤ 2 * evenGridCenter R + 3 := by exact_mod_cast h
  constructor <;> omega

/-- Three permutation layers and the supplied same-witness invoice give
an absolute doubled error at most nine without any parity hypothesis. -/
theorem fw_three_permutation_centered_invoice_any {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n)) (R : Fin 3 × Fin n → ℕ)
    (initial centered : Fin n → ℤ)
    (hinvoice : ∀ r, centered r - initial r =
      ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => p e.1 e.2)
        (fun e => (evenGridCenter (R e) : ℤ)) e r) (r : Fin n) :
    |2 * centered r - (2 * initial r +
      ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => p e.1 e.2)
        (fun e => (R e : ℤ)) e r)| ≤ 9 := by
  classical
  let rem : Fin 3 × Fin n → ℤ := fun e => (R e : ℤ) - 2 * evenGridCenter (R e)
  have hrem : ∀ e, 0 ≤ rem e ∧ rem e ≤ 3 := by
    intro e
    exact fw_radius_centering_remainder_any (R e)
  have hdiff : ∀ k : Fin 3, -3 ≤ rem (k,r) - rem (k,(p k).symm r) ∧
      rem (k,r) - rem (k,(p k).symm r) ≤ 3 := by
    intro k
    have h₁ := hrem (k,r)
    have h₂ := hrem (k,(p k).symm r)
    omega
  have hlo : (-9 : ℤ) ≤ ∑ k : Fin 3, (rem (k,r) - rem (k,(p k).symm r)) := by
    calc
      (-9 : ℤ) = ∑ _ : Fin 3, (-3 : ℤ) := by norm_num
      _ ≤ _ := Finset.sum_le_sum (fun k _ => (hdiff k).1)
  have hhi : (∑ k : Fin 3, (rem (k,r) - rem (k,(p k).symm r))) ≤ 9 := by
    calc
      _ ≤ ∑ _ : Fin 3, (3 : ℤ) := Finset.sum_le_sum (fun k _ => (hdiff k).2)
      _ = 9 := by norm_num
  have hi := hinvoice r
  rw [fw_three_permutation_transfer] at hi
  rw [fw_three_permutation_transfer, abs_le]
  simp only [rem, Finset.sum_sub_distrib, ← Finset.mul_sum] at hlo hhi
  simp only [Finset.sum_sub_distrib] at hi ⊢
  constructor <;> omega

end
end Sude
