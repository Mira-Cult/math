import Sude.FWAllLineMassReallocation

/-! Explicit scalar invoices for the all-line FW bridge and wide midpoint
allocation. No placement, diagonal mass, or grid claim is made here. -/
namespace Sude
noncomputable section

/-- The squared-incidence cap for the five bridge stages. -/
def fwBridgeMidpointMass : ℝ := 94

/-- The common all-line cap used for the actual FW wide stage count `3K`. -/
def fwWideMidpointMass (n : ℕ) : ℝ :=
  (18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4

/-- Positive scalar invoice for the bridge midpoint concentration. -/
def fwBridgeMidpointInvoice (X : ℝ) : ℝ :=
  2 * ((23 / 924 : ℝ) * X) ^ 2 * fwBridgeMidpointMass

/-- Positive scalar invoice for the wide midpoint concentration. -/
def fwWideMidpointInvoice (n : ℕ) (X : ℝ) : ℝ :=
  2 * (2 * X / 235) ^ 2 * fwWideMidpointMass n

/-- Both invoices are strictly positive for positive X, including zero wide
stages: the conservative wide mass cap is then still four. -/
theorem fw_double_block_scalar_invoices_pos (n : ℕ) (X : ℝ) (hX : 0 < X) :
    0 < fwBridgeMidpointInvoice X ∧ 0 < fwWideMidpointInvoice n X := by
  unfold fwBridgeMidpointInvoice fwBridgeMidpointMass fwWideMidpointInvoice fwWideMidpointMass
  constructor <;> positivity

/-- The scalar choices exactly pay both invoice hypotheses of the all-line
FW allocation, with no numerical estimate or mass-existence claim. -/
theorem fw_double_block_scalar_invoice_equalities (n : ℕ) (X : ℝ) :
    2 * ((23 / 924 : ℝ) * X) ^ 2 * 94 = fwBridgeMidpointInvoice X ∧
    2 * (2 * X / 235) ^ 2 * ((18 : ℝ) * ((3 * (n / 450) : ℕ) : ℝ) + 4) =
      fwWideMidpointInvoice n X := by
  constructor <;> rfl


/-- Scalar square-root normalization for the `2n+2` labelled-line budget. -/
theorem fw_double_block_threshold_identity (n : ℕ) (X c M : ℝ)
    (hX : 0 ≤ X) (hc : 0 ≤ c) :
    Real.sqrt ((2 * (c * X) ^ 2 * M) * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2) =
      X * c * Real.sqrt (M * Real.log (8 * (n : ℝ) + 8)) := by
  have hlog : (4 : ℝ) * (((n + n) + 2 : ℕ) : ℝ) = 8 * (n : ℝ) + 8 := by push_cast; ring
  rw [hlog]
  have heq : (2 * (c * X) ^ 2 * M) * Real.log (8 * (n : ℝ) + 8) / 2 =
      (X * c) ^ 2 * (M * Real.log (8 * (n : ℝ) + 8)) := by ring
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hX hc)]

/-- The bridge invoice gives the exact FW bridge midpoint threshold. -/
theorem fw_bridge_midpoint_invoice_threshold (n : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    Real.sqrt (fwBridgeMidpointInvoice X * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2) =
      X * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8)) := by
  simpa [fwBridgeMidpointInvoice, fwBridgeMidpointMass] using
    fw_double_block_threshold_identity n X (23 / 924) 94 hX (by norm_num)

/-- The wide invoice uses the FW stage count `3 * (n / 450)`, and its
threshold remains valid in the scalar zero-stage case. -/
theorem fw_wide_midpoint_invoice_threshold (n : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    Real.sqrt (fwWideMidpointInvoice n X * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2) =
      X * (2 / 235 : ℝ) * Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) *
        Real.log (8 * (n : ℝ) + 8)) := by
  have hmul : (2 * X / 235 : ℝ) = (2 / 235 : ℝ) * X := by ring
  have hmass : fwWideMidpointMass n = (54 : ℝ) * ((n / 450 : ℕ) : ℝ) + 4 := by
    unfold fwWideMidpointMass
    push_cast
    ring
  simpa [fwWideMidpointInvoice, hmul, hmass] using
    fw_double_block_threshold_identity n X (2 / 235) (54 * ((n / 450 : ℕ) : ℝ) + 4) hX (by norm_num)

end
end Sude
