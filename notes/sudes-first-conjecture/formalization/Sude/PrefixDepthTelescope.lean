import Sude.CentralWindow

/-! Telescoping global, per-depth prefix-allocation errors. The hypothesis
must bound each entire depth, not individual groups or stages. -/
namespace Sude
noncomputable section

/-- If each global depth changes a line total by at most `B`, the total
change through `D` depths is at most `D*B`. This is an algebraic bound; it
does not construct the depth sequence or its per-depth estimates. -/
theorem prefix_depth_telescope (f : ℕ → ℝ) (D : ℕ) (B : ℝ)
    (hstep : ∀ i < D, |f (i + 1) - f i| ≤ B) :
    |f D - f 0| ≤ (D : ℝ) * B := by
  induction D with
  | zero => simp
  | succ D ih =>
    have hprev : |f D - f 0| ≤ (D : ℝ) * B :=
      ih (fun i hi => hstep i (by omega))
    have hnext : |f (D + 1) - f D| ≤ B := hstep D (by omega)
    have heq : f (D + 1) - f 0 = (f (D + 1) - f D) + (f D - f 0) := by ring
    calc
      |f (D + 1) - f 0| = |(f (D + 1) - f D) + (f D - f 0)| := by rw [heq]
      _ ≤ |f (D + 1) - f D| + |f D - f 0| := abs_add_le _ _
      _ ≤ B + (D : ℝ) * B := add_le_add hnext hprev
      _ = ((D + 1 : ℕ) : ℝ) * B := by push_cast; ring

end
end Sude
