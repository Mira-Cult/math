import Sude.BTGrowingWidths

/-! A generic lower comparison for supplied bounded-width BT traces. The
    monotone recurrence and its width domination are explicit hypotheses. -/
namespace Sude
noncomputable section

theorem fw_bt_generic_width_trace_lower {j R floor : ℕ} {stages : List BTSelectedStage}
    (F : ℕ → ℕ) (G : ℕ → ℕ → ℕ) (lower : ℕ → ℕ → ℝ)
    (hzero : ∀ r, G 0 r = r)
    (hsucc : ∀ k r, G (k+1) r = G k (r+F r))
    (hmono : Monotone F)
    (hstep : ∀ (j R gap : ℕ), floor ≤ R → lower j R ≤ (gap : ℝ) → F R ≤ gap)
    (widths : BTWidthTrace lower j R stages)
    (hmin : ∀ stage ∈ stages, stage.minimum ≤ stage.gap) :
    ∀ r : ℕ, floor ≤ r → r ≤ R →
      G stages.length r ≤ R + (stages.map BTSelectedStage.gap).sum := by
  induction widths with
  | nil j R => intro r _ hr; simpa only [List.length_nil, List.map_nil, List.sum_nil, Nat.add_zero, hzero] using hr
  | cons j R stage tail hwidth hrest ih =>
    intro r hr hrR
    have hgap : lower j R ≤ (stage.gap : ℝ) := hwidth.trans (hmin stage (by simp))
    have hinc := hstep j R stage.gap (le_trans hr hrR) hgap
    have hnext : r + F r ≤ R + stage.gap := Nat.add_le_add hrR ((hmono hrR).trans hinc)
    have ht : ∀ s ∈ tail, s.minimum ≤ s.gap := by
      intro s hs
      exact hmin s (by simp [hs])
    have hout := ih ht (r + F r) (hr.trans (Nat.le_add_right r _)) hnext
    simpa only [List.length_cons, hsucc, List.map_cons, List.sum_cons, Nat.add_assoc] using hout

end
end Sude
