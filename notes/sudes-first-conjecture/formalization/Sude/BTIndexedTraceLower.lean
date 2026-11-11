import Sude.BTGenericTraceLower
/-! Comparison of a supplied BT width trace with an abstract indexed lower
    table. All stage bounds and recurrence inequalities remain hypotheses. -/
namespace Sude
noncomputable section

theorem fw_bt_indexed_width_trace_lower {j R floor : ℕ} {stages : List BTSelectedStage}
    (F T : ℕ → ℕ) (lower : ℕ → ℕ → ℝ)
    (hmono : Monotone F)
    (hfloor : ∀ i, floor ≤ T i)
    (hnext : ∀ i, T (i+1) ≤ T i + F (T i))
    (hstep : ∀ (j R gap : ℕ), floor ≤ R → lower j R ≤ (gap : ℝ) → F R ≤ gap)
    (widths : BTWidthTrace lower j R stages)
    (hmin : ∀ stage ∈ stages, stage.minimum ≤ stage.gap) :
    ∀ i : ℕ, T i ≤ R →
      T (i + stages.length) ≤ R + (stages.map BTSelectedStage.gap).sum := by
  induction widths with
  | nil j R =>
    intro i hi
    simpa only [List.length_nil, Nat.add_zero, List.map_nil, List.sum_nil] using hi
  | cons j R stage tail hwidth hrest ih =>
    intro i hi
    have hgap : lower j R ≤ (stage.gap : ℝ) := hwidth.trans (hmin stage (by simp))
    have hinc := hstep j R stage.gap (le_trans (hfloor i) hi) hgap
    have hnextR : T (i+1) ≤ R + stage.gap :=
      (hnext i).trans (Nat.add_le_add hi ((hmono hi).trans hinc))
    have ht : ∀ s ∈ tail, s.minimum ≤ s.gap := by
      intro s hs
      exact hmin s (by simp [hs])
    have hout := ih ht (i+1) hnextR
    simpa only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hout

theorem fw_bt_bounded_indexed_width_trace_lower {j R N : ℕ} {stages : List BTSelectedStage}
    (T F : ℕ → ℕ) (lower : ℕ → ℕ → ℝ)
    (hfloor : ∀ i ≤ N, 39 ≤ T i)
    (htable : ∀ i < N, T (i + 1) ≤ T i + F (T i))
    (hmono : Monotone F)
    (hgap : ∀ (j R gap : ℕ), 39 ≤ R → lower j R ≤ (gap : ℝ) → F R ≤ gap)
    (widths : BTWidthTrace lower j R stages)
    (hmin : ∀ s ∈ stages, s.minimum ≤ s.gap) :
    ∀ i, i + stages.length ≤ N → T i ≤ R →
      T (i + stages.length) ≤ R + (stages.map BTSelectedStage.gap).sum := by
  induction widths with
  | nil j R =>
    intro i hi hTR
    simpa only [List.length_nil, List.map_nil, List.sum_nil, Nat.add_zero] using hTR
  | cons j R stage tail hwidth hrest ih =>
    intro i hi hTR
    have hi10 : i < N := by simp only [List.length_cons] at hi; omega
    have hinc : F R ≤ stage.gap :=
      hgap j R stage.gap ((hfloor i (by omega)).trans hTR)
        (hwidth.trans (hmin stage (by simp)))
    have hnext : T (i + 1) ≤ R + stage.gap :=
      (htable i hi10).trans (Nat.add_le_add hTR ((hmono hTR).trans hinc))
    have ht : ∀ s ∈ tail, s.minimum ≤ s.gap := by
      intro s hs
      exact hmin s (by simp [hs])
    have htail : i + 1 + tail.length ≤ N := by simp only [List.length_cons] at hi; omega
    have hout := ih ht (i + 1) htail hnext
    simpa only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hout

end
end Sude
