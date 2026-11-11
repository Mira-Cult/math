import Sude.FWSubwheelDomination
namespace Sude
noncomputable section

theorem fw_wheel_cutoff_mono (W : ℕ) (hW : 0 < W) :
    Monotone (fun T => fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)) := by
  intro a b hab
  obtain ⟨i, hi⟩ := fw_wheel_cutoff_attained W b hW
  have ha := fw_wheel_cutoff_le_next (fwWheelUnit W) W (Nat.totient W) a
    (Nat.totient_pos.mpr hW) (fw_wheel_unit_period W hW)
    (fw_wheel_unit_strictMono W hW) i
  have hm := (fw_wheel_unit_strictMono W hW).monotone (show i + a + 1 ≤ i + (b + 1) by omega)
  dsimp only
  rw [hi]
  exact ha.trans (Nat.sub_le_sub_right hm _)
end
end Sude
