import Sude.FWRectangleCapacity

/-! Rectangle arithmetic for the initial FW bridge, retained-seed, and wide
roles. No rectangle budget for a subsequent growth trace is asserted. -/
namespace Sude

/-- At the common early layout, taking `P₀ = 16` counts the sixteen retained
seed stages, five bridge stages, and `3 * (n / 450)` wide stages. All three
role intervals fit and RP1's square capacity holds throughout the FW range. -/
theorem fw_initial_wide_rectangle_capacity {n : ℕ} (hn : 19485 ≤ n) :
    let L := fwJointRectangleCount n 16
    5 * (4 * 6) ≤ L ∧
    5 * (4 * 6) + 16 * (4 * 6) ≤ L ∧
    5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L ∧
    2 * L + 1 ≤ n := by
  dsimp only
  obtain ⟨_, hb, hcapacity⟩ := fw_full_rectangle_capacity_of_cap hn (P₀ := 16) (by decide)
  refine ⟨hb, ?_, ?_, ?_⟩
  · unfold fwJointRectangleCount
    omega
  · unfold fwJointRectangleCount
    omega
  · omega

end Sude
