import Sude.FWEntropyCurvature
import Sude.FWEntropyHalfEndpoint

/-! The uniform large-cut entropy inequality for FW's constants. -/
namespace Sude
noncomputable section

/-- The FW entropy lies strictly below `-1/250` on the entire closed
interval from `1/256` to `1/2`. This is an analytic inequality only; it
asserts no probability estimate or expander existence. -/
theorem fw_entropy_interval_gate {t : ℝ} (ht0 : 1 / 256 ≤ t) (ht1 : t ≤ 1 / 2) :
    fwCutEntropy t < -(1 : ℝ) / 250 := by
  exact lt_of_le_of_lt (fw_entropy_le_endpoint_max ht0 ht1)
    (max_lt fw_entropy_small_endpoint fw_entropy_half_endpoint)

end
end Sude
