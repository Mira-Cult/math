import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21939)) 481296429 481329197 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481296429 481329197).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21939 481296429 481329197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21939)) 481329197 481361965 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481329197 481361965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21939 481329197 481361965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21940)) 481361965 481394733 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 481361965 481394733).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21940 481361965 481394733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21941)) 481394733 481427501 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481394733 481427501).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21941 481394733 481427501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481296429 481361965).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 481296429 ≤ 481329197)
    (by decide : 481329197 ≤ 481361965) block0 block1

theorem join_0_1 : (twinPrimeSegment 481361965 481427501).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 481361965 ≤ 481394733)
    (by decide : 481394733 ≤ 481427501) block2 block3

theorem join_1_0 : (twinPrimeSegment 481296429 481427501).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 481296429 ≤ 481361965)
    (by decide : 481361965 ≤ 481427501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481296429 481427501).card = 409 := join_1_0

end S229C08
end Sude.GeneratedTwinScan
