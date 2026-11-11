import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16381)) 268304429 268337197 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268304429 268337197).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16381 268304429 268337197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16382)) 268337197 268369965 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268337197 268369965).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16382 268337197 268369965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16383)) 268369965 268402733 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 268369965 268402733).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16383 268369965 268402733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16384)) 268402733 268435501 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 268402733 268435501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16384 268402733 268435501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268304429 268369965).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 268304429 ≤ 268337197)
    (by decide : 268337197 ≤ 268369965) block0 block1

theorem join_0_1 : (twinPrimeSegment 268369965 268435501).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 268369965 ≤ 268402733)
    (by decide : 268402733 ≤ 268435501) block2 block3

theorem join_1_0 : (twinPrimeSegment 268304429 268435501).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 268304429 ≤ 268369965)
    (by decide : 268369965 ≤ 268435501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268304429 268435501).card = 461 := join_1_0

end S127C15
end Sude.GeneratedTwinScan
