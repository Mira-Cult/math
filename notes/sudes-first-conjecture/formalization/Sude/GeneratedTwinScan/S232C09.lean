import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22085)) 487718957 487751725 = 87 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487718957 487751725).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22085 487718957 487751725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22085)) 487751725 487784493 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 487751725 487784493).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22085 487751725 487784493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22086)) 487784493 487817261 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 487784493 487817261).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22086 487784493 487817261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22087)) 487817261 487850029 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487817261 487850029).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22087 487817261 487850029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487718957 487784493).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 487718957 ≤ 487751725)
    (by decide : 487751725 ≤ 487784493) block0 block1

theorem join_0_1 : (twinPrimeSegment 487784493 487850029).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 487784493 ≤ 487817261)
    (by decide : 487817261 ≤ 487850029) block2 block3

theorem join_1_0 : (twinPrimeSegment 487718957 487850029).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 487718957 ≤ 487784493)
    (by decide : 487784493 ≤ 487850029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487718957 487850029).card = 433 := join_1_0

end S232C09
end Sude.GeneratedTwinScan
