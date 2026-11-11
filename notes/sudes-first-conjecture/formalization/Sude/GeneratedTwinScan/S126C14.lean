import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16312)) 266076205 266108973 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 266076205 266108973).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16312 266076205 266108973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16313)) 266108973 266141741 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 266108973 266141741).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16313 266108973 266141741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16314)) 266141741 266174509 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 266141741 266174509).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16314 266141741 266174509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16315)) 266174509 266207277 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 266174509 266207277).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16315 266174509 266207277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 266076205 266141741).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 266076205 ≤ 266108973)
    (by decide : 266108973 ≤ 266141741) block0 block1

theorem join_0_1 : (twinPrimeSegment 266141741 266207277).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 266141741 ≤ 266174509)
    (by decide : 266174509 ≤ 266207277) block2 block3

theorem join_1_0 : (twinPrimeSegment 266076205 266207277).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 266076205 ≤ 266141741)
    (by decide : 266141741 ≤ 266207277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 266076205 266207277).card = 445 := join_1_0

end S126C14
end Sude.GeneratedTwinScan
