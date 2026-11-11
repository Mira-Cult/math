import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16004)) 256114733 256147501 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 256114733 256147501).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16004 256114733 256147501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16005)) 256147501 256180269 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 256147501 256180269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16005 256147501 256180269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16006)) 256180269 256213037 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 256180269 256213037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16006 256180269 256213037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16007)) 256213037 256245805 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 256213037 256245805).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16007 256213037 256245805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 256114733 256180269).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 256114733 ≤ 256147501)
    (by decide : 256147501 ≤ 256180269) block0 block1

theorem join_0_1 : (twinPrimeSegment 256180269 256245805).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 256180269 ≤ 256213037)
    (by decide : 256213037 ≤ 256245805) block2 block3

theorem join_1_0 : (twinPrimeSegment 256114733 256245805).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 256114733 ≤ 256180269)
    (by decide : 256180269 ≤ 256245805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 256114733 256245805).card = 468 := join_1_0

end S122C02
end Sude.GeneratedTwinScan
