import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19810)) 392429613 392462381 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 392429613 392462381).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19810 392429613 392462381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19811)) 392462381 392495149 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 392462381 392495149).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19811 392462381 392495149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19812)) 392495149 392527917 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 392495149 392527917).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19812 392495149 392527917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19813)) 392527917 392560685 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 392527917 392560685).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19813 392527917 392560685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 392429613 392495149).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 392429613 ≤ 392462381)
    (by decide : 392462381 ≤ 392495149) block0 block1

theorem join_0_1 : (twinPrimeSegment 392495149 392560685).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 392495149 ≤ 392527917)
    (by decide : 392527917 ≤ 392560685) block2 block3

theorem join_1_0 : (twinPrimeSegment 392429613 392560685).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 392429613 ≤ 392495149)
    (by decide : 392495149 ≤ 392560685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 392429613 392560685).card = 454 := join_1_0

end S187C02
end Sude.GeneratedTwinScan
