import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16074)) 258342957 258375725 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 258342957 258375725).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16074 258342957 258375725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16075)) 258375725 258408493 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 258375725 258408493).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16075 258375725 258408493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16076)) 258408493 258441261 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258408493 258441261).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16076 258408493 258441261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16077)) 258441261 258474029 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258441261 258474029).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16077 258441261 258474029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 258342957 258408493).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 258342957 ≤ 258375725)
    (by decide : 258375725 ≤ 258408493) block0 block1

theorem join_0_1 : (twinPrimeSegment 258408493 258474029).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 258408493 ≤ 258441261)
    (by decide : 258441261 ≤ 258474029) block2 block3

theorem join_1_0 : (twinPrimeSegment 258342957 258474029).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 258342957 ≤ 258408493)
    (by decide : 258408493 ≤ 258474029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 258342957 258474029).card = 436 := join_1_0

end S123C03
end Sude.GeneratedTwinScan
