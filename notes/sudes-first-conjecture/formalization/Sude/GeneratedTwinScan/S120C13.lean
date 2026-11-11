import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15918)) 253362221 253394989 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 253362221 253394989).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15918 253362221 253394989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15919)) 253394989 253427757 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 253394989 253427757).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15919 253394989 253427757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15920)) 253427757 253460525 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 253427757 253460525).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15920 253427757 253460525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15921)) 253460525 253493293 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 253460525 253493293).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15921 253460525 253493293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 253362221 253427757).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 253362221 ≤ 253394989)
    (by decide : 253394989 ≤ 253427757) block0 block1

theorem join_0_1 : (twinPrimeSegment 253427757 253493293).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 253427757 ≤ 253460525)
    (by decide : 253460525 ≤ 253493293) block2 block3

theorem join_1_0 : (twinPrimeSegment 253362221 253493293).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 253362221 ≤ 253427757)
    (by decide : 253427757 ≤ 253493293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 253362221 253493293).card = 493 := join_1_0

end S120C13
end Sude.GeneratedTwinScan
