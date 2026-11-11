import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16962)) 287703085 287735853 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287703085 287735853).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16962 287703085 287735853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16963)) 287735853 287768621 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287735853 287768621).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16963 287735853 287768621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16964)) 287768621 287801389 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 287768621 287801389).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16964 287768621 287801389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16965)) 287801389 287834157 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287801389 287834157).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16965 287801389 287834157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287703085 287768621).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 287703085 ≤ 287735853)
    (by decide : 287735853 ≤ 287768621) block0 block1

theorem join_0_1 : (twinPrimeSegment 287768621 287834157).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 287768621 ≤ 287801389)
    (by decide : 287801389 ≤ 287834157) block2 block3

theorem join_1_0 : (twinPrimeSegment 287703085 287834157).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 287703085 ≤ 287768621)
    (by decide : 287768621 ≤ 287834157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287703085 287834157).card = 441 := join_1_0

end S137C03
end Sude.GeneratedTwinScan
