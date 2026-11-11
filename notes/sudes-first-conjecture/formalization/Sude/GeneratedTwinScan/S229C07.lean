import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21936)) 481165357 481198125 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481165357 481198125).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21936 481165357 481198125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21936)) 481198125 481230893 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481198125 481230893).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21936 481198125 481230893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21937)) 481230893 481263661 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 481230893 481263661).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21937 481230893 481263661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21938)) 481263661 481296429 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481263661 481296429).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21938 481263661 481296429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481165357 481230893).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 481165357 ≤ 481198125)
    (by decide : 481198125 ≤ 481230893) block0 block1

theorem join_0_1 : (twinPrimeSegment 481230893 481296429).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 481230893 ≤ 481263661)
    (by decide : 481263661 ≤ 481296429) block2 block3

theorem join_1_0 : (twinPrimeSegment 481165357 481296429).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 481165357 ≤ 481230893)
    (by decide : 481230893 ≤ 481296429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481165357 481296429).card = 441 := join_1_0

end S229C07
end Sude.GeneratedTwinScan
