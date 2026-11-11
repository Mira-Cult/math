import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22505)) 506462253 506495021 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 506462253 506495021).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22505 506462253 506495021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22506)) 506495021 506527789 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 506495021 506527789).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22506 506495021 506527789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22506)) 506527789 506560557 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 506527789 506560557).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22506 506527789 506560557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22507)) 506560557 506593325 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 506560557 506593325).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22507 506560557 506593325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 506462253 506527789).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 506462253 ≤ 506495021)
    (by decide : 506495021 ≤ 506527789) block0 block1

theorem join_0_1 : (twinPrimeSegment 506527789 506593325).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 506527789 ≤ 506560557)
    (by decide : 506560557 ≤ 506593325) block2 block3

theorem join_1_0 : (twinPrimeSegment 506462253 506593325).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 506462253 ≤ 506527789)
    (by decide : 506527789 ≤ 506593325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 506462253 506593325).card = 412 := join_1_0

end S241C08
end Sude.GeneratedTwinScan
