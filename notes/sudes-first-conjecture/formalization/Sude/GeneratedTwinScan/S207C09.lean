import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20864)) 435290157 435322925 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 435290157 435322925).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20864 435290157 435322925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20865)) 435322925 435355693 = 88 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 435322925 435355693).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20865 435322925 435355693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20865)) 435355693 435388461 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 435355693 435388461).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20865 435355693 435388461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20866)) 435388461 435421229 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 435388461 435421229).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20866 435388461 435421229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 435290157 435355693).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 435290157 ≤ 435322925)
    (by decide : 435322925 ≤ 435355693) block0 block1

theorem join_0_1 : (twinPrimeSegment 435355693 435421229).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 435355693 ≤ 435388461)
    (by decide : 435388461 ≤ 435421229) block2 block3

theorem join_1_0 : (twinPrimeSegment 435290157 435421229).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 435290157 ≤ 435355693)
    (by decide : 435355693 ≤ 435421229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 435290157 435421229).card = 444 := join_1_0

end S207C09
end Sude.GeneratedTwinScan
