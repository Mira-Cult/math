import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21434)) 459407405 459440173 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 459407405 459440173).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21434 459407405 459440173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21435)) 459440173 459472941 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 459440173 459472941).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21435 459440173 459472941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21436)) 459472941 459505709 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 459472941 459505709).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21436 459472941 459505709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21436)) 459505709 459538477 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 459505709 459538477).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21436 459505709 459538477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 459407405 459472941).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 459407405 ≤ 459440173)
    (by decide : 459440173 ≤ 459472941) block0 block1

theorem join_0_1 : (twinPrimeSegment 459472941 459538477).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 459472941 ≤ 459505709)
    (by decide : 459505709 ≤ 459538477) block2 block3

theorem join_1_0 : (twinPrimeSegment 459407405 459538477).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 459407405 ≤ 459472941)
    (by decide : 459472941 ≤ 459538477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 459407405 459538477).card = 434 := join_1_0

end S219C01
end Sude.GeneratedTwinScan
