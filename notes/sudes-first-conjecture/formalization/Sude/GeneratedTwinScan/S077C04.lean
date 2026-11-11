import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12729)) 162005037 162037805 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162005037 162037805).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12729 162005037 162037805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12730)) 162037805 162070573 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162037805 162070573).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12730 162037805 162070573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12731)) 162070573 162103341 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162070573 162103341).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12731 162070573 162103341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12733)) 162103341 162136109 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 162103341 162136109).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12733 162103341 162136109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162005037 162070573).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 162005037 ≤ 162037805)
    (by decide : 162037805 ≤ 162070573) block0 block1

theorem join_0_1 : (twinPrimeSegment 162070573 162136109).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 162070573 ≤ 162103341)
    (by decide : 162103341 ≤ 162136109) block2 block3

theorem join_1_0 : (twinPrimeSegment 162005037 162136109).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 162005037 ≤ 162070573)
    (by decide : 162070573 ≤ 162136109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162005037 162136109).card = 464 := join_1_0

end S077C04
end Sude.GeneratedTwinScan
