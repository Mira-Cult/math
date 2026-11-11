import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19419)) 377094189 377126957 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 377094189 377126957).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19419 377094189 377126957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19420)) 377126957 377159725 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 377126957 377159725).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19420 377126957 377159725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19421)) 377159725 377192493 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 377159725 377192493).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19421 377159725 377192493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19422)) 377192493 377225261 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 377192493 377225261).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19422 377192493 377225261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 377094189 377159725).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 377094189 ≤ 377126957)
    (by decide : 377126957 ≤ 377159725) block0 block1

theorem join_0_1 : (twinPrimeSegment 377159725 377225261).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 377159725 ≤ 377192493)
    (by decide : 377192493 ≤ 377225261) block2 block3

theorem join_1_0 : (twinPrimeSegment 377094189 377225261).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 377094189 ≤ 377159725)
    (by decide : 377159725 ≤ 377225261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 377094189 377225261).card = 435 := join_1_0

end S179C13
end Sude.GeneratedTwinScan
