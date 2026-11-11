import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20008)) 400293933 400326701 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 400293933 400326701).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20008 400293933 400326701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20008)) 400326701 400359469 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 400326701 400359469).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20008 400326701 400359469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20009)) 400359469 400392237 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 400359469 400392237).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20009 400359469 400392237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20010)) 400392237 400425005 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 400392237 400425005).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20010 400392237 400425005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 400293933 400359469).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 400293933 ≤ 400326701)
    (by decide : 400326701 ≤ 400359469) block0 block1

theorem join_0_1 : (twinPrimeSegment 400359469 400425005).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 400359469 ≤ 400392237)
    (by decide : 400392237 ≤ 400425005) block2 block3

theorem join_1_0 : (twinPrimeSegment 400293933 400425005).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 400293933 ≤ 400359469)
    (by decide : 400359469 ≤ 400425005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 400293933 400425005).card = 440 := join_1_0

end S190C14
end Sude.GeneratedTwinScan
