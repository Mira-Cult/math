import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14046)) 197263405 197296173 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197263405 197296173).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14046 197263405 197296173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14047)) 197296173 197328941 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197296173 197328941).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14047 197296173 197328941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14048)) 197328941 197361709 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197328941 197361709).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14048 197328941 197361709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14049)) 197361709 197394477 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 197361709 197394477).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14049 197361709 197394477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197263405 197328941).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 197263405 ≤ 197296173)
    (by decide : 197296173 ≤ 197328941) block0 block1

theorem join_0_1 : (twinPrimeSegment 197328941 197394477).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 197328941 ≤ 197361709)
    (by decide : 197361709 ≤ 197394477) block2 block3

theorem join_1_0 : (twinPrimeSegment 197263405 197394477).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 197263405 ≤ 197328941)
    (by decide : 197328941 ≤ 197394477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197263405 197394477).card = 479 := join_1_0

end S094C01
end Sude.GeneratedTwinScan
