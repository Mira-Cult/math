import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13753)) 189136941 189169709 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 189136941 189169709).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13753 189136941 189169709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13755)) 189169709 189202477 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 189169709 189202477).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13755 189169709 189202477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13756)) 189202477 189235245 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 189202477 189235245).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13756 189202477 189235245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13757)) 189235245 189268013 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 189235245 189268013).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13757 189235245 189268013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 189136941 189202477).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 189136941 ≤ 189169709)
    (by decide : 189169709 ≤ 189202477) block0 block1

theorem join_0_1 : (twinPrimeSegment 189202477 189268013).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 189202477 ≤ 189235245)
    (by decide : 189235245 ≤ 189268013) block2 block3

theorem join_1_0 : (twinPrimeSegment 189136941 189268013).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 189136941 ≤ 189202477)
    (by decide : 189202477 ≤ 189268013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 189136941 189268013).card = 501 := join_1_0

end S090C03
end Sude.GeneratedTwinScan
