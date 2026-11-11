import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17895)) 320208941 320241709 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 320208941 320241709).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17895 320208941 320241709
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17896)) 320241709 320274477 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 320241709 320274477).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17896 320241709 320274477
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17897)) 320274477 320307245 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 320274477 320307245).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17897 320274477 320307245
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17898)) 320307245 320340013 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 320307245 320340013).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17898 320307245 320340013
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 320208941 320274477).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 320208941 ≤ 320241709)
    (by decide : 320241709 ≤ 320274477) block0 block1

theorem join_0_1 : (twinPrimeSegment 320274477 320340013).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 320274477 ≤ 320307245)
    (by decide : 320307245 ≤ 320340013) block2 block3

theorem join_1_0 : (twinPrimeSegment 320208941 320340013).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 320208941 ≤ 320274477)
    (by decide : 320274477 ≤ 320340013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 320208941 320340013).card = 451 := join_1_0

end S152C11
end Sude.GeneratedTwinScan
