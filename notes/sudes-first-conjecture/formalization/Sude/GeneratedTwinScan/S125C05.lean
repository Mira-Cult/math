import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16212)) 262799405 262832173 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262799405 262832173).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16212 262799405 262832173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16213)) 262832173 262864941 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 262832173 262864941).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16213 262832173 262864941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16214)) 262864941 262897709 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 262864941 262897709).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16214 262864941 262897709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16215)) 262897709 262930477 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 262897709 262930477).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16215 262897709 262930477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 262799405 262864941).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 262799405 ≤ 262832173)
    (by decide : 262832173 ≤ 262864941) block0 block1

theorem join_0_1 : (twinPrimeSegment 262864941 262930477).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 262864941 ≤ 262897709)
    (by decide : 262897709 ≤ 262930477) block2 block3

theorem join_1_0 : (twinPrimeSegment 262799405 262930477).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 262799405 ≤ 262864941)
    (by decide : 262864941 ≤ 262930477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262799405 262930477).card = 449 := join_1_0

end S125C05
end Sude.GeneratedTwinScan
