import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S242C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22551)) 508559405 508592173 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 508559405 508592173).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22551 508559405 508592173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22552)) 508592173 508624941 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 508592173 508624941).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22552 508592173 508624941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22553)) 508624941 508657709 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 508624941 508657709).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22553 508624941 508657709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22554)) 508657709 508690477 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 508657709 508690477).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22554 508657709 508690477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 508559405 508624941).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 508559405 ≤ 508592173)
    (by decide : 508592173 ≤ 508624941) block0 block1

theorem join_0_1 : (twinPrimeSegment 508624941 508690477).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 508624941 ≤ 508657709)
    (by decide : 508657709 ≤ 508690477) block2 block3

theorem join_1_0 : (twinPrimeSegment 508559405 508690477).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 508559405 ≤ 508624941)
    (by decide : 508624941 ≤ 508690477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 508559405 508690477).card = 438 := join_1_0

end S242C08
end Sude.GeneratedTwinScan
