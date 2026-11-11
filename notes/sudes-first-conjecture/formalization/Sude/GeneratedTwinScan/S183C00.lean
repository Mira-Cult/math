import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19591)) 383778861 383811629 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 383778861 383811629).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19591 383778861 383811629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19591)) 383811629 383844397 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383811629 383844397).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19591 383811629 383844397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19592)) 383844397 383877165 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383844397 383877165).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19592 383844397 383877165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19593)) 383877165 383909933 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 383877165 383909933).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19593 383877165 383909933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 383778861 383844397).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 383778861 ≤ 383811629)
    (by decide : 383811629 ≤ 383844397) block0 block1

theorem join_0_1 : (twinPrimeSegment 383844397 383909933).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 383844397 ≤ 383877165)
    (by decide : 383877165 ≤ 383909933) block2 block3

theorem join_1_0 : (twinPrimeSegment 383778861 383909933).card = 408 := by
  simpa using combineTwinPrimeSegments (by decide : 383778861 ≤ 383844397)
    (by decide : 383844397 ≤ 383909933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 383778861 383909933).card = 408 := join_1_0

end S183C00
end Sude.GeneratedTwinScan
