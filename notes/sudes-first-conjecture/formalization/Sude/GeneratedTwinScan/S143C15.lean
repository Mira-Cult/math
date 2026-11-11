import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17375)) 301858861 301891629 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 301858861 301891629).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17375 301858861 301891629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17375)) 301891629 301924397 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 301891629 301924397).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17375 301891629 301924397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17376)) 301924397 301957165 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 301924397 301957165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17376 301924397 301957165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17377)) 301957165 301989933 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 301957165 301989933).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17377 301957165 301989933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 301858861 301924397).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 301858861 ≤ 301891629)
    (by decide : 301891629 ≤ 301924397) block0 block1

theorem join_0_1 : (twinPrimeSegment 301924397 301989933).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 301924397 ≤ 301957165)
    (by decide : 301957165 ≤ 301989933) block2 block3

theorem join_1_0 : (twinPrimeSegment 301858861 301989933).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 301858861 ≤ 301924397)
    (by decide : 301924397 ≤ 301989933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 301858861 301989933).card = 442 := join_1_0

end S143C15
end Sude.GeneratedTwinScan
