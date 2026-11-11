import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16881)) 284950573 284983341 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284950573 284983341).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16881 284950573 284983341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16882)) 284983341 285016109 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284983341 285016109).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16882 284983341 285016109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16883)) 285016109 285048877 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 285016109 285048877).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16883 285016109 285048877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16884)) 285048877 285081645 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 285048877 285081645).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16884 285048877 285081645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284950573 285016109).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 284950573 ≤ 284983341)
    (by decide : 284983341 ≤ 285016109) block0 block1

theorem join_0_1 : (twinPrimeSegment 285016109 285081645).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 285016109 ≤ 285048877)
    (by decide : 285048877 ≤ 285081645) block2 block3

theorem join_1_0 : (twinPrimeSegment 284950573 285081645).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 284950573 ≤ 285016109)
    (by decide : 285016109 ≤ 285081645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284950573 285081645).card = 448 := join_1_0

end S135C14
end Sude.GeneratedTwinScan
