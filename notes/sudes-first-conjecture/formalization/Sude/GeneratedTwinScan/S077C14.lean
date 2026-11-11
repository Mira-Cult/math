import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12780)) 163315757 163348525 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 163315757 163348525).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12780 163315757 163348525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12782)) 163348525 163381293 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 163348525 163381293).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12782 163348525 163381293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12783)) 163381293 163414061 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 163381293 163414061).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12783 163381293 163414061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12784)) 163414061 163446829 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 163414061 163446829).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12784 163414061 163446829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 163315757 163381293).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 163315757 ≤ 163348525)
    (by decide : 163348525 ≤ 163381293) block0 block1

theorem join_0_1 : (twinPrimeSegment 163381293 163446829).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 163381293 ≤ 163414061)
    (by decide : 163414061 ≤ 163446829) block2 block3

theorem join_1_0 : (twinPrimeSegment 163315757 163446829).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 163315757 ≤ 163381293)
    (by decide : 163381293 ≤ 163446829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 163315757 163446829).card = 472 := join_1_0

end S077C14
end Sude.GeneratedTwinScan
