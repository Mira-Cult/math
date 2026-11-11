import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18200)) 331218989 331251757 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 331218989 331251757).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18200 331218989 331251757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18201)) 331251757 331284525 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 331251757 331284525).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18201 331251757 331284525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18202)) 331284525 331317293 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 331284525 331317293).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18202 331284525 331317293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18203)) 331317293 331350061 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 331317293 331350061).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18203 331317293 331350061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 331218989 331284525).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 331218989 ≤ 331251757)
    (by decide : 331251757 ≤ 331284525) block0 block1

theorem join_0_1 : (twinPrimeSegment 331284525 331350061).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 331284525 ≤ 331317293)
    (by decide : 331317293 ≤ 331350061) block2 block3

theorem join_1_0 : (twinPrimeSegment 331218989 331350061).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 331218989 ≤ 331284525)
    (by decide : 331284525 ≤ 331350061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 331218989 331350061).card = 476 := join_1_0

end S157C15
end Sude.GeneratedTwinScan
