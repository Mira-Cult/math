import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S247C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22797)) 519700525 519733293 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 519700525 519733293).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22797 519700525 519733293
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22798)) 519733293 519766061 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 519733293 519766061).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22798 519733293 519766061
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22799)) 519766061 519798829 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 519766061 519798829).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22799 519766061 519798829
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22799)) 519798829 519831597 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 519798829 519831597).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22799 519798829 519831597
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 519700525 519766061).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 519700525 ≤ 519733293)
    (by decide : 519733293 ≤ 519766061) block0 block1

theorem join_0_1 : (twinPrimeSegment 519766061 519831597).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 519766061 ≤ 519798829)
    (by decide : 519798829 ≤ 519831597) block2 block3

theorem join_1_0 : (twinPrimeSegment 519700525 519831597).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 519700525 ≤ 519766061)
    (by decide : 519766061 ≤ 519831597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 519700525 519831597).card = 465 := join_1_0

end S247C13
end Sude.GeneratedTwinScan
