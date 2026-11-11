import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22040)) 485752877 485785645 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 485752877 485785645).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22040 485752877 485785645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22041)) 485785645 485818413 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 485785645 485818413).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22041 485785645 485818413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22042)) 485818413 485851181 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485818413 485851181).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22042 485818413 485851181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22042)) 485851181 485883949 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485851181 485883949).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22042 485851181 485883949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 485752877 485818413).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 485752877 ≤ 485785645)
    (by decide : 485785645 ≤ 485818413) block0 block1

theorem join_0_1 : (twinPrimeSegment 485818413 485883949).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 485818413 ≤ 485851181)
    (by decide : 485851181 ≤ 485883949) block2 block3

theorem join_1_0 : (twinPrimeSegment 485752877 485883949).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 485752877 ≤ 485818413)
    (by decide : 485818413 ≤ 485883949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 485752877 485883949).card = 416 := join_1_0

end S231C10
end Sude.GeneratedTwinScan
