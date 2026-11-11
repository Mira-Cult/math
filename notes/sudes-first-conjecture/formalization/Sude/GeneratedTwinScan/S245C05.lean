import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22682)) 514457645 514490413 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514457645 514490413).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22682 514457645 514490413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22683)) 514490413 514523181 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 514490413 514523181).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22683 514490413 514523181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22683)) 514523181 514555949 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 514523181 514555949).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22683 514523181 514555949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22684)) 514555949 514588717 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514555949 514588717).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22684 514555949 514588717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514457645 514523181).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 514457645 ≤ 514490413)
    (by decide : 514490413 ≤ 514523181) block0 block1

theorem join_0_1 : (twinPrimeSegment 514523181 514588717).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 514523181 ≤ 514555949)
    (by decide : 514555949 ≤ 514588717) block2 block3

theorem join_1_0 : (twinPrimeSegment 514457645 514588717).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 514457645 ≤ 514523181)
    (by decide : 514523181 ≤ 514588717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514457645 514588717).card = 416 := join_1_0

end S245C05
end Sude.GeneratedTwinScan
