import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17714)) 313786413 313819181 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 313786413 313819181).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17714 313786413 313819181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17715)) 313819181 313851949 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 313819181 313851949).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17715 313819181 313851949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17716)) 313851949 313884717 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 313851949 313884717).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17716 313851949 313884717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17717)) 313884717 313917485 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 313884717 313917485).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17717 313884717 313917485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 313786413 313851949).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 313786413 ≤ 313819181)
    (by decide : 313819181 ≤ 313851949) block0 block1

theorem join_0_1 : (twinPrimeSegment 313851949 313917485).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 313851949 ≤ 313884717)
    (by decide : 313884717 ≤ 313917485) block2 block3

theorem join_1_0 : (twinPrimeSegment 313786413 313917485).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 313786413 ≤ 313851949)
    (by decide : 313851949 ≤ 313917485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 313786413 313917485).card = 439 := join_1_0

end S149C10
end Sude.GeneratedTwinScan
