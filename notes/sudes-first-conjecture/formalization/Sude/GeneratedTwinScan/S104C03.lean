import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14782)) 218497069 218529837 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 218497069 218529837).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14782 218497069 218529837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14783)) 218529837 218562605 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 218529837 218562605).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14783 218529837 218562605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14784)) 218562605 218595373 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 218562605 218595373).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14784 218562605 218595373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14786)) 218595373 218628141 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 218595373 218628141).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14786 218595373 218628141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 218497069 218562605).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 218497069 ≤ 218529837)
    (by decide : 218529837 ≤ 218562605) block0 block1

theorem join_0_1 : (twinPrimeSegment 218562605 218628141).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 218562605 ≤ 218595373)
    (by decide : 218595373 ≤ 218628141) block2 block3

theorem join_1_0 : (twinPrimeSegment 218497069 218628141).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 218497069 ≤ 218562605)
    (by decide : 218562605 ≤ 218628141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 218497069 218628141).card = 440 := join_1_0

end S104C03
end Sude.GeneratedTwinScan
