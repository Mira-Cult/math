import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18778)) 352583725 352616493 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352583725 352616493).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18778 352583725 352616493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18778)) 352616493 352649261 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 352616493 352649261).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18778 352616493 352649261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18779)) 352649261 352682029 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 352649261 352682029).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18779 352649261 352682029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18780)) 352682029 352714797 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352682029 352714797).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18780 352682029 352714797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352583725 352649261).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 352583725 ≤ 352616493)
    (by decide : 352616493 ≤ 352649261) block0 block1

theorem join_0_1 : (twinPrimeSegment 352649261 352714797).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 352649261 ≤ 352682029)
    (by decide : 352682029 ≤ 352714797) block2 block3

theorem join_1_0 : (twinPrimeSegment 352583725 352714797).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 352583725 ≤ 352649261)
    (by decide : 352649261 ≤ 352714797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352583725 352714797).card = 414 := join_1_0

end S168C02
end Sude.GeneratedTwinScan
