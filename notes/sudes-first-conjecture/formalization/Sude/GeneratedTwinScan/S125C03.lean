import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16204)) 262537261 262570029 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 262537261 262570029).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16204 262537261 262570029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16205)) 262570029 262602797 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 262570029 262602797).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16205 262570029 262602797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16206)) 262602797 262635565 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 262602797 262635565).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16206 262602797 262635565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16207)) 262635565 262668333 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 262635565 262668333).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16207 262635565 262668333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 262537261 262602797).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 262537261 ≤ 262570029)
    (by decide : 262570029 ≤ 262602797) block0 block1

theorem join_0_1 : (twinPrimeSegment 262602797 262668333).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 262602797 ≤ 262635565)
    (by decide : 262635565 ≤ 262668333) block2 block3

theorem join_1_0 : (twinPrimeSegment 262537261 262668333).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 262537261 ≤ 262602797)
    (by decide : 262602797 ≤ 262668333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 262537261 262668333).card = 455 := join_1_0

end S125C03
end Sude.GeneratedTwinScan
