import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16631)) 276561965 276594733 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 276561965 276594733).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16631 276561965 276594733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16632)) 276594733 276627501 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 276594733 276627501).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16632 276594733 276627501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16633)) 276627501 276660269 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 276627501 276660269).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16633 276627501 276660269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16634)) 276660269 276693037 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 276660269 276693037).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16634 276660269 276693037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 276561965 276627501).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 276561965 ≤ 276594733)
    (by decide : 276594733 ≤ 276627501) block0 block1

theorem join_0_1 : (twinPrimeSegment 276627501 276693037).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 276627501 ≤ 276660269)
    (by decide : 276660269 ≤ 276693037) block2 block3

theorem join_1_0 : (twinPrimeSegment 276561965 276693037).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 276561965 ≤ 276627501)
    (by decide : 276627501 ≤ 276693037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 276561965 276693037).card = 461 := join_1_0

end S131C14
end Sude.GeneratedTwinScan
