import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20592)) 424017965 424050733 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 424017965 424050733).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20592 424017965 424050733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20593)) 424050733 424083501 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 424050733 424083501).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20593 424050733 424083501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20594)) 424083501 424116269 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 424083501 424116269).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20594 424083501 424116269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20594)) 424116269 424149037 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 424116269 424149037).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20594 424116269 424149037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 424017965 424083501).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 424017965 ≤ 424050733)
    (by decide : 424050733 ≤ 424083501) block0 block1

theorem join_0_1 : (twinPrimeSegment 424083501 424149037).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 424083501 ≤ 424116269)
    (by decide : 424116269 ≤ 424149037) block2 block3

theorem join_1_0 : (twinPrimeSegment 424017965 424149037).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 424017965 ≤ 424083501)
    (by decide : 424083501 ≤ 424149037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 424017965 424149037).card = 441 := join_1_0

end S202C03
end Sude.GeneratedTwinScan
