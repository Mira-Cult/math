import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22855)) 522321965 522354733 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 522321965 522354733).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22855 522321965 522354733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22855)) 522354733 522387501 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 522354733 522387501).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22855 522354733 522387501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22856)) 522387501 522420269 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 522387501 522420269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22856 522387501 522420269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22857)) 522420269 522453037 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 522420269 522453037).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22857 522420269 522453037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 522321965 522387501).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 522321965 ≤ 522354733)
    (by decide : 522354733 ≤ 522387501) block0 block1

theorem join_0_1 : (twinPrimeSegment 522387501 522453037).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 522387501 ≤ 522420269)
    (by decide : 522420269 ≤ 522453037) block2 block3

theorem join_1_0 : (twinPrimeSegment 522321965 522453037).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 522321965 ≤ 522387501)
    (by decide : 522387501 ≤ 522453037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 522321965 522453037).card = 410 := join_1_0

end S249C01
end Sude.GeneratedTwinScan
