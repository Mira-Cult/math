import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14194)) 201457709 201490477 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 201457709 201490477).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14194 201457709 201490477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14195)) 201490477 201523245 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 201490477 201523245).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14195 201490477 201523245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14197)) 201523245 201556013 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 201523245 201556013).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14197 201523245 201556013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14198)) 201556013 201588781 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 201556013 201588781).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14198 201556013 201588781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 201457709 201523245).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 201457709 ≤ 201490477)
    (by decide : 201490477 ≤ 201523245) block0 block1

theorem join_0_1 : (twinPrimeSegment 201523245 201588781).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 201523245 ≤ 201556013)
    (by decide : 201556013 ≤ 201588781) block2 block3

theorem join_1_0 : (twinPrimeSegment 201457709 201588781).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 201457709 ≤ 201523245)
    (by decide : 201523245 ≤ 201588781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 201457709 201588781).card = 442 := join_1_0

end S096C01
end Sude.GeneratedTwinScan
