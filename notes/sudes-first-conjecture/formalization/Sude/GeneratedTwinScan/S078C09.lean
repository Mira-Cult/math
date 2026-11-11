import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12837)) 164757549 164790317 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 164757549 164790317).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12837 164757549 164790317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12838)) 164790317 164823085 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 164790317 164823085).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12838 164790317 164823085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12839)) 164823085 164855853 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 164823085 164855853).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12839 164823085 164855853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12840)) 164855853 164888621 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 164855853 164888621).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12840 164855853 164888621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 164757549 164823085).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 164757549 ≤ 164790317)
    (by decide : 164790317 ≤ 164823085) block0 block1

theorem join_0_1 : (twinPrimeSegment 164823085 164888621).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 164823085 ≤ 164855853)
    (by decide : 164855853 ≤ 164888621) block2 block3

theorem join_1_0 : (twinPrimeSegment 164757549 164888621).card = 496 := by
  simpa using combineTwinPrimeSegments (by decide : 164757549 ≤ 164823085)
    (by decide : 164823085 ≤ 164888621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 164757549 164888621).card = 496 := join_1_0

end S078C09
end Sude.GeneratedTwinScan
