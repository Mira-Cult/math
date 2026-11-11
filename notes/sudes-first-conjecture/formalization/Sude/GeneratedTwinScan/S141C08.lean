import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17227)) 296747053 296779821 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 296747053 296779821).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17227 296747053 296779821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17228)) 296779821 296812589 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 296779821 296812589).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17228 296779821 296812589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17229)) 296812589 296845357 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296812589 296845357).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17229 296812589 296845357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17230)) 296845357 296878125 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296845357 296878125).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17230 296845357 296878125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 296747053 296812589).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 296747053 ≤ 296779821)
    (by decide : 296779821 ≤ 296812589) block0 block1

theorem join_0_1 : (twinPrimeSegment 296812589 296878125).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 296812589 ≤ 296845357)
    (by decide : 296845357 ≤ 296878125) block2 block3

theorem join_1_0 : (twinPrimeSegment 296747053 296878125).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 296747053 ≤ 296812589)
    (by decide : 296812589 ≤ 296878125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 296747053 296878125).card = 461 := join_1_0

end S141C08
end Sude.GeneratedTwinScan
