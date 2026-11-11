import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22212)) 493355053 493387821 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 493355053 493387821).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22212 493355053 493387821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22213)) 493387821 493420589 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 493387821 493420589).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22213 493387821 493420589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22213)) 493420589 493453357 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493420589 493453357).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22213 493420589 493453357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22214)) 493453357 493486125 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493453357 493486125).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22214 493453357 493486125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 493355053 493420589).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 493355053 ≤ 493387821)
    (by decide : 493387821 ≤ 493420589) block0 block1

theorem join_0_1 : (twinPrimeSegment 493420589 493486125).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 493420589 ≤ 493453357)
    (by decide : 493453357 ≤ 493486125) block2 block3

theorem join_1_0 : (twinPrimeSegment 493355053 493486125).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 493355053 ≤ 493420589)
    (by decide : 493420589 ≤ 493486125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 493355053 493486125).card = 414 := join_1_0

end S235C04
end Sude.GeneratedTwinScan
