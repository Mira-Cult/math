import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16745)) 280363053 280395821 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 280363053 280395821).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16745 280363053 280395821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16746)) 280395821 280428589 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280395821 280428589).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16746 280395821 280428589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16746)) 280428589 280461357 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280428589 280461357).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16746 280428589 280461357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16747)) 280461357 280494125 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280461357 280494125).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16747 280461357 280494125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 280363053 280428589).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 280363053 ≤ 280395821)
    (by decide : 280395821 ≤ 280428589) block0 block1

theorem join_0_1 : (twinPrimeSegment 280428589 280494125).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 280428589 ≤ 280461357)
    (by decide : 280461357 ≤ 280494125) block2 block3

theorem join_1_0 : (twinPrimeSegment 280363053 280494125).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 280363053 ≤ 280428589)
    (by decide : 280428589 ≤ 280494125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 280363053 280494125).card = 456 := join_1_0

end S133C11
end Sude.GeneratedTwinScan
