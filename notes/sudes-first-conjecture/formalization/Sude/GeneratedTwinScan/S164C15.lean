import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18599)) 345899053 345931821 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 345899053 345931821).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18599 345899053 345931821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18600)) 345931821 345964589 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345931821 345964589).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18600 345931821 345964589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18601)) 345964589 345997357 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345964589 345997357).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18601 345964589 345997357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18601)) 345997357 346030125 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345997357 346030125).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18601 345997357 346030125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 345899053 345964589).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 345899053 ≤ 345931821)
    (by decide : 345931821 ≤ 345964589) block0 block1

theorem join_0_1 : (twinPrimeSegment 345964589 346030125).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 345964589 ≤ 345997357)
    (by decide : 345997357 ≤ 346030125) block2 block3

theorem join_1_0 : (twinPrimeSegment 345899053 346030125).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 345899053 ≤ 345964589)
    (by decide : 345964589 ≤ 346030125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 345899053 346030125).card = 466 := join_1_0

end S164C15
end Sude.GeneratedTwinScan
