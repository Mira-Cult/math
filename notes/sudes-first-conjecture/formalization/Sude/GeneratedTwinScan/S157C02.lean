import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18153)) 329515053 329547821 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 329515053 329547821).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18153 329515053 329547821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18154)) 329547821 329580589 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329547821 329580589).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18154 329547821 329580589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18155)) 329580589 329613357 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329580589 329613357).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18155 329580589 329613357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18156)) 329613357 329646125 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 329613357 329646125).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18156 329613357 329646125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 329515053 329580589).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 329515053 ≤ 329547821)
    (by decide : 329547821 ≤ 329580589) block0 block1

theorem join_0_1 : (twinPrimeSegment 329580589 329646125).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 329580589 ≤ 329613357)
    (by decide : 329613357 ≤ 329646125) block2 block3

theorem join_1_0 : (twinPrimeSegment 329515053 329646125).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 329515053 ≤ 329580589)
    (by decide : 329580589 ≤ 329646125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 329515053 329646125).card = 444 := join_1_0

end S157C02
end Sude.GeneratedTwinScan
