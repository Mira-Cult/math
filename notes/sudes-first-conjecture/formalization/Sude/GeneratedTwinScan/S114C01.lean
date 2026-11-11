import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15467)) 239206445 239239213 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239206445 239239213).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15467 239206445 239239213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15468)) 239239213 239271981 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 239239213 239271981).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15468 239239213 239271981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15469)) 239271981 239304749 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239271981 239304749).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15469 239271981 239304749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15470)) 239304749 239337517 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239304749 239337517).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15470 239304749 239337517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239206445 239271981).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 239206445 ≤ 239239213)
    (by decide : 239239213 ≤ 239271981) block0 block1

theorem join_0_1 : (twinPrimeSegment 239271981 239337517).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 239271981 ≤ 239304749)
    (by decide : 239304749 ≤ 239337517) block2 block3

theorem join_1_0 : (twinPrimeSegment 239206445 239337517).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 239206445 ≤ 239271981)
    (by decide : 239271981 ≤ 239337517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239206445 239337517).card = 451 := join_1_0

end S114C01
end Sude.GeneratedTwinScan
