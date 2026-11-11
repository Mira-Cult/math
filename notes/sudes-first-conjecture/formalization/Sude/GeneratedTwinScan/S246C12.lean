import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22748)) 517472301 517505069 = 84 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 517472301 517505069).card = 84 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22748 517472301 517505069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22749)) 517505069 517537837 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 517505069 517537837).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22749 517505069 517537837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22750)) 517537837 517570605 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 517537837 517570605).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22750 517537837 517570605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22750)) 517570605 517603373 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 517570605 517603373).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22750 517570605 517603373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 517472301 517537837).card = 182 := by
  simpa using combineTwinPrimeSegments (by decide : 517472301 ≤ 517505069)
    (by decide : 517505069 ≤ 517537837) block0 block1

theorem join_0_1 : (twinPrimeSegment 517537837 517603373).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 517537837 ≤ 517570605)
    (by decide : 517570605 ≤ 517603373) block2 block3

theorem join_1_0 : (twinPrimeSegment 517472301 517603373).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 517472301 ≤ 517537837)
    (by decide : 517537837 ≤ 517603373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 517472301 517603373).card = 413 := join_1_0

end S246C12
end Sude.GeneratedTwinScan
