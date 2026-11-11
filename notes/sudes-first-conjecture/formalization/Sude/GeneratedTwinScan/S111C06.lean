import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15284)) 233570349 233603117 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 233570349 233603117).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15284 233570349 233603117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15285)) 233603117 233635885 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 233603117 233635885).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15285 233603117 233635885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15286)) 233635885 233668653 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 233635885 233668653).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15286 233635885 233668653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15287)) 233668653 233701421 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 233668653 233701421).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15287 233668653 233701421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 233570349 233635885).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 233570349 ≤ 233603117)
    (by decide : 233603117 ≤ 233635885) block0 block1

theorem join_0_1 : (twinPrimeSegment 233635885 233701421).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 233635885 ≤ 233668653)
    (by decide : 233668653 ≤ 233701421) block2 block3

theorem join_1_0 : (twinPrimeSegment 233570349 233701421).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 233570349 ≤ 233635885)
    (by decide : 233635885 ≤ 233701421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 233570349 233701421).card = 486 := join_1_0

end S111C06
end Sude.GeneratedTwinScan
