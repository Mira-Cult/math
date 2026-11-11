import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19691)) 387711021 387743789 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 387711021 387743789).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19691 387711021 387743789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19692)) 387743789 387776557 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 387743789 387776557).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19692 387743789 387776557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19692)) 387776557 387809325 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 387776557 387809325).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19692 387776557 387809325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19693)) 387809325 387842093 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 387809325 387842093).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19693 387809325 387842093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 387711021 387776557).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 387711021 ≤ 387743789)
    (by decide : 387743789 ≤ 387776557) block0 block1

theorem join_0_1 : (twinPrimeSegment 387776557 387842093).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 387776557 ≤ 387809325)
    (by decide : 387809325 ≤ 387842093) block2 block3

theorem join_1_0 : (twinPrimeSegment 387711021 387842093).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 387711021 ≤ 387776557)
    (by decide : 387776557 ≤ 387842093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 387711021 387842093).card = 460 := join_1_0

end S184C14
end Sude.GeneratedTwinScan
