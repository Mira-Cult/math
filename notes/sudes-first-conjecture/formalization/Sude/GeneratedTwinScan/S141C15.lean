import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17253)) 297664557 297697325 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297664557 297697325).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17253 297664557 297697325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17254)) 297697325 297730093 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297697325 297730093).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17254 297697325 297730093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17255)) 297730093 297762861 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297730093 297762861).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17255 297730093 297762861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17256)) 297762861 297795629 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 297762861 297795629).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17256 297762861 297795629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297664557 297730093).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 297664557 ≤ 297697325)
    (by decide : 297697325 ≤ 297730093) block0 block1

theorem join_0_1 : (twinPrimeSegment 297730093 297795629).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 297730093 ≤ 297762861)
    (by decide : 297762861 ≤ 297795629) block2 block3

theorem join_1_0 : (twinPrimeSegment 297664557 297795629).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 297664557 ≤ 297730093)
    (by decide : 297730093 ≤ 297795629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297664557 297795629).card = 471 := join_1_0

end S141C15
end Sude.GeneratedTwinScan
