import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21422)) 458883117 458915885 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 458883117 458915885).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21422 458883117 458915885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21423)) 458915885 458948653 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 458915885 458948653).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21423 458915885 458948653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21423)) 458948653 458981421 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458948653 458981421).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21423 458948653 458981421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21424)) 458981421 459014189 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 458981421 459014189).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21424 458981421 459014189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 458883117 458948653).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 458883117 ≤ 458915885)
    (by decide : 458915885 ≤ 458948653) block0 block1

theorem join_0_1 : (twinPrimeSegment 458948653 459014189).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 458948653 ≤ 458981421)
    (by decide : 458981421 ≤ 459014189) block2 block3

theorem join_1_0 : (twinPrimeSegment 458883117 459014189).card = 407 := by
  simpa using combineTwinPrimeSegments (by decide : 458883117 ≤ 458948653)
    (by decide : 458948653 ≤ 459014189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 458883117 459014189).card = 407 := join_1_0

end S218C13
end Sude.GeneratedTwinScan
