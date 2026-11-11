import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17510)) 306577453 306610221 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306577453 306610221).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17510 306577453 306610221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17511)) 306610221 306642989 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 306610221 306642989).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17511 306610221 306642989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17512)) 306642989 306675757 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 306642989 306675757).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17512 306642989 306675757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17513)) 306675757 306708525 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 306675757 306708525).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17513 306675757 306708525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306577453 306642989).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 306577453 ≤ 306610221)
    (by decide : 306610221 ≤ 306642989) block0 block1

theorem join_0_1 : (twinPrimeSegment 306642989 306708525).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 306642989 ≤ 306675757)
    (by decide : 306675757 ≤ 306708525) block2 block3

theorem join_1_0 : (twinPrimeSegment 306577453 306708525).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 306577453 ≤ 306642989)
    (by decide : 306642989 ≤ 306708525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306577453 306708525).card = 454 := join_1_0

end S146C03
end Sude.GeneratedTwinScan
