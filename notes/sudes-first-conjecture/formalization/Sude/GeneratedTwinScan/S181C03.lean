import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19493)) 379977773 380010541 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 379977773 380010541).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19493 379977773 380010541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19494)) 380010541 380043309 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 380010541 380043309).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19494 380010541 380043309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19495)) 380043309 380076077 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 380043309 380076077).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19495 380043309 380076077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19496)) 380076077 380108845 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 380076077 380108845).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19496 380076077 380108845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 379977773 380043309).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 379977773 ≤ 380010541)
    (by decide : 380010541 ≤ 380043309) block0 block1

theorem join_0_1 : (twinPrimeSegment 380043309 380108845).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 380043309 ≤ 380076077)
    (by decide : 380076077 ≤ 380108845) block2 block3

theorem join_1_0 : (twinPrimeSegment 379977773 380108845).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 379977773 ≤ 380043309)
    (by decide : 380043309 ≤ 380108845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 379977773 380108845).card = 444 := join_1_0

end S181C03
end Sude.GeneratedTwinScan
