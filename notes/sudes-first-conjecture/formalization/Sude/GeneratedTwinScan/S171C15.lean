import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18989)) 360579117 360611885 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360579117 360611885).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18989 360579117 360611885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18990)) 360611885 360644653 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 360611885 360644653).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18990 360611885 360644653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18991)) 360644653 360677421 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 360644653 360677421).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18991 360644653 360677421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18992)) 360677421 360710189 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360677421 360710189).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18992 360677421 360710189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360579117 360644653).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 360579117 ≤ 360611885)
    (by decide : 360611885 ≤ 360644653) block0 block1

theorem join_0_1 : (twinPrimeSegment 360644653 360710189).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 360644653 ≤ 360677421)
    (by decide : 360677421 ≤ 360710189) block2 block3

theorem join_1_0 : (twinPrimeSegment 360579117 360710189).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 360579117 ≤ 360644653)
    (by decide : 360644653 ≤ 360710189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360579117 360710189).card = 427 := join_1_0

end S171C15
end Sude.GeneratedTwinScan
