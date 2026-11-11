import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16444)) 270401581 270434349 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 270401581 270434349).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16444 270401581 270434349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16445)) 270434349 270467117 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 270434349 270467117).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16445 270434349 270467117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16446)) 270467117 270499885 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 270467117 270499885).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16446 270467117 270499885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16447)) 270499885 270532653 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 270499885 270532653).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16447 270499885 270532653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 270401581 270467117).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 270401581 ≤ 270434349)
    (by decide : 270434349 ≤ 270467117) block0 block1

theorem join_0_1 : (twinPrimeSegment 270467117 270532653).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 270467117 ≤ 270499885)
    (by decide : 270499885 ≤ 270532653) block2 block3

theorem join_1_0 : (twinPrimeSegment 270401581 270532653).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 270401581 ≤ 270467117)
    (by decide : 270467117 ≤ 270532653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 270401581 270532653).card = 479 := join_1_0

end S128C15
end Sude.GeneratedTwinScan
