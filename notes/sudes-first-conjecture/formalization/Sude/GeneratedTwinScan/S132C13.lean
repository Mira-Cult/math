import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16690)) 278528045 278560813 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278528045 278560813).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16690 278528045 278560813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16691)) 278560813 278593581 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278560813 278593581).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16691 278560813 278593581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16692)) 278593581 278626349 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278593581 278626349).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16692 278593581 278626349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16693)) 278626349 278659117 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 278626349 278659117).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16693 278626349 278659117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278528045 278593581).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 278528045 ≤ 278560813)
    (by decide : 278560813 ≤ 278593581) block0 block1

theorem join_0_1 : (twinPrimeSegment 278593581 278659117).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 278593581 ≤ 278626349)
    (by decide : 278626349 ≤ 278659117) block2 block3

theorem join_1_0 : (twinPrimeSegment 278528045 278659117).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 278528045 ≤ 278593581)
    (by decide : 278593581 ≤ 278659117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278528045 278659117).card = 416 := join_1_0

end S132C13
end Sude.GeneratedTwinScan
