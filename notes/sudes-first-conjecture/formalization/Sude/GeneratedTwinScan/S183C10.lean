import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19624)) 385089581 385122349 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 385089581 385122349).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19624 385089581 385122349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19625)) 385122349 385155117 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 385122349 385155117).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19625 385122349 385155117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19626)) 385155117 385187885 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385155117 385187885).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19626 385155117 385187885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19627)) 385187885 385220653 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385187885 385220653).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19627 385187885 385220653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 385089581 385155117).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 385089581 ≤ 385122349)
    (by decide : 385122349 ≤ 385155117) block0 block1

theorem join_0_1 : (twinPrimeSegment 385155117 385220653).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 385155117 ≤ 385187885)
    (by decide : 385187885 ≤ 385220653) block2 block3

theorem join_1_0 : (twinPrimeSegment 385089581 385220653).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 385089581 ≤ 385155117)
    (by decide : 385155117 ≤ 385220653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 385089581 385220653).card = 454 := join_1_0

end S183C10
end Sude.GeneratedTwinScan
