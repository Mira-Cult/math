import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13624)) 185597997 185630765 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 185597997 185630765).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13624 185597997 185630765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13625)) 185630765 185663533 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 185630765 185663533).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13625 185630765 185663533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13627)) 185663533 185696301 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 185663533 185696301).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13627 185663533 185696301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13628)) 185696301 185729069 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 185696301 185729069).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13628 185696301 185729069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 185597997 185663533).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 185597997 ≤ 185630765)
    (by decide : 185630765 ≤ 185663533) block0 block1

theorem join_0_1 : (twinPrimeSegment 185663533 185729069).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 185663533 ≤ 185696301)
    (by decide : 185696301 ≤ 185729069) block2 block3

theorem join_1_0 : (twinPrimeSegment 185597997 185729069).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 185597997 ≤ 185663533)
    (by decide : 185663533 ≤ 185729069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 185597997 185729069).card = 460 := join_1_0

end S088C08
end Sude.GeneratedTwinScan
