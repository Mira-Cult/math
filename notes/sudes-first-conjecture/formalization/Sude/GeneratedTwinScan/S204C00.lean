import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20684)) 427819053 427851821 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427819053 427851821).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20684 427819053 427851821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20685)) 427851821 427884589 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427851821 427884589).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20685 427851821 427884589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20686)) 427884589 427917357 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 427884589 427917357).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20686 427884589 427917357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20686)) 427917357 427950125 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 427917357 427950125).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20686 427917357 427950125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427819053 427884589).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 427851821)
    (by decide : 427851821 ≤ 427884589) block0 block1

theorem join_0_1 : (twinPrimeSegment 427884589 427950125).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 427884589 ≤ 427917357)
    (by decide : 427917357 ≤ 427950125) block2 block3

theorem join_1_0 : (twinPrimeSegment 427819053 427950125).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 427884589)
    (by decide : 427884589 ≤ 427950125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427819053 427950125).card = 418 := join_1_0

end S204C00
end Sude.GeneratedTwinScan
