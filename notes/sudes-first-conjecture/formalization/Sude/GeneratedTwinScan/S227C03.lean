import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21828)) 476446765 476479533 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 476446765 476479533).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21828 476446765 476479533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21829)) 476479533 476512301 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 476479533 476512301).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21829 476479533 476512301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21829)) 476512301 476545069 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 476512301 476545069).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21829 476512301 476545069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21830)) 476545069 476577837 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 476545069 476577837).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21830 476545069 476577837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 476446765 476512301).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 476446765 ≤ 476479533)
    (by decide : 476479533 ≤ 476512301) block0 block1

theorem join_0_1 : (twinPrimeSegment 476512301 476577837).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 476512301 ≤ 476545069)
    (by decide : 476545069 ≤ 476577837) block2 block3

theorem join_1_0 : (twinPrimeSegment 476446765 476577837).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 476446765 ≤ 476512301)
    (by decide : 476512301 ≤ 476577837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 476446765 476577837).card = 444 := join_1_0

end S227C03
end Sude.GeneratedTwinScan
