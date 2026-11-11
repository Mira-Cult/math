import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13829)) 191234093 191266861 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 191234093 191266861).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13829 191234093 191266861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13831)) 191266861 191299629 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191266861 191299629).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13831 191266861 191299629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13832)) 191299629 191332397 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191299629 191332397).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13832 191299629 191332397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13833)) 191332397 191365165 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191332397 191365165).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13833 191332397 191365165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 191234093 191299629).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 191234093 ≤ 191266861)
    (by decide : 191266861 ≤ 191299629) block0 block1

theorem join_0_1 : (twinPrimeSegment 191299629 191365165).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 191299629 ≤ 191332397)
    (by decide : 191332397 ≤ 191365165) block2 block3

theorem join_1_0 : (twinPrimeSegment 191234093 191365165).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 191234093 ≤ 191299629)
    (by decide : 191299629 ≤ 191365165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 191234093 191365165).card = 472 := join_1_0

end S091C03
end Sude.GeneratedTwinScan
