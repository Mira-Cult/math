import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12749)) 162529325 162562093 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162529325 162562093).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12749 162529325 162562093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12751)) 162562093 162594861 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162562093 162594861).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12751 162562093 162594861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12752)) 162594861 162627629 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162594861 162627629).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12752 162594861 162627629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12753)) 162627629 162660397 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 162627629 162660397).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12753 162627629 162660397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162529325 162594861).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 162529325 ≤ 162562093)
    (by decide : 162562093 ≤ 162594861) block0 block1

theorem join_0_1 : (twinPrimeSegment 162594861 162660397).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 162594861 ≤ 162627629)
    (by decide : 162627629 ≤ 162660397) block2 block3

theorem join_1_0 : (twinPrimeSegment 162529325 162660397).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 162529325 ≤ 162594861)
    (by decide : 162594861 ≤ 162660397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162529325 162660397).card = 482 := join_1_0

end S077C08
end Sude.GeneratedTwinScan
