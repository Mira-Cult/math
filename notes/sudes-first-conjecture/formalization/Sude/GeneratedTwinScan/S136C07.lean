import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16916)) 286130221 286162989 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 286130221 286162989).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16916 286130221 286162989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16917)) 286162989 286195757 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286162989 286195757).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16917 286162989 286195757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16918)) 286195757 286228525 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286195757 286228525).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16918 286195757 286228525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16919)) 286228525 286261293 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 286228525 286261293).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16919 286228525 286261293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 286130221 286195757).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 286130221 ≤ 286162989)
    (by decide : 286162989 ≤ 286195757) block0 block1

theorem join_0_1 : (twinPrimeSegment 286195757 286261293).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 286195757 ≤ 286228525)
    (by decide : 286228525 ≤ 286261293) block2 block3

theorem join_1_0 : (twinPrimeSegment 286130221 286261293).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 286130221 ≤ 286195757)
    (by decide : 286195757 ≤ 286261293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 286130221 286261293).card = 466 := join_1_0

end S136C07
end Sude.GeneratedTwinScan
