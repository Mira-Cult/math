import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S196C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20307)) 412352557 412385325 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 412352557 412385325).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20307 412352557 412385325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20308)) 412385325 412418093 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 412385325 412418093).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20308 412385325 412418093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20308)) 412418093 412450861 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 412418093 412450861).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20308 412418093 412450861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20309)) 412450861 412483629 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 412450861 412483629).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20309 412450861 412483629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 412352557 412418093).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 412352557 ≤ 412385325)
    (by decide : 412385325 ≤ 412418093) block0 block1

theorem join_0_1 : (twinPrimeSegment 412418093 412483629).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 412418093 ≤ 412450861)
    (by decide : 412450861 ≤ 412483629) block2 block3

theorem join_1_0 : (twinPrimeSegment 412352557 412483629).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 412352557 ≤ 412418093)
    (by decide : 412418093 ≤ 412483629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 412352557 412483629).card = 443 := join_1_0

end S196C10
end Sude.GeneratedTwinScan
