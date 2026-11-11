import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13059)) 170524717 170557485 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 170524717 170557485).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13059 170524717 170557485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13061)) 170557485 170590253 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 170557485 170590253).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13061 170557485 170590253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13062)) 170590253 170623021 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 170590253 170623021).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13062 170590253 170623021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13063)) 170623021 170655789 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 170623021 170655789).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13063 170623021 170655789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 170524717 170590253).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 170524717 ≤ 170557485)
    (by decide : 170557485 ≤ 170590253) block0 block1

theorem join_0_1 : (twinPrimeSegment 170590253 170655789).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 170590253 ≤ 170623021)
    (by decide : 170623021 ≤ 170655789) block2 block3

theorem join_1_0 : (twinPrimeSegment 170524717 170655789).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 170524717 ≤ 170590253)
    (by decide : 170590253 ≤ 170655789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 170524717 170655789).card = 455 := join_1_0

end S081C05
end Sude.GeneratedTwinScan
