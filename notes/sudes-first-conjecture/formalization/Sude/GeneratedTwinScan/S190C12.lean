import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20001)) 400031789 400064557 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 400031789 400064557).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20001 400031789 400064557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20002)) 400064557 400097325 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 400064557 400097325).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20002 400064557 400097325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20003)) 400097325 400130093 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 400097325 400130093).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20003 400097325 400130093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20004)) 400130093 400162861 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 400130093 400162861).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20004 400130093 400162861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 400031789 400097325).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 400031789 ≤ 400064557)
    (by decide : 400064557 ≤ 400097325) block0 block1

theorem join_0_1 : (twinPrimeSegment 400097325 400162861).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 400097325 ≤ 400130093)
    (by decide : 400130093 ≤ 400162861) block2 block3

theorem join_1_0 : (twinPrimeSegment 400031789 400162861).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 400031789 ≤ 400097325)
    (by decide : 400097325 ≤ 400162861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 400031789 400162861).card = 441 := join_1_0

end S190C12
end Sude.GeneratedTwinScan
