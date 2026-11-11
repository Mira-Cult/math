import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12938)) 167378989 167411757 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 167378989 167411757).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12938 167378989 167411757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12940)) 167411757 167444525 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167411757 167444525).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12940 167411757 167444525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12941)) 167444525 167477293 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167444525 167477293).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12941 167444525 167477293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12942)) 167477293 167510061 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 167477293 167510061).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12942 167477293 167510061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 167378989 167444525).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 167378989 ≤ 167411757)
    (by decide : 167411757 ≤ 167444525) block0 block1

theorem join_0_1 : (twinPrimeSegment 167444525 167510061).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 167444525 ≤ 167477293)
    (by decide : 167477293 ≤ 167510061) block2 block3

theorem join_1_0 : (twinPrimeSegment 167378989 167510061).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 167378989 ≤ 167444525)
    (by decide : 167444525 ≤ 167510061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 167378989 167510061).card = 507 := join_1_0

end S079C13
end Sude.GeneratedTwinScan
