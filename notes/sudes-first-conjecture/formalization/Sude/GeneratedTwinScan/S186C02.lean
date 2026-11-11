import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S186C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19757)) 390332461 390365229 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 390332461 390365229).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19757 390332461 390365229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19758)) 390365229 390397997 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 390365229 390397997).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19758 390365229 390397997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19759)) 390397997 390430765 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 390397997 390430765).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19759 390397997 390430765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19760)) 390430765 390463533 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 390430765 390463533).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19760 390430765 390463533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 390332461 390397997).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 390332461 ≤ 390365229)
    (by decide : 390365229 ≤ 390397997) block0 block1

theorem join_0_1 : (twinPrimeSegment 390397997 390463533).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 390397997 ≤ 390430765)
    (by decide : 390430765 ≤ 390463533) block2 block3

theorem join_1_0 : (twinPrimeSegment 390332461 390463533).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 390332461 ≤ 390397997)
    (by decide : 390397997 ≤ 390463533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 390332461 390463533).card = 434 := join_1_0

end S186C02
end Sude.GeneratedTwinScan
