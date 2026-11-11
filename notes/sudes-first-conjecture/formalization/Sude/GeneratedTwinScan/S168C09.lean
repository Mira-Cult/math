import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18802)) 353501229 353533997 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 353501229 353533997).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18802 353501229 353533997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18803)) 353533997 353566765 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353533997 353566765).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18803 353533997 353566765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18804)) 353566765 353599533 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353566765 353599533).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18804 353566765 353599533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18805)) 353599533 353632301 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353599533 353632301).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18805 353599533 353632301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 353501229 353566765).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 353501229 ≤ 353533997)
    (by decide : 353533997 ≤ 353566765) block0 block1

theorem join_0_1 : (twinPrimeSegment 353566765 353632301).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 353566765 ≤ 353599533)
    (by decide : 353599533 ≤ 353632301) block2 block3

theorem join_1_0 : (twinPrimeSegment 353501229 353632301).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 353501229 ≤ 353566765)
    (by decide : 353566765 ≤ 353632301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 353501229 353632301).card = 446 := join_1_0

end S168C09
end Sude.GeneratedTwinScan
