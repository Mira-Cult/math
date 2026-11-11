import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18225)) 332136493 332169261 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332136493 332169261).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18225 332136493 332169261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18226)) 332169261 332202029 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332169261 332202029).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18226 332169261 332202029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18227)) 332202029 332234797 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332202029 332234797).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18227 332202029 332234797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18228)) 332234797 332267565 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 332234797 332267565).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18228 332234797 332267565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332136493 332202029).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 332136493 ≤ 332169261)
    (by decide : 332169261 ≤ 332202029) block0 block1

theorem join_0_1 : (twinPrimeSegment 332202029 332267565).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 332202029 ≤ 332234797)
    (by decide : 332234797 ≤ 332267565) block2 block3

theorem join_1_0 : (twinPrimeSegment 332136493 332267565).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 332136493 ≤ 332202029)
    (by decide : 332202029 ≤ 332267565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332136493 332267565).card = 438 := join_1_0

end S158C06
end Sude.GeneratedTwinScan
