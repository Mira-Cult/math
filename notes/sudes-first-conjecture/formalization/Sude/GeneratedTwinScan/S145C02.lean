import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17446)) 304349229 304381997 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 304349229 304381997).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17446 304349229 304381997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17447)) 304381997 304414765 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 304381997 304414765).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17447 304381997 304414765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17448)) 304414765 304447533 = 91 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 304414765 304447533).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17448 304414765 304447533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17449)) 304447533 304480301 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 304447533 304480301).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17449 304447533 304480301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 304349229 304414765).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 304349229 ≤ 304381997)
    (by decide : 304381997 ≤ 304414765) block0 block1

theorem join_0_1 : (twinPrimeSegment 304414765 304480301).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 304414765 ≤ 304447533)
    (by decide : 304447533 ≤ 304480301) block2 block3

theorem join_1_0 : (twinPrimeSegment 304349229 304480301).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 304349229 ≤ 304414765)
    (by decide : 304414765 ≤ 304480301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 304349229 304480301).card = 441 := join_1_0

end S145C02
end Sude.GeneratedTwinScan
