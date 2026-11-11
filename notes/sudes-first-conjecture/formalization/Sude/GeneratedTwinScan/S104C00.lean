import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14769)) 218103853 218136621 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 218103853 218136621).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14769 218103853 218136621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14770)) 218136621 218169389 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 218136621 218169389).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14770 218136621 218169389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14771)) 218169389 218202157 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 218169389 218202157).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14771 218169389 218202157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14772)) 218202157 218234925 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 218202157 218234925).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14772 218202157 218234925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 218103853 218169389).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 218136621)
    (by decide : 218136621 ≤ 218169389) block0 block1

theorem join_0_1 : (twinPrimeSegment 218169389 218234925).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 218169389 ≤ 218202157)
    (by decide : 218202157 ≤ 218234925) block2 block3

theorem join_1_0 : (twinPrimeSegment 218103853 218234925).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 218169389)
    (by decide : 218169389 ≤ 218234925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 218103853 218234925).card = 451 := join_1_0

end S104C00
end Sude.GeneratedTwinScan
