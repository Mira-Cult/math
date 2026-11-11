import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16110)) 259522605 259555373 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 259522605 259555373).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16110 259522605 259555373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16111)) 259555373 259588141 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 259555373 259588141).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16111 259555373 259588141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16112)) 259588141 259620909 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 259588141 259620909).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16112 259588141 259620909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16113)) 259620909 259653677 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 259620909 259653677).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16113 259620909 259653677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 259522605 259588141).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 259522605 ≤ 259555373)
    (by decide : 259555373 ≤ 259588141) block0 block1

theorem join_0_1 : (twinPrimeSegment 259588141 259653677).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 259588141 ≤ 259620909)
    (by decide : 259620909 ≤ 259653677) block2 block3

theorem join_1_0 : (twinPrimeSegment 259522605 259653677).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 259522605 ≤ 259588141)
    (by decide : 259588141 ≤ 259653677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 259522605 259653677).card = 451 := join_1_0

end S123C12
end Sude.GeneratedTwinScan
