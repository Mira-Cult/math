import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15463)) 239075373 239108141 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239075373 239108141).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15463 239075373 239108141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15464)) 239108141 239140909 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 239108141 239140909).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15464 239108141 239140909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15465)) 239140909 239173677 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239140909 239173677).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15465 239140909 239173677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15466)) 239173677 239206445 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239173677 239206445).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15466 239173677 239206445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239075373 239140909).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 239075373 ≤ 239108141)
    (by decide : 239108141 ≤ 239140909) block0 block1

theorem join_0_1 : (twinPrimeSegment 239140909 239206445).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 239140909 ≤ 239173677)
    (by decide : 239173677 ≤ 239206445) block2 block3

theorem join_1_0 : (twinPrimeSegment 239075373 239206445).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 239075373 ≤ 239140909)
    (by decide : 239140909 ≤ 239206445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239075373 239206445).card = 480 := join_1_0

end S114C00
end Sude.GeneratedTwinScan
