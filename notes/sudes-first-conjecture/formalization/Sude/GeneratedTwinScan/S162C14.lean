import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18482)) 341573677 341606445 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 341573677 341606445).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18482 341573677 341606445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18483)) 341606445 341639213 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 341606445 341639213).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18483 341606445 341639213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18484)) 341639213 341671981 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 341639213 341671981).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18484 341639213 341671981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18485)) 341671981 341704749 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 341671981 341704749).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18485 341671981 341704749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 341573677 341639213).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 341573677 ≤ 341606445)
    (by decide : 341606445 ≤ 341639213) block0 block1

theorem join_0_1 : (twinPrimeSegment 341639213 341704749).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 341639213 ≤ 341671981)
    (by decide : 341671981 ≤ 341704749) block2 block3

theorem join_1_0 : (twinPrimeSegment 341573677 341704749).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 341573677 ≤ 341639213)
    (by decide : 341639213 ≤ 341704749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 341573677 341704749).card = 449 := join_1_0

end S162C14
end Sude.GeneratedTwinScan
