import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21507)) 462553133 462585901 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 462553133 462585901).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21507 462553133 462585901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21508)) 462585901 462618669 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 462585901 462618669).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21508 462585901 462618669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21509)) 462618669 462651437 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 462618669 462651437).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21509 462618669 462651437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21510)) 462651437 462684205 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 462651437 462684205).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21510 462651437 462684205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 462553133 462618669).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 462553133 ≤ 462585901)
    (by decide : 462585901 ≤ 462618669) block0 block1

theorem join_0_1 : (twinPrimeSegment 462618669 462684205).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 462618669 ≤ 462651437)
    (by decide : 462651437 ≤ 462684205) block2 block3

theorem join_1_0 : (twinPrimeSegment 462553133 462684205).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 462553133 ≤ 462618669)
    (by decide : 462618669 ≤ 462684205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 462553133 462684205).card = 450 := join_1_0

end S220C09
end Sude.GeneratedTwinScan
