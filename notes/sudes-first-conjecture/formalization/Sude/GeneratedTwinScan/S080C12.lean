import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13014)) 169345069 169377837 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 169345069 169377837).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13014 169345069 169377837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13015)) 169377837 169410605 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 169377837 169410605).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13015 169377837 169410605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13017)) 169410605 169443373 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169410605 169443373).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13017 169410605 169443373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13018)) 169443373 169476141 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169443373 169476141).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13018 169443373 169476141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 169345069 169410605).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 169345069 ≤ 169377837)
    (by decide : 169377837 ≤ 169410605) block0 block1

theorem join_0_1 : (twinPrimeSegment 169410605 169476141).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 169410605 ≤ 169443373)
    (by decide : 169443373 ≤ 169476141) block2 block3

theorem join_1_0 : (twinPrimeSegment 169345069 169476141).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 169345069 ≤ 169410605)
    (by decide : 169410605 ≤ 169476141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 169345069 169476141).card = 484 := join_1_0

end S080C12
end Sude.GeneratedTwinScan
