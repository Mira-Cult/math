import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16556)) 274071597 274104365 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274071597 274104365).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16556 274071597 274104365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16557)) 274104365 274137133 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 274104365 274137133).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16557 274104365 274137133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16558)) 274137133 274169901 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274137133 274169901).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16558 274137133 274169901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16559)) 274169901 274202669 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274169901 274202669).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16559 274169901 274202669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274071597 274137133).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 274071597 ≤ 274104365)
    (by decide : 274104365 ≤ 274137133) block0 block1

theorem join_0_1 : (twinPrimeSegment 274137133 274202669).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 274137133 ≤ 274169901)
    (by decide : 274169901 ≤ 274202669) block2 block3

theorem join_1_0 : (twinPrimeSegment 274071597 274202669).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 274071597 ≤ 274137133)
    (by decide : 274137133 ≤ 274202669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274071597 274202669).card = 446 := join_1_0

end S130C11
end Sude.GeneratedTwinScan
