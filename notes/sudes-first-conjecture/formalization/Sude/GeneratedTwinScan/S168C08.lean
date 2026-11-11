import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18799)) 353370157 353402925 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 353370157 353402925).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18799 353370157 353402925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18799)) 353402925 353435693 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353402925 353435693).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18799 353402925 353435693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18800)) 353435693 353468461 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353435693 353468461).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18800 353435693 353468461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18801)) 353468461 353501229 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353468461 353501229).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18801 353468461 353501229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 353370157 353435693).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 353370157 ≤ 353402925)
    (by decide : 353402925 ≤ 353435693) block0 block1

theorem join_0_1 : (twinPrimeSegment 353435693 353501229).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 353435693 ≤ 353468461)
    (by decide : 353468461 ≤ 353501229) block2 block3

theorem join_1_0 : (twinPrimeSegment 353370157 353501229).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 353370157 ≤ 353435693)
    (by decide : 353435693 ≤ 353501229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 353370157 353501229).card = 452 := join_1_0

end S168C08
end Sude.GeneratedTwinScan
