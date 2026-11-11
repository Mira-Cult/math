import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22194)) 492568621 492601389 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492568621 492601389).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22194 492568621 492601389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22195)) 492601389 492634157 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492601389 492634157).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22195 492601389 492634157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22196)) 492634157 492666925 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 492634157 492666925).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22196 492634157 492666925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22196)) 492666925 492699693 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492666925 492699693).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22196 492666925 492699693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492568621 492634157).card = 191 := by
  simpa using combineTwinPrimeSegments (by decide : 492568621 ≤ 492601389)
    (by decide : 492601389 ≤ 492634157) block0 block1

theorem join_0_1 : (twinPrimeSegment 492634157 492699693).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 492634157 ≤ 492666925)
    (by decide : 492666925 ≤ 492699693) block2 block3

theorem join_1_0 : (twinPrimeSegment 492568621 492699693).card = 405 := by
  simpa using combineTwinPrimeSegments (by decide : 492568621 ≤ 492634157)
    (by decide : 492634157 ≤ 492699693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492568621 492699693).card = 405 := join_1_0

end S234C14
end Sude.GeneratedTwinScan
