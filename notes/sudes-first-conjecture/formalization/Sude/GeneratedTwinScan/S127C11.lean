import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16364)) 267780141 267812909 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 267780141 267812909).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16364 267780141 267812909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16365)) 267812909 267845677 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 267812909 267845677).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16365 267812909 267845677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16366)) 267845677 267878445 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 267845677 267878445).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16366 267845677 267878445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16367)) 267878445 267911213 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 267878445 267911213).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16367 267878445 267911213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 267780141 267845677).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 267780141 ≤ 267812909)
    (by decide : 267812909 ≤ 267845677) block0 block1

theorem join_0_1 : (twinPrimeSegment 267845677 267911213).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 267845677 ≤ 267878445)
    (by decide : 267878445 ≤ 267911213) block2 block3

theorem join_1_0 : (twinPrimeSegment 267780141 267911213).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 267780141 ≤ 267845677)
    (by decide : 267845677 ≤ 267911213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 267780141 267911213).card = 475 := join_1_0

end S127C11
end Sude.GeneratedTwinScan
