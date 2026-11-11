import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18325)) 335806509 335839277 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 335806509 335839277).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18325 335806509 335839277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18326)) 335839277 335872045 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 335839277 335872045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18326 335839277 335872045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18327)) 335872045 335904813 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 335872045 335904813).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18327 335872045 335904813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18328)) 335904813 335937581 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 335904813 335937581).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18328 335904813 335937581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 335806509 335872045).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 335806509 ≤ 335839277)
    (by decide : 335839277 ≤ 335872045) block0 block1

theorem join_0_1 : (twinPrimeSegment 335872045 335937581).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 335872045 ≤ 335904813)
    (by decide : 335904813 ≤ 335937581) block2 block3

theorem join_1_0 : (twinPrimeSegment 335806509 335937581).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 335806509 ≤ 335872045)
    (by decide : 335872045 ≤ 335937581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 335806509 335937581).card = 447 := join_1_0

end S160C02
end Sude.GeneratedTwinScan
