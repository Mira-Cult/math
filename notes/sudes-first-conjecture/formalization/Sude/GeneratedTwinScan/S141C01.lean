import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17200)) 295829549 295862317 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 295829549 295862317).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17200 295829549 295862317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17201)) 295862317 295895085 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 295862317 295895085).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17201 295862317 295895085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17202)) 295895085 295927853 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 295895085 295927853).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17202 295895085 295927853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17203)) 295927853 295960621 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 295927853 295960621).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17203 295927853 295960621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 295829549 295895085).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 295829549 ≤ 295862317)
    (by decide : 295862317 ≤ 295895085) block0 block1

theorem join_0_1 : (twinPrimeSegment 295895085 295960621).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 295895085 ≤ 295927853)
    (by decide : 295927853 ≤ 295960621) block2 block3

theorem join_1_0 : (twinPrimeSegment 295829549 295960621).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 295829549 ≤ 295895085)
    (by decide : 295895085 ≤ 295960621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 295829549 295960621).card = 421 := join_1_0

end S141C01
end Sude.GeneratedTwinScan
