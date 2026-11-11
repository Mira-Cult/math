import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21825)) 476315693 476348461 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 476315693 476348461).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21825 476315693 476348461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21826)) 476348461 476381229 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 476348461 476381229).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21826 476348461 476381229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21826)) 476381229 476413997 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 476381229 476413997).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21826 476381229 476413997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21827)) 476413997 476446765 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 476413997 476446765).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21827 476413997 476446765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 476315693 476381229).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 476315693 ≤ 476348461)
    (by decide : 476348461 ≤ 476381229) block0 block1

theorem join_0_1 : (twinPrimeSegment 476381229 476446765).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 476381229 ≤ 476413997)
    (by decide : 476413997 ≤ 476446765) block2 block3

theorem join_1_0 : (twinPrimeSegment 476315693 476446765).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 476315693 ≤ 476381229)
    (by decide : 476381229 ≤ 476446765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 476315693 476446765).card = 417 := join_1_0

end S227C02
end Sude.GeneratedTwinScan
