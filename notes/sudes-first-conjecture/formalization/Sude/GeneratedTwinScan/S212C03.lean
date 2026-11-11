import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21095)) 444989485 445022253 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 444989485 445022253).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21095 444989485 445022253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21096)) 445022253 445055021 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445022253 445055021).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21096 445022253 445055021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21097)) 445055021 445087789 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445055021 445087789).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21097 445055021 445087789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21097)) 445087789 445120557 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 445087789 445120557).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21097 445087789 445120557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 444989485 445055021).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 444989485 ≤ 445022253)
    (by decide : 445022253 ≤ 445055021) block0 block1

theorem join_0_1 : (twinPrimeSegment 445055021 445120557).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 445055021 ≤ 445087789)
    (by decide : 445087789 ≤ 445120557) block2 block3

theorem join_1_0 : (twinPrimeSegment 444989485 445120557).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 444989485 ≤ 445055021)
    (by decide : 445055021 ≤ 445120557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 444989485 445120557).card = 429 := join_1_0

end S212C03
end Sude.GeneratedTwinScan
