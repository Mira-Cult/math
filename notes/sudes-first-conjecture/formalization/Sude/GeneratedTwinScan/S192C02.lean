import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20073)) 402915373 402948141 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 402915373 402948141).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20073 402915373 402948141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20074)) 402948141 402980909 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 402948141 402980909).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20074 402948141 402980909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20075)) 402980909 403013677 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 402980909 403013677).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20075 402980909 403013677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20076)) 403013677 403046445 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 403013677 403046445).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20076 403013677 403046445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 402915373 402980909).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 402915373 ≤ 402948141)
    (by decide : 402948141 ≤ 402980909) block0 block1

theorem join_0_1 : (twinPrimeSegment 402980909 403046445).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 402980909 ≤ 403013677)
    (by decide : 403013677 ≤ 403046445) block2 block3

theorem join_1_0 : (twinPrimeSegment 402915373 403046445).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 402915373 ≤ 402980909)
    (by decide : 402980909 ≤ 403046445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 402915373 403046445).card = 471 := join_1_0

end S192C02
end Sude.GeneratedTwinScan
