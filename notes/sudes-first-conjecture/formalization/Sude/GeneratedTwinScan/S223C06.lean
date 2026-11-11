import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21644)) 468451373 468484141 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 468451373 468484141).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21644 468451373 468484141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21645)) 468484141 468516909 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 468484141 468516909).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21645 468484141 468516909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21646)) 468516909 468549677 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 468516909 468549677).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21646 468516909 468549677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21646)) 468549677 468582445 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 468549677 468582445).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21646 468549677 468582445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 468451373 468516909).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 468451373 ≤ 468484141)
    (by decide : 468484141 ≤ 468516909) block0 block1

theorem join_0_1 : (twinPrimeSegment 468516909 468582445).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 468516909 ≤ 468549677)
    (by decide : 468549677 ≤ 468582445) block2 block3

theorem join_1_0 : (twinPrimeSegment 468451373 468582445).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 468451373 ≤ 468516909)
    (by decide : 468516909 ≤ 468582445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 468451373 468582445).card = 436 := join_1_0

end S223C06
end Sude.GeneratedTwinScan
