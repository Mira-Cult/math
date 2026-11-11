import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18368)) 337379373 337412141 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 337379373 337412141).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18368 337379373 337412141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18369)) 337412141 337444909 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337412141 337444909).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18369 337412141 337444909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18370)) 337444909 337477677 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337444909 337477677).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18370 337444909 337477677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18371)) 337477677 337510445 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 337477677 337510445).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18371 337477677 337510445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 337379373 337444909).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 337379373 ≤ 337412141)
    (by decide : 337412141 ≤ 337444909) block0 block1

theorem join_0_1 : (twinPrimeSegment 337444909 337510445).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 337444909 ≤ 337477677)
    (by decide : 337477677 ≤ 337510445) block2 block3

theorem join_1_0 : (twinPrimeSegment 337379373 337510445).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 337379373 ≤ 337444909)
    (by decide : 337444909 ≤ 337510445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 337379373 337510445).card = 458 := join_1_0

end S160C14
end Sude.GeneratedTwinScan
