import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19661)) 386531373 386564141 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386531373 386564141).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19661 386531373 386564141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19662)) 386564141 386596909 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386564141 386596909).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19662 386564141 386596909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19662)) 386596909 386629677 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386596909 386629677).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19662 386596909 386629677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19663)) 386629677 386662445 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 386629677 386662445).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19663 386629677 386662445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386531373 386596909).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 386531373 ≤ 386564141)
    (by decide : 386564141 ≤ 386596909) block0 block1

theorem join_0_1 : (twinPrimeSegment 386596909 386662445).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 386596909 ≤ 386629677)
    (by decide : 386629677 ≤ 386662445) block2 block3

theorem join_1_0 : (twinPrimeSegment 386531373 386662445).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 386531373 ≤ 386596909)
    (by decide : 386596909 ≤ 386662445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386531373 386662445).card = 419 := join_1_0

end S184C05
end Sude.GeneratedTwinScan
