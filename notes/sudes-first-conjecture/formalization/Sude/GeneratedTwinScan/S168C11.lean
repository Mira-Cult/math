import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18809)) 353763373 353796141 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 353763373 353796141).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18809 353763373 353796141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18810)) 353796141 353828909 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353796141 353828909).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18810 353796141 353828909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18811)) 353828909 353861677 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353828909 353861677).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18811 353828909 353861677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18812)) 353861677 353894445 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353861677 353894445).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18812 353861677 353894445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 353763373 353828909).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 353763373 ≤ 353796141)
    (by decide : 353796141 ≤ 353828909) block0 block1

theorem join_0_1 : (twinPrimeSegment 353828909 353894445).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 353828909 ≤ 353861677)
    (by decide : 353861677 ≤ 353894445) block2 block3

theorem join_1_0 : (twinPrimeSegment 353763373 353894445).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 353763373 ≤ 353828909)
    (by decide : 353828909 ≤ 353894445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 353763373 353894445).card = 446 := join_1_0

end S168C11
end Sude.GeneratedTwinScan
