import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15732)) 247463981 247496749 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 247463981 247496749).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15732 247463981 247496749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15733)) 247496749 247529517 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 247496749 247529517).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15733 247496749 247529517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15734)) 247529517 247562285 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 247529517 247562285).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15734 247529517 247562285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15735)) 247562285 247595053 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 247562285 247595053).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15735 247562285 247595053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 247463981 247529517).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 247463981 ≤ 247496749)
    (by decide : 247496749 ≤ 247529517) block0 block1

theorem join_0_1 : (twinPrimeSegment 247529517 247595053).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 247529517 ≤ 247562285)
    (by decide : 247562285 ≤ 247595053) block2 block3

theorem join_1_0 : (twinPrimeSegment 247463981 247595053).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 247463981 ≤ 247529517)
    (by decide : 247529517 ≤ 247595053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 247463981 247595053).card = 444 := join_1_0

end S118C00
end Sude.GeneratedTwinScan
