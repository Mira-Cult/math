import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16400)) 268959789 268992557 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268959789 268992557).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16400 268959789 268992557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16401)) 268992557 269025325 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268992557 269025325).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16401 268992557 269025325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16402)) 269025325 269058093 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269025325 269058093).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16402 269025325 269058093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16403)) 269058093 269090861 = 91 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269058093 269090861).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16403 269058093 269090861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268959789 269025325).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 268959789 ≤ 268992557)
    (by decide : 268992557 ≤ 269025325) block0 block1

theorem join_0_1 : (twinPrimeSegment 269025325 269090861).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 269025325 ≤ 269058093)
    (by decide : 269058093 ≤ 269090861) block2 block3

theorem join_1_0 : (twinPrimeSegment 268959789 269090861).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 268959789 ≤ 269025325)
    (by decide : 269025325 ≤ 269090861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268959789 269090861).card = 421 := join_1_0

end S128C04
end Sude.GeneratedTwinScan
