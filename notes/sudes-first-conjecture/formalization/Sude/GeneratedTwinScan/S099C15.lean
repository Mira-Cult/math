import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14478)) 209584173 209616941 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209584173 209616941).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14478 209584173 209616941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14479)) 209616941 209649709 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 209616941 209649709).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14479 209616941 209649709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14480)) 209649709 209682477 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 209649709 209682477).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14480 209649709 209682477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14481)) 209682477 209715245 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 209682477 209715245).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14481 209682477 209715245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209584173 209649709).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 209584173 ≤ 209616941)
    (by decide : 209616941 ≤ 209649709) block0 block1

theorem join_0_1 : (twinPrimeSegment 209649709 209715245).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 209649709 ≤ 209682477)
    (by decide : 209682477 ≤ 209715245) block2 block3

theorem join_1_0 : (twinPrimeSegment 209584173 209715245).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 209584173 ≤ 209649709)
    (by decide : 209649709 ≤ 209715245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209584173 209715245).card = 477 := join_1_0

end S099C15
end Sude.GeneratedTwinScan
