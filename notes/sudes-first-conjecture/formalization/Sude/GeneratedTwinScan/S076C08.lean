import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12667)) 160432173 160464941 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 160432173 160464941).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12667 160432173 160464941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12668)) 160464941 160497709 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 160464941 160497709).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12668 160464941 160497709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12670)) 160497709 160530477 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 160497709 160530477).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12670 160497709 160530477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12671)) 160530477 160563245 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160530477 160563245).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12671 160530477 160563245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 160432173 160497709).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 160432173 ≤ 160464941)
    (by decide : 160464941 ≤ 160497709) block0 block1

theorem join_0_1 : (twinPrimeSegment 160497709 160563245).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 160497709 ≤ 160530477)
    (by decide : 160530477 ≤ 160563245) block2 block3

theorem join_1_0 : (twinPrimeSegment 160432173 160563245).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 160432173 ≤ 160497709)
    (by decide : 160497709 ≤ 160563245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 160432173 160563245).card = 477 := join_1_0

end S076C08
end Sude.GeneratedTwinScan
