import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12662)) 160301101 160333869 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 160301101 160333869).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12662 160301101 160333869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12663)) 160333869 160366637 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 160333869 160366637).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12663 160333869 160366637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12664)) 160366637 160399405 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 160366637 160399405).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12664 160366637 160399405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12666)) 160399405 160432173 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160399405 160432173).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12666 160399405 160432173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 160301101 160366637).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 160301101 ≤ 160333869)
    (by decide : 160333869 ≤ 160366637) block0 block1

theorem join_0_1 : (twinPrimeSegment 160366637 160432173).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 160366637 ≤ 160399405)
    (by decide : 160399405 ≤ 160432173) block2 block3

theorem join_1_0 : (twinPrimeSegment 160301101 160432173).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 160301101 ≤ 160366637)
    (by decide : 160366637 ≤ 160432173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 160301101 160432173).card = 482 := join_1_0

end S076C07
end Sude.GeneratedTwinScan
