import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15089)) 227672109 227704877 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227672109 227704877).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15089 227672109 227704877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15090)) 227704877 227737645 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227704877 227737645).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15090 227704877 227737645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15092)) 227737645 227770413 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227737645 227770413).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15092 227737645 227770413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15093)) 227770413 227803181 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 227770413 227803181).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15093 227770413 227803181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227672109 227737645).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 227672109 ≤ 227704877)
    (by decide : 227704877 ≤ 227737645) block0 block1

theorem join_0_1 : (twinPrimeSegment 227737645 227803181).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 227737645 ≤ 227770413)
    (by decide : 227770413 ≤ 227803181) block2 block3

theorem join_1_0 : (twinPrimeSegment 227672109 227803181).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 227672109 ≤ 227737645)
    (by decide : 227737645 ≤ 227803181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227672109 227803181).card = 469 := join_1_0

end S108C09
end Sude.GeneratedTwinScan
