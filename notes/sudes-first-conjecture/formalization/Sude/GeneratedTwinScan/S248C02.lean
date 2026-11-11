import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22812)) 520355885 520388653 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 520355885 520388653).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22812 520355885 520388653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22812)) 520388653 520421421 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 520388653 520421421).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22812 520388653 520421421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22813)) 520421421 520454189 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 520421421 520454189).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22813 520421421 520454189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22814)) 520454189 520486957 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 520454189 520486957).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22814 520454189 520486957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 520355885 520421421).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 520355885 ≤ 520388653)
    (by decide : 520388653 ≤ 520421421) block0 block1

theorem join_0_1 : (twinPrimeSegment 520421421 520486957).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 520421421 ≤ 520454189)
    (by decide : 520454189 ≤ 520486957) block2 block3

theorem join_1_0 : (twinPrimeSegment 520355885 520486957).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 520355885 ≤ 520421421)
    (by decide : 520421421 ≤ 520486957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 520355885 520486957).card = 423 := join_1_0

end S248C02
end Sude.GeneratedTwinScan
