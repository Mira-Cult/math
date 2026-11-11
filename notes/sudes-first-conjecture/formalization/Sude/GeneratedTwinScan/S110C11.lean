import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15236)) 232128557 232161325 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 232128557 232161325).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15236 232128557 232161325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15237)) 232161325 232194093 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 232161325 232194093).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15237 232161325 232194093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15238)) 232194093 232226861 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 232194093 232226861).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15238 232194093 232226861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15240)) 232226861 232259629 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 232226861 232259629).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15240 232226861 232259629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 232128557 232194093).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 232128557 ≤ 232161325)
    (by decide : 232161325 ≤ 232194093) block0 block1

theorem join_0_1 : (twinPrimeSegment 232194093 232259629).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 232194093 ≤ 232226861)
    (by decide : 232226861 ≤ 232259629) block2 block3

theorem join_1_0 : (twinPrimeSegment 232128557 232259629).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 232128557 ≤ 232194093)
    (by decide : 232194093 ≤ 232259629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 232128557 232259629).card = 457 := join_1_0

end S110C11
end Sude.GeneratedTwinScan
