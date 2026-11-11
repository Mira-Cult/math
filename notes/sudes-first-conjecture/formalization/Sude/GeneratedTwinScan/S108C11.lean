import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15098)) 227934253 227967021 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227934253 227967021).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15098 227934253 227967021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15099)) 227967021 227999789 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227967021 227999789).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15099 227967021 227999789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15100)) 227999789 228032557 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227999789 228032557).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15100 227999789 228032557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15101)) 228032557 228065325 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 228032557 228065325).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15101 228032557 228065325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227934253 227999789).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 227934253 ≤ 227967021)
    (by decide : 227967021 ≤ 227999789) block0 block1

theorem join_0_1 : (twinPrimeSegment 227999789 228065325).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 227999789 ≤ 228032557)
    (by decide : 228032557 ≤ 228065325) block2 block3

theorem join_1_0 : (twinPrimeSegment 227934253 228065325).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 227934253 ≤ 227999789)
    (by decide : 227999789 ≤ 228065325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227934253 228065325).card = 437 := join_1_0

end S108C11
end Sude.GeneratedTwinScan
