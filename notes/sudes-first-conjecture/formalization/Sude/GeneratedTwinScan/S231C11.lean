import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22043)) 485883949 485916717 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 485883949 485916717).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22043 485883949 485916717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22044)) 485916717 485949485 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 485916717 485949485).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22044 485916717 485949485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22045)) 485949485 485982253 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485949485 485982253).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22045 485949485 485982253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22045)) 485982253 486015021 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485982253 486015021).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22045 485982253 486015021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 485883949 485949485).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 485883949 ≤ 485916717)
    (by decide : 485916717 ≤ 485949485) block0 block1

theorem join_0_1 : (twinPrimeSegment 485949485 486015021).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 485949485 ≤ 485982253)
    (by decide : 485982253 ≤ 486015021) block2 block3

theorem join_1_0 : (twinPrimeSegment 485883949 486015021).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 485883949 ≤ 485949485)
    (by decide : 485949485 ≤ 486015021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 485883949 486015021).card = 456 := join_1_0

end S231C11
end Sude.GeneratedTwinScan
