import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15496)) 240123949 240156717 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 240123949 240156717).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15496 240123949 240156717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15498)) 240156717 240189485 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 240156717 240189485).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15498 240156717 240189485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15499)) 240189485 240222253 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 240189485 240222253).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15499 240189485 240222253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15500)) 240222253 240255021 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 240222253 240255021).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15500 240222253 240255021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 240123949 240189485).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 240123949 ≤ 240156717)
    (by decide : 240156717 ≤ 240189485) block0 block1

theorem join_0_1 : (twinPrimeSegment 240189485 240255021).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 240189485 ≤ 240222253)
    (by decide : 240222253 ≤ 240255021) block2 block3

theorem join_1_0 : (twinPrimeSegment 240123949 240255021).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 240123949 ≤ 240189485)
    (by decide : 240189485 ≤ 240255021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 240123949 240255021).card = 480 := join_1_0

end S114C08
end Sude.GeneratedTwinScan
