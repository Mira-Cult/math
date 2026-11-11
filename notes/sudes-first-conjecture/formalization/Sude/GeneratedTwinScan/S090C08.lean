import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13777)) 189792301 189825069 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 189792301 189825069).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13777 189792301 189825069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13778)) 189825069 189857837 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 189825069 189857837).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13778 189825069 189857837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13780)) 189857837 189890605 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 189857837 189890605).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13780 189857837 189890605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13781)) 189890605 189923373 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 189890605 189923373).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13781 189890605 189923373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 189792301 189857837).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 189792301 ≤ 189825069)
    (by decide : 189825069 ≤ 189857837) block0 block1

theorem join_0_1 : (twinPrimeSegment 189857837 189923373).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 189857837 ≤ 189890605)
    (by decide : 189890605 ≤ 189923373) block2 block3

theorem join_1_0 : (twinPrimeSegment 189792301 189923373).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 189792301 ≤ 189857837)
    (by decide : 189857837 ≤ 189923373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 189792301 189923373).card = 494 := join_1_0

end S090C08
end Sude.GeneratedTwinScan
