import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14919)) 222560301 222593069 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 222560301 222593069).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14919 222560301 222593069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14920)) 222593069 222625837 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 222593069 222625837).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14920 222593069 222625837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14921)) 222625837 222658605 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 222625837 222658605).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14921 222625837 222658605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14922)) 222658605 222691373 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 222658605 222691373).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14922 222658605 222691373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 222560301 222625837).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 222560301 ≤ 222593069)
    (by decide : 222593069 ≤ 222625837) block0 block1

theorem join_0_1 : (twinPrimeSegment 222625837 222691373).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 222625837 ≤ 222658605)
    (by decide : 222658605 ≤ 222691373) block2 block3

theorem join_1_0 : (twinPrimeSegment 222560301 222691373).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 222560301 ≤ 222625837)
    (by decide : 222625837 ≤ 222691373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 222560301 222691373).card = 486 := join_1_0

end S106C02
end Sude.GeneratedTwinScan
