import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93192237 93225005 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 93192237 93225005).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93192237 93225005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93225005 93257773 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 93225005 93257773).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93225005 93257773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93257773 93290541 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 93257773 93290541).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93257773 93290541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93290541 93323309 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 93290541 93323309).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93290541 93323309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 93192237 93257773).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 93192237 ≤ 93225005)
    (by decide : 93225005 ≤ 93257773) block0 block1

theorem join_0_1 : (twinPrimeSegment 93257773 93323309).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 93257773 ≤ 93290541)
    (by decide : 93290541 ≤ 93323309) block2 block3

theorem join_1_0 : (twinPrimeSegment 93192237 93323309).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 93192237 ≤ 93257773)
    (by decide : 93257773 ≤ 93323309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 93192237 93323309).card = 512 := join_1_0

end S044C07
end Sude.GeneratedTwinScan
