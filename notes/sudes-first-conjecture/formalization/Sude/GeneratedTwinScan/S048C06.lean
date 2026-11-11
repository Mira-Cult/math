import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101449773 101482541 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101449773 101482541).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101449773 101482541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101482541 101515309 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 101482541 101515309).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101482541 101515309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101515309 101548077 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 101515309 101548077).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101515309 101548077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101548077 101580845 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101548077 101580845).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101548077 101580845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101449773 101515309).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 101449773 ≤ 101482541)
    (by decide : 101482541 ≤ 101515309) block0 block1

theorem join_0_1 : (twinPrimeSegment 101515309 101580845).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 101515309 ≤ 101548077)
    (by decide : 101548077 ≤ 101580845) block2 block3

theorem join_1_0 : (twinPrimeSegment 101449773 101580845).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 101449773 ≤ 101515309)
    (by decide : 101515309 ≤ 101580845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101449773 101580845).card = 488 := join_1_0

end S048C06
end Sude.GeneratedTwinScan
