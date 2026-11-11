import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97517613 97550381 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 97517613 97550381).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97517613 97550381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97550381 97583149 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97550381 97583149).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97550381 97583149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97583149 97615917 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97583149 97615917).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97583149 97615917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97615917 97648685 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 97615917 97648685).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97615917 97648685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 97517613 97583149).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 97517613 ≤ 97550381)
    (by decide : 97550381 ≤ 97583149) block0 block1

theorem join_0_1 : (twinPrimeSegment 97583149 97648685).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 97583149 ≤ 97615917)
    (by decide : 97615917 ≤ 97648685) block2 block3

theorem join_1_0 : (twinPrimeSegment 97517613 97648685).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 97517613 ≤ 97583149)
    (by decide : 97583149 ≤ 97648685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 97517613 97648685).card = 497 := join_1_0

end S046C08
end Sude.GeneratedTwinScan
