import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65536045 65568813 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 65536045 65568813).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65536045 65568813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65568813 65601581 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 65568813 65601581).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65568813 65601581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65601581 65634349 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 65601581 65634349).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65601581 65634349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65634349 65667117 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 65634349 65667117).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65634349 65667117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 65536045 65601581).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 65536045 ≤ 65568813)
    (by decide : 65568813 ≤ 65601581) block0 block1

theorem join_0_1 : (twinPrimeSegment 65601581 65667117).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 65601581 ≤ 65634349)
    (by decide : 65634349 ≤ 65667117) block2 block3

theorem join_1_0 : (twinPrimeSegment 65536045 65667117).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 65536045 ≤ 65601581)
    (by decide : 65601581 ≤ 65667117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 65536045 65667117).card = 522 := join_1_0

end S031C04
end Sude.GeneratedTwinScan
