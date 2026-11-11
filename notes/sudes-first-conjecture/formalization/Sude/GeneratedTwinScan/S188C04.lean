import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19870)) 394788909 394821677 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 394788909 394821677).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19870 394788909 394821677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19870)) 394821677 394854445 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 394821677 394854445).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19870 394821677 394854445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19871)) 394854445 394887213 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 394854445 394887213).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19871 394854445 394887213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19872)) 394887213 394919981 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 394887213 394919981).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19872 394887213 394919981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 394788909 394854445).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 394788909 ≤ 394821677)
    (by decide : 394821677 ≤ 394854445) block0 block1

theorem join_0_1 : (twinPrimeSegment 394854445 394919981).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 394854445 ≤ 394887213)
    (by decide : 394887213 ≤ 394919981) block2 block3

theorem join_1_0 : (twinPrimeSegment 394788909 394919981).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 394788909 ≤ 394854445)
    (by decide : 394854445 ≤ 394919981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 394788909 394919981).card = 446 := join_1_0

end S188C04
end Sude.GeneratedTwinScan
