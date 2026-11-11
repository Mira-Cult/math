import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17982)) 323354669 323387437 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 323354669 323387437).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17982 323354669 323387437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17983)) 323387437 323420205 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 323387437 323420205).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17983 323387437 323420205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17984)) 323420205 323452973 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 323420205 323452973).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17984 323420205 323452973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17985)) 323452973 323485741 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 323452973 323485741).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17985 323452973 323485741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 323354669 323420205).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 323354669 ≤ 323387437)
    (by decide : 323387437 ≤ 323420205) block0 block1

theorem join_0_1 : (twinPrimeSegment 323420205 323485741).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 323420205 ≤ 323452973)
    (by decide : 323452973 ≤ 323485741) block2 block3

theorem join_1_0 : (twinPrimeSegment 323354669 323485741).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 323354669 ≤ 323420205)
    (by decide : 323420205 ≤ 323485741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 323354669 323485741).card = 420 := join_1_0

end S154C03
end Sude.GeneratedTwinScan
