import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15271)) 233177133 233209901 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 233177133 233209901).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15271 233177133 233209901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15272)) 233209901 233242669 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 233209901 233242669).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15272 233209901 233242669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15273)) 233242669 233275437 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 233242669 233275437).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15273 233242669 233275437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15274)) 233275437 233308205 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 233275437 233308205).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15274 233275437 233308205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 233177133 233242669).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 233177133 ≤ 233209901)
    (by decide : 233209901 ≤ 233242669) block0 block1

theorem join_0_1 : (twinPrimeSegment 233242669 233308205).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 233242669 ≤ 233275437)
    (by decide : 233275437 ≤ 233308205) block2 block3

theorem join_1_0 : (twinPrimeSegment 233177133 233308205).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 233177133 ≤ 233242669)
    (by decide : 233242669 ≤ 233308205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 233177133 233308205).card = 449 := join_1_0

end S111C03
end Sude.GeneratedTwinScan
