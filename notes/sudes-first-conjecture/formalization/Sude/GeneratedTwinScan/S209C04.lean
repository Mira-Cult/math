import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20949)) 438829101 438861869 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 438829101 438861869).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20949 438829101 438861869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20949)) 438861869 438894637 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 438861869 438894637).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20949 438861869 438894637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20950)) 438894637 438927405 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 438894637 438927405).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20950 438894637 438927405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20951)) 438927405 438960173 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 438927405 438960173).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20951 438927405 438960173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 438829101 438894637).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 438829101 ≤ 438861869)
    (by decide : 438861869 ≤ 438894637) block0 block1

theorem join_0_1 : (twinPrimeSegment 438894637 438960173).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 438894637 ≤ 438927405)
    (by decide : 438927405 ≤ 438960173) block2 block3

theorem join_1_0 : (twinPrimeSegment 438829101 438960173).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 438829101 ≤ 438894637)
    (by decide : 438894637 ≤ 438960173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 438829101 438960173).card = 412 := join_1_0

end S209C04
end Sude.GeneratedTwinScan
