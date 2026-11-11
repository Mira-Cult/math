import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16057)) 257818669 257851437 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 257818669 257851437).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16057 257818669 257851437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16058)) 257851437 257884205 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 257851437 257884205).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16058 257851437 257884205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16059)) 257884205 257916973 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 257884205 257916973).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16059 257884205 257916973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16060)) 257916973 257949741 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 257916973 257949741).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16060 257916973 257949741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 257818669 257884205).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 257818669 ≤ 257851437)
    (by decide : 257851437 ≤ 257884205) block0 block1

theorem join_0_1 : (twinPrimeSegment 257884205 257949741).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 257884205 ≤ 257916973)
    (by decide : 257916973 ≤ 257949741) block2 block3

theorem join_1_0 : (twinPrimeSegment 257818669 257949741).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 257818669 ≤ 257884205)
    (by decide : 257884205 ≤ 257949741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 257818669 257949741).card = 484 := join_1_0

end S122C15
end Sude.GeneratedTwinScan
