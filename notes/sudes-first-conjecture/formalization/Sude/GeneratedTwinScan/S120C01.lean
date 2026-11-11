import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15868)) 251789357 251822125 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 251789357 251822125).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15868 251789357 251822125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15869)) 251822125 251854893 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 251822125 251854893).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15869 251822125 251854893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15870)) 251854893 251887661 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 251854893 251887661).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15870 251854893 251887661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15872)) 251887661 251920429 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 251887661 251920429).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15872 251887661 251920429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 251789357 251854893).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 251789357 ≤ 251822125)
    (by decide : 251822125 ≤ 251854893) block0 block1

theorem join_0_1 : (twinPrimeSegment 251854893 251920429).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 251854893 ≤ 251887661)
    (by decide : 251887661 ≤ 251920429) block2 block3

theorem join_1_0 : (twinPrimeSegment 251789357 251920429).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 251789357 ≤ 251854893)
    (by decide : 251854893 ≤ 251920429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 251789357 251920429).card = 437 := join_1_0

end S120C01
end Sude.GeneratedTwinScan
