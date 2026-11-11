import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21602)) 466616365 466649133 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 466616365 466649133).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21602 466616365 466649133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21602)) 466649133 466681901 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 466649133 466681901).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21602 466649133 466681901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21603)) 466681901 466714669 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 466681901 466714669).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21603 466681901 466714669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21604)) 466714669 466747437 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 466714669 466747437).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21604 466714669 466747437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 466616365 466681901).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 466616365 ≤ 466649133)
    (by decide : 466649133 ≤ 466681901) block0 block1

theorem join_0_1 : (twinPrimeSegment 466681901 466747437).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 466681901 ≤ 466714669)
    (by decide : 466714669 ≤ 466747437) block2 block3

theorem join_1_0 : (twinPrimeSegment 466616365 466747437).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 466616365 ≤ 466681901)
    (by decide : 466681901 ≤ 466747437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 466616365 466747437).card = 411 := join_1_0

end S222C08
end Sude.GeneratedTwinScan
