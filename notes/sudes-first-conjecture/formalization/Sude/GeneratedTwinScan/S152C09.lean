import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17887)) 319946797 319979565 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 319946797 319979565).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17887 319946797 319979565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17888)) 319979565 320012333 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 319979565 320012333).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17888 319979565 320012333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17889)) 320012333 320045101 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 320012333 320045101).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17889 320012333 320045101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17890)) 320045101 320077869 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 320045101 320077869).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17890 320045101 320077869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 319946797 320012333).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 319946797 ≤ 319979565)
    (by decide : 319979565 ≤ 320012333) block0 block1

theorem join_0_1 : (twinPrimeSegment 320012333 320077869).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 320012333 ≤ 320045101)
    (by decide : 320045101 ≤ 320077869) block2 block3

theorem join_1_0 : (twinPrimeSegment 319946797 320077869).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 319946797 ≤ 320012333)
    (by decide : 320012333 ≤ 320077869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 319946797 320077869).card = 460 := join_1_0

end S152C09
end Sude.GeneratedTwinScan
