import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16939)) 286916653 286949421 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 286916653 286949421).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16939 286916653 286949421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16940)) 286949421 286982189 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286949421 286982189).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16940 286949421 286982189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16941)) 286982189 287014957 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286982189 287014957).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16941 286982189 287014957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16942)) 287014957 287047725 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287014957 287047725).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16942 287014957 287047725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 286916653 286982189).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 286916653 ≤ 286949421)
    (by decide : 286949421 ≤ 286982189) block0 block1

theorem join_0_1 : (twinPrimeSegment 286982189 287047725).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 286982189 ≤ 287014957)
    (by decide : 287014957 ≤ 287047725) block2 block3

theorem join_1_0 : (twinPrimeSegment 286916653 287047725).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 286916653 ≤ 286982189)
    (by decide : 286982189 ≤ 287047725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 286916653 287047725).card = 457 := join_1_0

end S136C13
end Sude.GeneratedTwinScan
