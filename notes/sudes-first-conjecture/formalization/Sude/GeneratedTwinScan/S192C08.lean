import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20093)) 403701805 403734573 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 403701805 403734573).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20093 403701805 403734573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20093)) 403734573 403767341 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 403734573 403767341).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20093 403734573 403767341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20094)) 403767341 403800109 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 403767341 403800109).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20094 403767341 403800109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20095)) 403800109 403832877 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 403800109 403832877).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20095 403800109 403832877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 403701805 403767341).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 403701805 ≤ 403734573)
    (by decide : 403734573 ≤ 403767341) block0 block1

theorem join_0_1 : (twinPrimeSegment 403767341 403832877).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 403767341 ≤ 403800109)
    (by decide : 403800109 ≤ 403832877) block2 block3

theorem join_1_0 : (twinPrimeSegment 403701805 403832877).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 403701805 ≤ 403767341)
    (by decide : 403767341 ≤ 403832877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 403701805 403832877).card = 428 := join_1_0

end S192C08
end Sude.GeneratedTwinScan
