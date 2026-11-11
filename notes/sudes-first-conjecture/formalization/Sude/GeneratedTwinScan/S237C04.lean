import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22306)) 497549357 497582125 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497549357 497582125).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22306 497549357 497582125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22307)) 497582125 497614893 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497582125 497614893).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22307 497582125 497614893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22308)) 497614893 497647661 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 497614893 497647661).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22308 497614893 497647661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22308)) 497647661 497680429 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 497647661 497680429).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22308 497647661 497680429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497549357 497614893).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 497549357 ≤ 497582125)
    (by decide : 497582125 ≤ 497614893) block0 block1

theorem join_0_1 : (twinPrimeSegment 497614893 497680429).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 497614893 ≤ 497647661)
    (by decide : 497647661 ≤ 497680429) block2 block3

theorem join_1_0 : (twinPrimeSegment 497549357 497680429).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 497549357 ≤ 497614893)
    (by decide : 497614893 ≤ 497680429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497549357 497680429).card = 443 := join_1_0

end S237C04
end Sude.GeneratedTwinScan
