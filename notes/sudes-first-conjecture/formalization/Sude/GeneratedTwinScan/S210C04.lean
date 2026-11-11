import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20999)) 440926253 440959021 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 440926253 440959021).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20999 440926253 440959021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20999)) 440959021 440991789 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 440959021 440991789).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20999 440959021 440991789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21000)) 440991789 441024557 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 440991789 441024557).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21000 440991789 441024557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21001)) 441024557 441057325 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 441024557 441057325).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21001 441024557 441057325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 440926253 440991789).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 440926253 ≤ 440959021)
    (by decide : 440959021 ≤ 440991789) block0 block1

theorem join_0_1 : (twinPrimeSegment 440991789 441057325).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 440991789 ≤ 441024557)
    (by decide : 441024557 ≤ 441057325) block2 block3

theorem join_1_0 : (twinPrimeSegment 440926253 441057325).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 440926253 ≤ 440991789)
    (by decide : 440991789 ≤ 441057325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 440926253 441057325).card = 456 := join_1_0

end S210C04
end Sude.GeneratedTwinScan
