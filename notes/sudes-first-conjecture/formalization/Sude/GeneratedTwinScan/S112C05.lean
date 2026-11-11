import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15348)) 235536429 235569197 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 235536429 235569197).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15348 235536429 235569197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15349)) 235569197 235601965 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 235569197 235601965).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15349 235569197 235601965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15350)) 235601965 235634733 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 235601965 235634733).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15350 235601965 235634733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15351)) 235634733 235667501 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 235634733 235667501).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15351 235634733 235667501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 235536429 235601965).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 235536429 ≤ 235569197)
    (by decide : 235569197 ≤ 235601965) block0 block1

theorem join_0_1 : (twinPrimeSegment 235601965 235667501).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 235601965 ≤ 235634733)
    (by decide : 235634733 ≤ 235667501) block2 block3

theorem join_1_0 : (twinPrimeSegment 235536429 235667501).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 235536429 ≤ 235601965)
    (by decide : 235601965 ≤ 235667501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 235536429 235667501).card = 466 := join_1_0

end S112C05
end Sude.GeneratedTwinScan
