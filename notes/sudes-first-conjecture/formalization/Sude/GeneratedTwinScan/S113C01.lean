import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S113C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15399)) 237109293 237142061 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 237109293 237142061).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15399 237109293 237142061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15400)) 237142061 237174829 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 237142061 237174829).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15400 237142061 237174829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15401)) 237174829 237207597 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 237174829 237207597).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15401 237174829 237207597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15402)) 237207597 237240365 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 237207597 237240365).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15402 237207597 237240365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 237109293 237174829).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 237109293 ≤ 237142061)
    (by decide : 237142061 ≤ 237174829) block0 block1

theorem join_0_1 : (twinPrimeSegment 237174829 237240365).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 237174829 ≤ 237207597)
    (by decide : 237207597 ≤ 237240365) block2 block3

theorem join_1_0 : (twinPrimeSegment 237109293 237240365).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 237109293 ≤ 237174829)
    (by decide : 237174829 ≤ 237240365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 237109293 237240365).card = 501 := join_1_0

end S113C01
end Sude.GeneratedTwinScan
