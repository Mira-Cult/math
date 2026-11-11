import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14318)) 204996653 205029421 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204996653 205029421).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14318 204996653 205029421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14319)) 205029421 205062189 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205029421 205062189).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14319 205029421 205062189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14321)) 205062189 205094957 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205062189 205094957).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14321 205062189 205094957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14322)) 205094957 205127725 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 205094957 205127725).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14322 205094957 205127725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204996653 205062189).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 204996653 ≤ 205029421)
    (by decide : 205029421 ≤ 205062189) block0 block1

theorem join_0_1 : (twinPrimeSegment 205062189 205127725).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 205062189 ≤ 205094957)
    (by decide : 205094957 ≤ 205127725) block2 block3

theorem join_1_0 : (twinPrimeSegment 204996653 205127725).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 204996653 ≤ 205062189)
    (by decide : 205062189 ≤ 205127725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204996653 205127725).card = 473 := join_1_0

end S097C12
end Sude.GeneratedTwinScan
