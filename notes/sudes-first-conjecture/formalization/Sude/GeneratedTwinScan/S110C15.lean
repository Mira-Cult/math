import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15254)) 232652845 232685613 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 232652845 232685613).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15254 232652845 232685613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15255)) 232685613 232718381 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 232685613 232718381).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15255 232685613 232718381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15256)) 232718381 232751149 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 232718381 232751149).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15256 232718381 232751149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15257)) 232751149 232783917 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 232751149 232783917).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15257 232751149 232783917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 232652845 232718381).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 232652845 ≤ 232685613)
    (by decide : 232685613 ≤ 232718381) block0 block1

theorem join_0_1 : (twinPrimeSegment 232718381 232783917).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 232718381 ≤ 232751149)
    (by decide : 232751149 ≤ 232783917) block2 block3

theorem join_1_0 : (twinPrimeSegment 232652845 232783917).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 232652845 ≤ 232718381)
    (by decide : 232718381 ≤ 232783917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 232652845 232783917).card = 443 := join_1_0

end S110C15
end Sude.GeneratedTwinScan
