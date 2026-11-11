import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20083)) 403308589 403341357 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 403308589 403341357).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20083 403308589 403341357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20084)) 403341357 403374125 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 403341357 403374125).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20084 403341357 403374125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20084)) 403374125 403406893 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 403374125 403406893).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20084 403374125 403406893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20085)) 403406893 403439661 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 403406893 403439661).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20085 403406893 403439661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 403308589 403374125).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 403308589 ≤ 403341357)
    (by decide : 403341357 ≤ 403374125) block0 block1

theorem join_0_1 : (twinPrimeSegment 403374125 403439661).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 403374125 ≤ 403406893)
    (by decide : 403406893 ≤ 403439661) block2 block3

theorem join_1_0 : (twinPrimeSegment 403308589 403439661).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 403308589 ≤ 403374125)
    (by decide : 403374125 ≤ 403439661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 403308589 403439661).card = 460 := join_1_0

end S192C05
end Sude.GeneratedTwinScan
