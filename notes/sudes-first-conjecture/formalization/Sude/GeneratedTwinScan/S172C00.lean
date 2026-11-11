import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18993)) 360710189 360742957 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 360710189 360742957).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18993 360710189 360742957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18994)) 360742957 360775725 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 360742957 360775725).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18994 360742957 360775725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18994)) 360775725 360808493 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 360775725 360808493).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18994 360775725 360808493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18995)) 360808493 360841261 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 360808493 360841261).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18995 360808493 360841261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 360710189 360775725).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 360742957)
    (by decide : 360742957 ≤ 360775725) block0 block1

theorem join_0_1 : (twinPrimeSegment 360775725 360841261).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 360775725 ≤ 360808493)
    (by decide : 360808493 ≤ 360841261) block2 block3

theorem join_1_0 : (twinPrimeSegment 360710189 360841261).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 360775725)
    (by decide : 360775725 ≤ 360841261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 360710189 360841261).card = 456 := join_1_0

end S172C00
end Sude.GeneratedTwinScan
