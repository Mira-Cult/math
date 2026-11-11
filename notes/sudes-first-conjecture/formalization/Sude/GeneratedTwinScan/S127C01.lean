import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S127C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16324)) 266469421 266502189 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 266469421 266502189).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16324 266469421 266502189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16325)) 266502189 266534957 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 266502189 266534957).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16325 266502189 266534957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16326)) 266534957 266567725 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 266534957 266567725).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16326 266534957 266567725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16327)) 266567725 266600493 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 266567725 266600493).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16327 266567725 266600493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 266469421 266534957).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 266469421 ≤ 266502189)
    (by decide : 266502189 ≤ 266534957) block0 block1

theorem join_0_1 : (twinPrimeSegment 266534957 266600493).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 266534957 ≤ 266567725)
    (by decide : 266567725 ≤ 266600493) block2 block3

theorem join_1_0 : (twinPrimeSegment 266469421 266600493).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 266469421 ≤ 266534957)
    (by decide : 266534957 ≤ 266600493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 266469421 266600493).card = 458 := join_1_0

end S127C01
end Sude.GeneratedTwinScan
