import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S142C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17269)) 298188845 298221613 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 298188845 298221613).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17269 298188845 298221613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17270)) 298221613 298254381 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 298221613 298254381).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17270 298221613 298254381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17270)) 298254381 298287149 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 298254381 298287149).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17270 298254381 298287149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17271)) 298287149 298319917 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 298287149 298319917).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17271 298287149 298319917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 298188845 298254381).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 298188845 ≤ 298221613)
    (by decide : 298221613 ≤ 298254381) block0 block1

theorem join_0_1 : (twinPrimeSegment 298254381 298319917).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 298254381 ≤ 298287149)
    (by decide : 298287149 ≤ 298319917) block2 block3

theorem join_1_0 : (twinPrimeSegment 298188845 298319917).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 298188845 ≤ 298254381)
    (by decide : 298254381 ≤ 298319917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 298188845 298319917).card = 425 := join_1_0

end S142C03
end Sude.GeneratedTwinScan
