import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19453)) 378404909 378437677 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 378404909 378437677).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19453 378404909 378437677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19454)) 378437677 378470445 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 378437677 378470445).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19454 378437677 378470445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19455)) 378470445 378503213 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 378470445 378503213).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19455 378470445 378503213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19456)) 378503213 378535981 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 378503213 378535981).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19456 378503213 378535981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 378404909 378470445).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 378404909 ≤ 378437677)
    (by decide : 378437677 ≤ 378470445) block0 block1

theorem join_0_1 : (twinPrimeSegment 378470445 378535981).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 378470445 ≤ 378503213)
    (by decide : 378503213 ≤ 378535981) block2 block3

theorem join_1_0 : (twinPrimeSegment 378404909 378535981).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 378404909 ≤ 378470445)
    (by decide : 378470445 ≤ 378535981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 378404909 378535981).card = 427 := join_1_0

end S180C07
end Sude.GeneratedTwinScan
