import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19348)) 374341677 374374445 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 374341677 374374445).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19348 374341677 374374445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19349)) 374374445 374407213 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 374374445 374407213).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19349 374374445 374407213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19350)) 374407213 374439981 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 374407213 374439981).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19350 374407213 374439981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19351)) 374439981 374472749 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 374439981 374472749).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19351 374439981 374472749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 374341677 374407213).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 374341677 ≤ 374374445)
    (by decide : 374374445 ≤ 374407213) block0 block1

theorem join_0_1 : (twinPrimeSegment 374407213 374472749).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 374407213 ≤ 374439981)
    (by decide : 374439981 ≤ 374472749) block2 block3

theorem join_1_0 : (twinPrimeSegment 374341677 374472749).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 374341677 ≤ 374407213)
    (by decide : 374407213 ≤ 374472749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 374341677 374472749).card = 463 := join_1_0

end S178C08
end Sude.GeneratedTwinScan
