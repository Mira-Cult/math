import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18214)) 331743277 331776045 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 331743277 331776045).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18214 331743277 331776045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18215)) 331776045 331808813 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 331776045 331808813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18215 331776045 331808813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18216)) 331808813 331841581 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 331808813 331841581).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18216 331808813 331841581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18217)) 331841581 331874349 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 331841581 331874349).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18217 331841581 331874349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 331743277 331808813).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 331743277 ≤ 331776045)
    (by decide : 331776045 ≤ 331808813) block0 block1

theorem join_0_1 : (twinPrimeSegment 331808813 331874349).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 331808813 ≤ 331841581)
    (by decide : 331841581 ≤ 331874349) block2 block3

theorem join_1_0 : (twinPrimeSegment 331743277 331874349).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 331743277 ≤ 331808813)
    (by decide : 331808813 ≤ 331874349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 331743277 331874349).card = 443 := join_1_0

end S158C03
end Sude.GeneratedTwinScan
