import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17484)) 305659949 305692717 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305659949 305692717).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17484 305659949 305692717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17485)) 305692717 305725485 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305692717 305725485).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17485 305692717 305725485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17485)) 305725485 305758253 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305725485 305758253).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17485 305725485 305758253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17486)) 305758253 305791021 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 305758253 305791021).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17486 305758253 305791021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305659949 305725485).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 305659949 ≤ 305692717)
    (by decide : 305692717 ≤ 305725485) block0 block1

theorem join_0_1 : (twinPrimeSegment 305725485 305791021).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 305725485 ≤ 305758253)
    (by decide : 305758253 ≤ 305791021) block2 block3

theorem join_1_0 : (twinPrimeSegment 305659949 305791021).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 305659949 ≤ 305725485)
    (by decide : 305725485 ≤ 305791021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305659949 305791021).card = 443 := join_1_0

end S145C12
end Sude.GeneratedTwinScan
