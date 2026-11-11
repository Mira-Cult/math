import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14684)) 215613485 215646253 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 215613485 215646253).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14684 215613485 215646253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14686)) 215646253 215679021 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 215646253 215679021).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14686 215646253 215679021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14687)) 215679021 215711789 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 215679021 215711789).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14687 215679021 215711789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14688)) 215711789 215744557 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 215711789 215744557).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14688 215711789 215744557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 215613485 215679021).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 215613485 ≤ 215646253)
    (by decide : 215646253 ≤ 215679021) block0 block1

theorem join_0_1 : (twinPrimeSegment 215679021 215744557).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 215679021 ≤ 215711789)
    (by decide : 215711789 ≤ 215744557) block2 block3

theorem join_1_0 : (twinPrimeSegment 215613485 215744557).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 215613485 ≤ 215679021)
    (by decide : 215679021 ≤ 215744557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 215613485 215744557).card = 487 := join_1_0

end S102C13
end Sude.GeneratedTwinScan
