import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18920)) 357957677 357990445 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357957677 357990445).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18920 357957677 357990445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18921)) 357990445 358023213 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357990445 358023213).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18921 357990445 358023213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18922)) 358023213 358055981 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 358023213 358055981).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18922 358023213 358055981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18923)) 358055981 358088749 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 358055981 358088749).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18923 358055981 358088749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357957677 358023213).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 357957677 ≤ 357990445)
    (by decide : 357990445 ≤ 358023213) block0 block1

theorem join_0_1 : (twinPrimeSegment 358023213 358088749).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 358023213 ≤ 358055981)
    (by decide : 358055981 ≤ 358088749) block2 block3

theorem join_1_0 : (twinPrimeSegment 357957677 358088749).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 357957677 ≤ 358023213)
    (by decide : 358023213 ≤ 358088749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357957677 358088749).card = 451 := join_1_0

end S170C11
end Sude.GeneratedTwinScan
