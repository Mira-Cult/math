import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13318)) 177340461 177373229 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177340461 177373229).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13318 177340461 177373229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13319)) 177373229 177405997 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 177373229 177405997).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13319 177373229 177405997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13320)) 177405997 177438765 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177405997 177438765).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13320 177405997 177438765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13321)) 177438765 177471533 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177438765 177471533).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13321 177438765 177471533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177340461 177405997).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 177340461 ≤ 177373229)
    (by decide : 177373229 ≤ 177405997) block0 block1

theorem join_0_1 : (twinPrimeSegment 177405997 177471533).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 177405997 ≤ 177438765)
    (by decide : 177438765 ≤ 177471533) block2 block3

theorem join_1_0 : (twinPrimeSegment 177340461 177471533).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 177340461 ≤ 177405997)
    (by decide : 177405997 ≤ 177471533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177340461 177471533).card = 486 := join_1_0

end S084C09
end Sude.GeneratedTwinScan
