import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14649)) 214564909 214597677 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 214564909 214597677).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14649 214564909 214597677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14650)) 214597677 214630445 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 214597677 214630445).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14650 214597677 214630445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14651)) 214630445 214663213 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 214630445 214663213).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14651 214630445 214663213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14652)) 214663213 214695981 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 214663213 214695981).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14652 214663213 214695981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 214564909 214630445).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 214564909 ≤ 214597677)
    (by decide : 214597677 ≤ 214630445) block0 block1

theorem join_0_1 : (twinPrimeSegment 214630445 214695981).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 214630445 ≤ 214663213)
    (by decide : 214663213 ≤ 214695981) block2 block3

theorem join_1_0 : (twinPrimeSegment 214564909 214695981).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 214564909 ≤ 214630445)
    (by decide : 214630445 ≤ 214695981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 214564909 214695981).card = 485 := join_1_0

end S102C05
end Sude.GeneratedTwinScan
