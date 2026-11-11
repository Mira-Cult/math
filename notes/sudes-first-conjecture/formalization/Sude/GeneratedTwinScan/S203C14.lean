import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20678)) 427556909 427589677 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427556909 427589677).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20678 427556909 427589677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20679)) 427589677 427622445 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427589677 427622445).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20679 427589677 427622445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20679)) 427622445 427655213 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 427622445 427655213).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20679 427622445 427655213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20680)) 427655213 427687981 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 427655213 427687981).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20680 427655213 427687981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427556909 427622445).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 427556909 ≤ 427589677)
    (by decide : 427589677 ≤ 427622445) block0 block1

theorem join_0_1 : (twinPrimeSegment 427622445 427687981).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 427622445 ≤ 427655213)
    (by decide : 427655213 ≤ 427687981) block2 block3

theorem join_1_0 : (twinPrimeSegment 427556909 427687981).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 427556909 ≤ 427622445)
    (by decide : 427622445 ≤ 427687981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427556909 427687981).card = 430 := join_1_0

end S203C14
end Sude.GeneratedTwinScan
