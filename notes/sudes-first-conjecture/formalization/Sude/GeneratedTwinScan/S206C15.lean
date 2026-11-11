import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20832)) 433979437 434012205 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 433979437 434012205).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20832 433979437 434012205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20833)) 434012205 434044973 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 434012205 434044973).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20833 434012205 434044973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20834)) 434044973 434077741 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 434044973 434077741).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20834 434044973 434077741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20835)) 434077741 434110509 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 434077741 434110509).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20835 434077741 434110509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 433979437 434044973).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 433979437 ≤ 434012205)
    (by decide : 434012205 ≤ 434044973) block0 block1

theorem join_0_1 : (twinPrimeSegment 434044973 434110509).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 434044973 ≤ 434077741)
    (by decide : 434077741 ≤ 434110509) block2 block3

theorem join_1_0 : (twinPrimeSegment 433979437 434110509).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 433979437 ≤ 434044973)
    (by decide : 434044973 ≤ 434110509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 433979437 434110509).card = 464 := join_1_0

end S206C15
end Sude.GeneratedTwinScan
