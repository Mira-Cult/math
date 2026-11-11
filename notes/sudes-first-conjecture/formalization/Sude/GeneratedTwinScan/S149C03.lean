import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17689)) 312868909 312901677 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 312868909 312901677).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17689 312868909 312901677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17689)) 312901677 312934445 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 312901677 312934445).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17689 312901677 312934445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17690)) 312934445 312967213 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312934445 312967213).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17690 312934445 312967213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17691)) 312967213 312999981 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312967213 312999981).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17691 312967213 312999981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 312868909 312934445).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 312868909 ≤ 312901677)
    (by decide : 312901677 ≤ 312934445) block0 block1

theorem join_0_1 : (twinPrimeSegment 312934445 312999981).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 312934445 ≤ 312967213)
    (by decide : 312967213 ≤ 312999981) block2 block3

theorem join_1_0 : (twinPrimeSegment 312868909 312999981).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 312868909 ≤ 312934445)
    (by decide : 312934445 ≤ 312999981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 312868909 312999981).card = 447 := join_1_0

end S149C03
end Sude.GeneratedTwinScan
