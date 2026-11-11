import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16240)) 263716909 263749677 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263716909 263749677).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16240 263716909 263749677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16241)) 263749677 263782445 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 263749677 263782445).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16241 263749677 263782445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16242)) 263782445 263815213 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 263782445 263815213).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16242 263782445 263815213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16243)) 263815213 263847981 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 263815213 263847981).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16243 263815213 263847981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263716909 263782445).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 263716909 ≤ 263749677)
    (by decide : 263749677 ≤ 263782445) block0 block1

theorem join_0_1 : (twinPrimeSegment 263782445 263847981).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 263782445 ≤ 263815213)
    (by decide : 263815213 ≤ 263847981) block2 block3

theorem join_1_0 : (twinPrimeSegment 263716909 263847981).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 263716909 ≤ 263782445)
    (by decide : 263782445 ≤ 263847981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263716909 263847981).card = 432 := join_1_0

end S125C12
end Sude.GeneratedTwinScan
