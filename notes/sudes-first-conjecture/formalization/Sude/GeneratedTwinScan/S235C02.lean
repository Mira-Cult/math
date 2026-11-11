import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22206)) 493092909 493125677 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 493092909 493125677).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22206 493092909 493125677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22207)) 493125677 493158445 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 493125677 493158445).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22207 493125677 493158445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22207)) 493158445 493191213 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493158445 493191213).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22207 493158445 493191213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22208)) 493191213 493223981 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493191213 493223981).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22208 493191213 493223981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 493092909 493158445).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 493092909 ≤ 493125677)
    (by decide : 493125677 ≤ 493158445) block0 block1

theorem join_0_1 : (twinPrimeSegment 493158445 493223981).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 493158445 ≤ 493191213)
    (by decide : 493191213 ≤ 493223981) block2 block3

theorem join_1_0 : (twinPrimeSegment 493092909 493223981).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 493092909 ≤ 493158445)
    (by decide : 493158445 ≤ 493223981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 493092909 493223981).card = 445 := join_1_0

end S235C02
end Sude.GeneratedTwinScan
