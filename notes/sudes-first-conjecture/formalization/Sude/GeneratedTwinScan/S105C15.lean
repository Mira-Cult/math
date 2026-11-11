import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14906)) 222167085 222199853 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 222167085 222199853).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14906 222167085 222199853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14907)) 222199853 222232621 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 222199853 222232621).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14907 222199853 222232621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14908)) 222232621 222265389 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 222232621 222265389).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14908 222232621 222265389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14909)) 222265389 222298157 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 222265389 222298157).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14909 222265389 222298157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 222167085 222232621).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 222167085 ≤ 222199853)
    (by decide : 222199853 ≤ 222232621) block0 block1

theorem join_0_1 : (twinPrimeSegment 222232621 222298157).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 222232621 ≤ 222265389)
    (by decide : 222265389 ≤ 222298157) block2 block3

theorem join_1_0 : (twinPrimeSegment 222167085 222298157).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 222167085 ≤ 222232621)
    (by decide : 222232621 ≤ 222298157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 222167085 222298157).card = 463 := join_1_0

end S105C15
end Sude.GeneratedTwinScan
