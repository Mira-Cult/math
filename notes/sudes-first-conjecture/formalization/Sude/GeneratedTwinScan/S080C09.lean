import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12999)) 168951853 168984621 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168951853 168984621).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12999 168951853 168984621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13000)) 168984621 169017389 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168984621 169017389).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13000 168984621 169017389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13001)) 169017389 169050157 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169017389 169050157).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13001 169017389 169050157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13003)) 169050157 169082925 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169050157 169082925).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13003 169050157 169082925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168951853 169017389).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 168951853 ≤ 168984621)
    (by decide : 168984621 ≤ 169017389) block0 block1

theorem join_0_1 : (twinPrimeSegment 169017389 169082925).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 169017389 ≤ 169050157)
    (by decide : 169050157 ≤ 169082925) block2 block3

theorem join_1_0 : (twinPrimeSegment 168951853 169082925).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 168951853 ≤ 169017389)
    (by decide : 169017389 ≤ 169082925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168951853 169082925).card = 484 := join_1_0

end S080C09
end Sude.GeneratedTwinScan
