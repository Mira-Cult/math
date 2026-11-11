import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14350)) 205914157 205946925 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 205914157 205946925).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14350 205914157 205946925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14351)) 205946925 205979693 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205946925 205979693).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14351 205946925 205979693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14353)) 205979693 206012461 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205979693 206012461).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14353 205979693 206012461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14354)) 206012461 206045229 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 206012461 206045229).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14354 206012461 206045229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 205914157 205979693).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 205914157 ≤ 205946925)
    (by decide : 205946925 ≤ 205979693) block0 block1

theorem join_0_1 : (twinPrimeSegment 205979693 206045229).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 205979693 ≤ 206012461)
    (by decide : 206012461 ≤ 206045229) block2 block3

theorem join_1_0 : (twinPrimeSegment 205914157 206045229).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 205914157 ≤ 205979693)
    (by decide : 205979693 ≤ 206045229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 205914157 206045229).card = 426 := join_1_0

end S098C03
end Sude.GeneratedTwinScan
