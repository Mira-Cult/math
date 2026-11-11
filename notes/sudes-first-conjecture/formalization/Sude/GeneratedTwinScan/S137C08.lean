import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16982)) 288358445 288391213 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 288358445 288391213).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16982 288358445 288391213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16983)) 288391213 288423981 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 288391213 288423981).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16983 288391213 288423981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16984)) 288423981 288456749 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288423981 288456749).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16984 288423981 288456749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16984)) 288456749 288489517 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288456749 288489517).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16984 288456749 288489517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 288358445 288423981).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 288358445 ≤ 288391213)
    (by decide : 288391213 ≤ 288423981) block0 block1

theorem join_0_1 : (twinPrimeSegment 288423981 288489517).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 288423981 ≤ 288456749)
    (by decide : 288456749 ≤ 288489517) block2 block3

theorem join_1_0 : (twinPrimeSegment 288358445 288489517).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 288358445 ≤ 288423981)
    (by decide : 288423981 ≤ 288489517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 288358445 288489517).card = 446 := join_1_0

end S137C08
end Sude.GeneratedTwinScan
