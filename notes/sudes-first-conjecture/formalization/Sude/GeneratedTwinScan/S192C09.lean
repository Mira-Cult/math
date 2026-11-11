import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20096)) 403832877 403865645 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 403832877 403865645).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20096 403832877 403865645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20097)) 403865645 403898413 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 403865645 403898413).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20097 403865645 403898413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20098)) 403898413 403931181 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 403898413 403931181).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20098 403898413 403931181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20098)) 403931181 403963949 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 403931181 403963949).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20098 403931181 403963949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 403832877 403898413).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 403832877 ≤ 403865645)
    (by decide : 403865645 ≤ 403898413) block0 block1

theorem join_0_1 : (twinPrimeSegment 403898413 403963949).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 403898413 ≤ 403931181)
    (by decide : 403931181 ≤ 403963949) block2 block3

theorem join_1_0 : (twinPrimeSegment 403832877 403963949).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 403832877 ≤ 403898413)
    (by decide : 403898413 ≤ 403963949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 403832877 403963949).card = 463 := join_1_0

end S192C09
end Sude.GeneratedTwinScan
