import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20086)) 403439661 403472429 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 403439661 403472429).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20086 403439661 403472429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20087)) 403472429 403505197 = 86 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 403472429 403505197).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20087 403472429 403505197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20088)) 403505197 403537965 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 403505197 403537965).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20088 403505197 403537965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20089)) 403537965 403570733 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 403537965 403570733).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20089 403537965 403570733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 403439661 403505197).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 403439661 ≤ 403472429)
    (by decide : 403472429 ≤ 403505197) block0 block1

theorem join_0_1 : (twinPrimeSegment 403505197 403570733).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 403505197 ≤ 403537965)
    (by decide : 403537965 ≤ 403570733) block2 block3

theorem join_1_0 : (twinPrimeSegment 403439661 403570733).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 403439661 ≤ 403505197)
    (by decide : 403505197 ≤ 403570733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 403439661 403570733).card = 410 := join_1_0

end S192C06
end Sude.GeneratedTwinScan
