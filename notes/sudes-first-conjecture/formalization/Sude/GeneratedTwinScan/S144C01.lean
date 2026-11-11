import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17382)) 302121005 302153773 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 302121005 302153773).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17382 302121005 302153773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17383)) 302153773 302186541 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302153773 302186541).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17383 302153773 302186541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17384)) 302186541 302219309 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302186541 302219309).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17384 302186541 302219309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17385)) 302219309 302252077 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 302219309 302252077).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17385 302219309 302252077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 302121005 302186541).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 302121005 ≤ 302153773)
    (by decide : 302153773 ≤ 302186541) block0 block1

theorem join_0_1 : (twinPrimeSegment 302186541 302252077).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 302186541 ≤ 302219309)
    (by decide : 302219309 ≤ 302252077) block2 block3

theorem join_1_0 : (twinPrimeSegment 302121005 302252077).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 302121005 ≤ 302186541)
    (by decide : 302186541 ≤ 302252077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 302121005 302252077).card = 483 := join_1_0

end S144C01
end Sude.GeneratedTwinScan
