import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13184)) 173801517 173834285 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 173801517 173834285).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13184 173801517 173834285
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13185)) 173834285 173867053 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 173834285 173867053).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13185 173834285 173867053
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13187)) 173867053 173899821 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 173867053 173899821).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13187 173867053 173899821
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13188)) 173899821 173932589 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 173899821 173932589).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13188 173899821 173932589
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 173801517 173867053).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 173801517 ≤ 173834285)
    (by decide : 173834285 ≤ 173867053) block0 block1

theorem join_0_1 : (twinPrimeSegment 173867053 173932589).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 173867053 ≤ 173899821)
    (by decide : 173899821 ≤ 173932589) block2 block3

theorem join_1_0 : (twinPrimeSegment 173801517 173932589).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 173801517 ≤ 173867053)
    (by decide : 173867053 ≤ 173932589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 173801517 173932589).card = 446 := join_1_0

end S082C14
end Sude.GeneratedTwinScan
