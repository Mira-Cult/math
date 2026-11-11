import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S153C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17920)) 321126445 321159213 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 321126445 321159213).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17920 321126445 321159213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17921)) 321159213 321191981 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 321159213 321191981).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17921 321159213 321191981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17922)) 321191981 321224749 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 321191981 321224749).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17922 321191981 321224749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17923)) 321224749 321257517 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 321224749 321257517).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17923 321224749 321257517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 321126445 321191981).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 321126445 ≤ 321159213)
    (by decide : 321159213 ≤ 321191981) block0 block1

theorem join_0_1 : (twinPrimeSegment 321191981 321257517).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 321191981 ≤ 321224749)
    (by decide : 321224749 ≤ 321257517) block2 block3

theorem join_1_0 : (twinPrimeSegment 321126445 321257517).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 321126445 ≤ 321191981)
    (by decide : 321191981 ≤ 321257517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 321126445 321257517).card = 443 := join_1_0

end S153C02
end Sude.GeneratedTwinScan
