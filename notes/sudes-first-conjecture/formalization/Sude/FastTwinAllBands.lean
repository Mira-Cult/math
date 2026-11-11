import Sude.FastTwinFirstBand
import Sude.FastTwinScan.B72
import Sude.FastTwinScan.B73
import Sude.FastTwinScan.B74
import Sude.FastTwinScan.B75
import Sude.FastTwinScan.B76
import Sude.FastTwinScan.B77
import Sude.FastTwinScan.B78
import Sude.FastTwinScan.B79
import Sude.FastTwinScan.B80
import Sude.FastTwinScan.B81
import Sude.FastTwinScan.B82
import Sude.FastTwinScan.B83
import Sude.FastTwinScan.B84
import Sude.FastTwinScan.B85
import Sude.FastTwinScan.B86
import Sude.FastTwinScan.B87
import Sude.FastTwinScan.B88
import Sude.FastTwinScan.B89
import Sude.FastTwinScan.B90
import Sude.FastTwinScan.B91
import Sude.FastTwinScan.B92
import Sude.FastTwinScan.B93
import Sude.FastTwinScan.B94
import Sude.FastTwinScan.B95

/-! Combine FastTwinFirstBand (S000..S287) with B72..B95 (S288..S383) to establish
`2811426 ≤ finiteTwinSeeds.card` across all four FW bands (`19485 ≤ n ≤ 27553`). -/
namespace Sude
noncomputable section

set_option autoImplicit false

theorem fastTwinTailJoin_0_0 : (twinPrimeSegment 603979821 620757037).card = 54135 := by
  simpa using combineTwinPrimeSegments (by decide : 603979821 ≤ 612368429) (by decide : 612368429 ≤ 620757037) FastTwinScan.B72.total FastTwinScan.B73.total

theorem fastTwinTailJoin_0_1 : (twinPrimeSegment 620757037 637534253).card = 53942 := by
  simpa using combineTwinPrimeSegments (by decide : 620757037 ≤ 629145645) (by decide : 629145645 ≤ 637534253) FastTwinScan.B74.total FastTwinScan.B75.total

theorem fastTwinTailJoin_0_2 : (twinPrimeSegment 637534253 654311469).card = 53664 := by
  simpa using combineTwinPrimeSegments (by decide : 637534253 ≤ 645922861) (by decide : 645922861 ≤ 654311469) FastTwinScan.B76.total FastTwinScan.B77.total

theorem fastTwinTailJoin_0_3 : (twinPrimeSegment 654311469 671088685).card = 53740 := by
  simpa using combineTwinPrimeSegments (by decide : 654311469 ≤ 662700077) (by decide : 662700077 ≤ 671088685) FastTwinScan.B78.total FastTwinScan.B79.total

theorem fastTwinTailJoin_0_4 : (twinPrimeSegment 671088685 687865901).card = 53537 := by
  simpa using combineTwinPrimeSegments (by decide : 671088685 ≤ 679477293) (by decide : 679477293 ≤ 687865901) FastTwinScan.B80.total FastTwinScan.B81.total

theorem fastTwinTailJoin_0_5 : (twinPrimeSegment 687865901 704643117).card = 53355 := by
  simpa using combineTwinPrimeSegments (by decide : 687865901 ≤ 696254509) (by decide : 696254509 ≤ 704643117) FastTwinScan.B82.total FastTwinScan.B83.total

theorem fastTwinTailJoin_0_6 : (twinPrimeSegment 704643117 721420333).card = 53512 := by
  simpa using combineTwinPrimeSegments (by decide : 704643117 ≤ 713031725) (by decide : 713031725 ≤ 721420333) FastTwinScan.B84.total FastTwinScan.B85.total

theorem fastTwinTailJoin_0_7 : (twinPrimeSegment 721420333 738197549).card = 53221 := by
  simpa using combineTwinPrimeSegments (by decide : 721420333 ≤ 729808941) (by decide : 729808941 ≤ 738197549) FastTwinScan.B86.total FastTwinScan.B87.total

theorem fastTwinTailJoin_0_8 : (twinPrimeSegment 738197549 754974765).card = 52927 := by
  simpa using combineTwinPrimeSegments (by decide : 738197549 ≤ 746586157) (by decide : 746586157 ≤ 754974765) FastTwinScan.B88.total FastTwinScan.B89.total

theorem fastTwinTailJoin_0_9 : (twinPrimeSegment 754974765 771751981).card = 52708 := by
  simpa using combineTwinPrimeSegments (by decide : 754974765 ≤ 763363373) (by decide : 763363373 ≤ 771751981) FastTwinScan.B90.total FastTwinScan.B91.total

theorem fastTwinTailJoin_0_10 : (twinPrimeSegment 771751981 788529197).card = 52694 := by
  simpa using combineTwinPrimeSegments (by decide : 771751981 ≤ 780140589) (by decide : 780140589 ≤ 788529197) FastTwinScan.B92.total FastTwinScan.B93.total

theorem fastTwinTailJoin_0_11 : (twinPrimeSegment 788529197 805306413).card = 52658 := by
  simpa using combineTwinPrimeSegments (by decide : 788529197 ≤ 796917805) (by decide : 796917805 ≤ 805306413) FastTwinScan.B94.total FastTwinScan.B95.total

theorem fastTwinTailJoin_1_0 : (twinPrimeSegment 603979821 637534253).card = 108077 := by
  simpa using combineTwinPrimeSegments (by decide : 603979821 ≤ 620757037) (by decide : 620757037 ≤ 637534253) fastTwinTailJoin_0_0 fastTwinTailJoin_0_1

theorem fastTwinTailJoin_1_1 : (twinPrimeSegment 637534253 671088685).card = 107404 := by
  simpa using combineTwinPrimeSegments (by decide : 637534253 ≤ 654311469) (by decide : 654311469 ≤ 671088685) fastTwinTailJoin_0_2 fastTwinTailJoin_0_3

theorem fastTwinTailJoin_1_2 : (twinPrimeSegment 671088685 704643117).card = 106892 := by
  simpa using combineTwinPrimeSegments (by decide : 671088685 ≤ 687865901) (by decide : 687865901 ≤ 704643117) fastTwinTailJoin_0_4 fastTwinTailJoin_0_5

theorem fastTwinTailJoin_1_3 : (twinPrimeSegment 704643117 738197549).card = 106733 := by
  simpa using combineTwinPrimeSegments (by decide : 704643117 ≤ 721420333) (by decide : 721420333 ≤ 738197549) fastTwinTailJoin_0_6 fastTwinTailJoin_0_7

theorem fastTwinTailJoin_1_4 : (twinPrimeSegment 738197549 771751981).card = 105635 := by
  simpa using combineTwinPrimeSegments (by decide : 738197549 ≤ 754974765) (by decide : 754974765 ≤ 771751981) fastTwinTailJoin_0_8 fastTwinTailJoin_0_9

theorem fastTwinTailJoin_1_5 : (twinPrimeSegment 771751981 805306413).card = 105352 := by
  simpa using combineTwinPrimeSegments (by decide : 771751981 ≤ 788529197) (by decide : 788529197 ≤ 805306413) fastTwinTailJoin_0_10 fastTwinTailJoin_0_11

theorem fastTwinTailJoin_2_0 : (twinPrimeSegment 603979821 671088685).card = 215481 := by
  simpa using combineTwinPrimeSegments (by decide : 603979821 ≤ 637534253) (by decide : 637534253 ≤ 671088685) fastTwinTailJoin_1_0 fastTwinTailJoin_1_1

theorem fastTwinTailJoin_2_1 : (twinPrimeSegment 671088685 738197549).card = 213625 := by
  simpa using combineTwinPrimeSegments (by decide : 671088685 ≤ 704643117) (by decide : 704643117 ≤ 738197549) fastTwinTailJoin_1_2 fastTwinTailJoin_1_3

theorem fastTwinTailJoin_2_2 : (twinPrimeSegment 738197549 805306413).card = 210987 := by
  simpa using combineTwinPrimeSegments (by decide : 738197549 ≤ 771751981) (by decide : 771751981 ≤ 805306413) fastTwinTailJoin_1_4 fastTwinTailJoin_1_5

theorem fastTwinTailJoin_3_0 : (twinPrimeSegment 603979821 738197549).card = 429106 := by
  simpa using combineTwinPrimeSegments (by decide : 603979821 ≤ 671088685) (by decide : 671088685 ≤ 738197549) fastTwinTailJoin_2_0 fastTwinTailJoin_2_1

theorem fastTwinTailJoin_4_0 : (twinPrimeSegment 603979821 805306413).card = 640093 := by
  simpa using combineTwinPrimeSegments (by decide : 603979821 ≤ 738197549) (by decide : 738197549 ≤ 805306413) fastTwinTailJoin_3_0 fastTwinTailJoin_2_2

/-- The first 384 segments `[45, 805306413)` contain `2819375` twin-prime lower endpoints. -/
theorem finiteTwinFirst384Segments : (twinPrimeSegment 45 805306413).card = 2819375 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 603979821) (by decide : 603979821 ≤ 805306413) finiteTwinFirst288Segments fastTwinTailJoin_4_0

/-- The finite twin-prime seed pool contains at least `2,811,426` twin-prime pairs,
discharging the full FW four-band seed supply hypothesis `2811426 ≤ finiteTwinSeeds.card`. -/
theorem finiteTwinSeeds_at_least_2811426 : 2811426 ≤ finiteTwinSeeds.card := by
  have hsub : twinPrimeSegment 45 805306413 ⊆ finiteTwinSeeds := by
    intro p hp
    simp only [twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
    exact (mem_finiteTwinSeeds p).mpr ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
  have hcard := Finset.card_le_card hsub
  rw [finiteTwinFirst384Segments] at hcard
  omega

end
end Sude
