import Sude.FastTwinScan.B00
import Sude.FastTwinScan.B01
import Sude.FastTwinScan.B02
import Sude.FastTwinScan.B03
import Sude.FastTwinScan.B04
import Sude.FastTwinScan.B05
import Sude.FastTwinScan.B06
import Sude.FastTwinScan.B07
import Sude.FastTwinScan.B08
import Sude.FastTwinScan.B09
import Sude.FastTwinScan.B10
import Sude.FastTwinScan.B11
import Sude.FastTwinScan.B12
import Sude.FastTwinScan.B13
import Sude.FastTwinScan.B14
import Sude.FastTwinScan.B15
import Sude.FastTwinScan.B16
import Sude.FastTwinScan.B17
import Sude.FastTwinScan.B18
import Sude.FastTwinScan.B19
import Sude.FastTwinScan.B20
import Sude.FastTwinScan.B21
import Sude.FastTwinScan.B22
import Sude.FastTwinScan.B23
import Sude.FastTwinScan.B24
import Sude.FastTwinScan.B25
import Sude.FastTwinScan.B26
import Sude.FastTwinScan.B27
import Sude.FastTwinScan.B28
import Sude.FastTwinScan.B29
import Sude.FastTwinScan.B30
import Sude.FastTwinScan.B31
import Sude.FastTwinScan.B32
import Sude.FastTwinScan.B33
import Sude.FastTwinScan.B34
import Sude.FastTwinScan.B35
import Sude.FastTwinScan.B36
import Sude.FastTwinScan.B37
import Sude.FastTwinScan.B38
import Sude.FastTwinScan.B39
import Sude.FastTwinScan.B40
import Sude.FastTwinScan.B41
import Sude.FastTwinScan.B42
import Sude.FastTwinScan.B43
import Sude.FastTwinScan.B44
import Sude.FastTwinScan.B45
import Sude.FastTwinScan.B46
import Sude.FastTwinScan.B47
import Sude.FastTwinScan.B48
import Sude.FastTwinScan.B49
import Sude.FastTwinScan.B50
import Sude.FastTwinScan.B51
import Sude.FastTwinScan.B52
import Sude.FastTwinScan.B53
import Sude.FastTwinScan.B54
import Sude.FastTwinScan.B55
import Sude.FastTwinScan.B56
import Sude.FastTwinScan.B57
import Sude.FastTwinScan.B58
import Sude.FastTwinScan.B59
import Sude.FastTwinScan.B60
import Sude.FastTwinScan.B61
import Sude.FastTwinScan.B62
import Sude.FastTwinScan.B63
import Sude.FastTwinScan.B64
import Sude.FastTwinScan.B65
import Sude.FastTwinScan.B66
import Sude.FastTwinScan.B67
import Sude.FastTwinScan.B68
import Sude.FastTwinScan.B69
import Sude.FastTwinScan.B70
import Sude.FastTwinScan.B71

/-! Combine the 72 fast twin-prime scan blocks (S000..S287) to establish
`2168112 ≤ finiteTwinSeeds.card` for the first FW band (`19485 ≤ n ≤ 21248`). -/
namespace Sude
noncomputable section

set_option autoImplicit false

theorem fastTwinJoin_0_0 : (twinPrimeSegment 45 16777261).card = 92240 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 8388653) (by decide : 8388653 ≤ 16777261) FastTwinScan.B00.total FastTwinScan.B01.total

theorem fastTwinJoin_0_1 : (twinPrimeSegment 16777261 33554477).card = 76371 := by
  simpa using combineTwinPrimeSegments (by decide : 16777261 ≤ 25165869) (by decide : 25165869 ≤ 33554477) FastTwinScan.B02.total FastTwinScan.B03.total

theorem fastTwinJoin_0_2 : (twinPrimeSegment 33554477 50331693).card = 71804 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 41943085) (by decide : 41943085 ≤ 50331693) FastTwinScan.B04.total FastTwinScan.B05.total

theorem fastTwinJoin_0_3 : (twinPrimeSegment 50331693 67108909).card = 69140 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 58720301) (by decide : 58720301 ≤ 67108909) FastTwinScan.B06.total FastTwinScan.B07.total

theorem fastTwinJoin_0_4 : (twinPrimeSegment 67108909 83886125).card = 67353 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 75497517) (by decide : 75497517 ≤ 83886125) FastTwinScan.B08.total FastTwinScan.B09.total

theorem fastTwinJoin_0_5 : (twinPrimeSegment 83886125 100663341).card = 65999 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 92274733) (by decide : 92274733 ≤ 100663341) FastTwinScan.B10.total FastTwinScan.B11.total

theorem fastTwinJoin_0_6 : (twinPrimeSegment 100663341 117440557).card = 64754 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 109051949) (by decide : 109051949 ≤ 117440557) FastTwinScan.B12.total FastTwinScan.B13.total

theorem fastTwinJoin_0_7 : (twinPrimeSegment 117440557 134217773).card = 63646 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 125829165) (by decide : 125829165 ≤ 134217773) FastTwinScan.B14.total FastTwinScan.B15.total

theorem fastTwinJoin_0_8 : (twinPrimeSegment 134217773 150994989).card = 62743 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 142606381) (by decide : 142606381 ≤ 150994989) FastTwinScan.B16.total FastTwinScan.B17.total

theorem fastTwinJoin_0_9 : (twinPrimeSegment 150994989 167772205).card = 61880 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 159383597) (by decide : 159383597 ≤ 167772205) FastTwinScan.B18.total FastTwinScan.B19.total

theorem fastTwinJoin_0_10 : (twinPrimeSegment 167772205 184549421).card = 61183 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 176160813) (by decide : 176160813 ≤ 184549421) FastTwinScan.B20.total FastTwinScan.B21.total

theorem fastTwinJoin_0_11 : (twinPrimeSegment 184549421 201326637).card = 61030 := by
  simpa using combineTwinPrimeSegments (by decide : 184549421 ≤ 192938029) (by decide : 192938029 ≤ 201326637) FastTwinScan.B22.total FastTwinScan.B23.total

theorem fastTwinJoin_0_12 : (twinPrimeSegment 201326637 218103853).card = 60127 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 209715245) (by decide : 209715245 ≤ 218103853) FastTwinScan.B24.total FastTwinScan.B25.total

theorem fastTwinJoin_0_13 : (twinPrimeSegment 218103853 234881069).card = 59506 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 226492461) (by decide : 226492461 ≤ 234881069) FastTwinScan.B26.total FastTwinScan.B27.total

theorem fastTwinJoin_0_14 : (twinPrimeSegment 234881069 251658285).card = 59523 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 243269677) (by decide : 243269677 ≤ 251658285) FastTwinScan.B28.total FastTwinScan.B29.total

theorem fastTwinJoin_0_15 : (twinPrimeSegment 251658285 268435501).card = 58976 := by
  simpa using combineTwinPrimeSegments (by decide : 251658285 ≤ 260046893) (by decide : 260046893 ≤ 268435501) FastTwinScan.B30.total FastTwinScan.B31.total

theorem fastTwinJoin_0_16 : (twinPrimeSegment 268435501 285212717).card = 58680 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 276824109) (by decide : 276824109 ≤ 285212717) FastTwinScan.B32.total FastTwinScan.B33.total

theorem fastTwinJoin_0_17 : (twinPrimeSegment 285212717 301989933).card = 58376 := by
  simpa using combineTwinPrimeSegments (by decide : 285212717 ≤ 293601325) (by decide : 293601325 ≤ 301989933) FastTwinScan.B34.total FastTwinScan.B35.total

theorem fastTwinJoin_0_18 : (twinPrimeSegment 301989933 318767149).card = 58061 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 310378541) (by decide : 310378541 ≤ 318767149) FastTwinScan.B36.total FastTwinScan.B37.total

theorem fastTwinJoin_0_19 : (twinPrimeSegment 318767149 335544365).card = 57795 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 327155757) (by decide : 327155757 ≤ 335544365) FastTwinScan.B38.total FastTwinScan.B39.total

theorem fastTwinJoin_0_20 : (twinPrimeSegment 335544365 352321581).card = 57183 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 343932973) (by decide : 343932973 ≤ 352321581) FastTwinScan.B40.total FastTwinScan.B41.total

theorem fastTwinJoin_0_21 : (twinPrimeSegment 352321581 369098797).card = 56864 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 360710189) (by decide : 360710189 ≤ 369098797) FastTwinScan.B42.total FastTwinScan.B43.total

theorem fastTwinJoin_0_22 : (twinPrimeSegment 369098797 385876013).card = 56985 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 377487405) (by decide : 377487405 ≤ 385876013) FastTwinScan.B44.total FastTwinScan.B45.total

theorem fastTwinJoin_0_23 : (twinPrimeSegment 385876013 402653229).card = 56420 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 394264621) (by decide : 394264621 ≤ 402653229) FastTwinScan.B46.total FastTwinScan.B47.total

theorem fastTwinJoin_0_24 : (twinPrimeSegment 402653229 419430445).card = 56302 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 411041837) (by decide : 411041837 ≤ 419430445) FastTwinScan.B48.total FastTwinScan.B49.total

theorem fastTwinJoin_0_25 : (twinPrimeSegment 419430445 436207661).card = 56163 := by
  simpa using combineTwinPrimeSegments (by decide : 419430445 ≤ 427819053) (by decide : 427819053 ≤ 436207661) FastTwinScan.B50.total FastTwinScan.B51.total

theorem fastTwinJoin_0_26 : (twinPrimeSegment 436207661 452984877).card = 55945 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 444596269) (by decide : 444596269 ≤ 452984877) FastTwinScan.B52.total FastTwinScan.B53.total

theorem fastTwinJoin_0_27 : (twinPrimeSegment 452984877 469762093).card = 55552 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 461373485) (by decide : 461373485 ≤ 469762093) FastTwinScan.B54.total FastTwinScan.B55.total

theorem fastTwinJoin_0_28 : (twinPrimeSegment 469762093 486539309).card = 55319 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 478150701) (by decide : 478150701 ≤ 486539309) FastTwinScan.B56.total FastTwinScan.B57.total

theorem fastTwinJoin_0_29 : (twinPrimeSegment 486539309 503316525).card = 55034 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 494927917) (by decide : 494927917 ≤ 503316525) FastTwinScan.B58.total FastTwinScan.B59.total

theorem fastTwinJoin_0_30 : (twinPrimeSegment 503316525 520093741).card = 55106 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 511705133) (by decide : 511705133 ≤ 520093741) FastTwinScan.B60.total FastTwinScan.B61.total

theorem fastTwinJoin_0_31 : (twinPrimeSegment 520093741 536870957).card = 55014 := by
  simpa using combineTwinPrimeSegments (by decide : 520093741 ≤ 528482349) (by decide : 528482349 ≤ 536870957) FastTwinScan.B62.total FastTwinScan.B63.total

theorem fastTwinJoin_0_32 : (twinPrimeSegment 536870957 553648173).card = 54811 := by
  simpa using combineTwinPrimeSegments (by decide : 536870957 ≤ 545259565) (by decide : 545259565 ≤ 553648173) FastTwinScan.B64.total FastTwinScan.B65.total

theorem fastTwinJoin_0_33 : (twinPrimeSegment 553648173 570425389).card = 54614 := by
  simpa using combineTwinPrimeSegments (by decide : 553648173 ≤ 562036781) (by decide : 562036781 ≤ 570425389) FastTwinScan.B66.total FastTwinScan.B67.total

theorem fastTwinJoin_0_34 : (twinPrimeSegment 570425389 587202605).card = 54391 := by
  simpa using combineTwinPrimeSegments (by decide : 570425389 ≤ 578813997) (by decide : 578813997 ≤ 587202605) FastTwinScan.B68.total FastTwinScan.B69.total

theorem fastTwinJoin_0_35 : (twinPrimeSegment 587202605 603979821).card = 54392 := by
  simpa using combineTwinPrimeSegments (by decide : 587202605 ≤ 595591213) (by decide : 595591213 ≤ 603979821) FastTwinScan.B70.total FastTwinScan.B71.total

theorem fastTwinJoin_1_0 : (twinPrimeSegment 45 33554477).card = 168611 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 16777261) (by decide : 16777261 ≤ 33554477) fastTwinJoin_0_0 fastTwinJoin_0_1

theorem fastTwinJoin_1_1 : (twinPrimeSegment 33554477 67108909).card = 140944 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 50331693) (by decide : 50331693 ≤ 67108909) fastTwinJoin_0_2 fastTwinJoin_0_3

theorem fastTwinJoin_1_2 : (twinPrimeSegment 67108909 100663341).card = 133352 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 83886125) (by decide : 83886125 ≤ 100663341) fastTwinJoin_0_4 fastTwinJoin_0_5

theorem fastTwinJoin_1_3 : (twinPrimeSegment 100663341 134217773).card = 128400 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 117440557) (by decide : 117440557 ≤ 134217773) fastTwinJoin_0_6 fastTwinJoin_0_7

theorem fastTwinJoin_1_4 : (twinPrimeSegment 134217773 167772205).card = 124623 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 150994989) (by decide : 150994989 ≤ 167772205) fastTwinJoin_0_8 fastTwinJoin_0_9

theorem fastTwinJoin_1_5 : (twinPrimeSegment 167772205 201326637).card = 122213 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 184549421) (by decide : 184549421 ≤ 201326637) fastTwinJoin_0_10 fastTwinJoin_0_11

theorem fastTwinJoin_1_6 : (twinPrimeSegment 201326637 234881069).card = 119633 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 218103853) (by decide : 218103853 ≤ 234881069) fastTwinJoin_0_12 fastTwinJoin_0_13

theorem fastTwinJoin_1_7 : (twinPrimeSegment 234881069 268435501).card = 118499 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 251658285) (by decide : 251658285 ≤ 268435501) fastTwinJoin_0_14 fastTwinJoin_0_15

theorem fastTwinJoin_1_8 : (twinPrimeSegment 268435501 301989933).card = 117056 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 285212717) (by decide : 285212717 ≤ 301989933) fastTwinJoin_0_16 fastTwinJoin_0_17

theorem fastTwinJoin_1_9 : (twinPrimeSegment 301989933 335544365).card = 115856 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 318767149) (by decide : 318767149 ≤ 335544365) fastTwinJoin_0_18 fastTwinJoin_0_19

theorem fastTwinJoin_1_10 : (twinPrimeSegment 335544365 369098797).card = 114047 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 352321581) (by decide : 352321581 ≤ 369098797) fastTwinJoin_0_20 fastTwinJoin_0_21

theorem fastTwinJoin_1_11 : (twinPrimeSegment 369098797 402653229).card = 113405 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 385876013) (by decide : 385876013 ≤ 402653229) fastTwinJoin_0_22 fastTwinJoin_0_23

theorem fastTwinJoin_1_12 : (twinPrimeSegment 402653229 436207661).card = 112465 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 419430445) (by decide : 419430445 ≤ 436207661) fastTwinJoin_0_24 fastTwinJoin_0_25

theorem fastTwinJoin_1_13 : (twinPrimeSegment 436207661 469762093).card = 111497 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 452984877) (by decide : 452984877 ≤ 469762093) fastTwinJoin_0_26 fastTwinJoin_0_27

theorem fastTwinJoin_1_14 : (twinPrimeSegment 469762093 503316525).card = 110353 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 486539309) (by decide : 486539309 ≤ 503316525) fastTwinJoin_0_28 fastTwinJoin_0_29

theorem fastTwinJoin_1_15 : (twinPrimeSegment 503316525 536870957).card = 110120 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 520093741) (by decide : 520093741 ≤ 536870957) fastTwinJoin_0_30 fastTwinJoin_0_31

theorem fastTwinJoin_1_16 : (twinPrimeSegment 536870957 570425389).card = 109425 := by
  simpa using combineTwinPrimeSegments (by decide : 536870957 ≤ 553648173) (by decide : 553648173 ≤ 570425389) fastTwinJoin_0_32 fastTwinJoin_0_33

theorem fastTwinJoin_1_17 : (twinPrimeSegment 570425389 603979821).card = 108783 := by
  simpa using combineTwinPrimeSegments (by decide : 570425389 ≤ 587202605) (by decide : 587202605 ≤ 603979821) fastTwinJoin_0_34 fastTwinJoin_0_35

theorem fastTwinJoin_2_0 : (twinPrimeSegment 45 67108909).card = 309555 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 33554477) (by decide : 33554477 ≤ 67108909) fastTwinJoin_1_0 fastTwinJoin_1_1

theorem fastTwinJoin_2_1 : (twinPrimeSegment 67108909 134217773).card = 261752 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 100663341) (by decide : 100663341 ≤ 134217773) fastTwinJoin_1_2 fastTwinJoin_1_3

theorem fastTwinJoin_2_2 : (twinPrimeSegment 134217773 201326637).card = 246836 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 167772205) (by decide : 167772205 ≤ 201326637) fastTwinJoin_1_4 fastTwinJoin_1_5

theorem fastTwinJoin_2_3 : (twinPrimeSegment 201326637 268435501).card = 238132 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 234881069) (by decide : 234881069 ≤ 268435501) fastTwinJoin_1_6 fastTwinJoin_1_7

theorem fastTwinJoin_2_4 : (twinPrimeSegment 268435501 335544365).card = 232912 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 301989933) (by decide : 301989933 ≤ 335544365) fastTwinJoin_1_8 fastTwinJoin_1_9

theorem fastTwinJoin_2_5 : (twinPrimeSegment 335544365 402653229).card = 227452 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 369098797) (by decide : 369098797 ≤ 402653229) fastTwinJoin_1_10 fastTwinJoin_1_11

theorem fastTwinJoin_2_6 : (twinPrimeSegment 402653229 469762093).card = 223962 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 436207661) (by decide : 436207661 ≤ 469762093) fastTwinJoin_1_12 fastTwinJoin_1_13

theorem fastTwinJoin_2_7 : (twinPrimeSegment 469762093 536870957).card = 220473 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 503316525) (by decide : 503316525 ≤ 536870957) fastTwinJoin_1_14 fastTwinJoin_1_15

theorem fastTwinJoin_2_8 : (twinPrimeSegment 536870957 603979821).card = 218208 := by
  simpa using combineTwinPrimeSegments (by decide : 536870957 ≤ 570425389) (by decide : 570425389 ≤ 603979821) fastTwinJoin_1_16 fastTwinJoin_1_17

theorem fastTwinJoin_3_0 : (twinPrimeSegment 45 134217773).card = 571307 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 67108909) (by decide : 67108909 ≤ 134217773) fastTwinJoin_2_0 fastTwinJoin_2_1

theorem fastTwinJoin_3_1 : (twinPrimeSegment 134217773 268435501).card = 484968 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 201326637) (by decide : 201326637 ≤ 268435501) fastTwinJoin_2_2 fastTwinJoin_2_3

theorem fastTwinJoin_3_2 : (twinPrimeSegment 268435501 402653229).card = 460364 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 335544365) (by decide : 335544365 ≤ 402653229) fastTwinJoin_2_4 fastTwinJoin_2_5

theorem fastTwinJoin_3_3 : (twinPrimeSegment 402653229 536870957).card = 444435 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 469762093) (by decide : 469762093 ≤ 536870957) fastTwinJoin_2_6 fastTwinJoin_2_7

theorem fastTwinJoin_4_0 : (twinPrimeSegment 45 268435501).card = 1056275 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 134217773) (by decide : 134217773 ≤ 268435501) fastTwinJoin_3_0 fastTwinJoin_3_1

theorem fastTwinJoin_4_1 : (twinPrimeSegment 268435501 536870957).card = 904799 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 402653229) (by decide : 402653229 ≤ 536870957) fastTwinJoin_3_2 fastTwinJoin_3_3

theorem fastTwinJoin_5_0 : (twinPrimeSegment 45 536870957).card = 1961074 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 268435501) (by decide : 268435501 ≤ 536870957) fastTwinJoin_4_0 fastTwinJoin_4_1

theorem fastTwinJoin_6_0 : (twinPrimeSegment 45 603979821).card = 2179282 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 536870957) (by decide : 536870957 ≤ 603979821) fastTwinJoin_5_0 fastTwinJoin_2_8

/-- The first 288 segments `[45, 603979821)` contain `2179282` twin-prime lower endpoints. -/
theorem finiteTwinFirst288Segments : (twinPrimeSegment 45 603979821).card = 2179282 := fastTwinJoin_6_0

/-- The finite twin-prime seed pool contains at least `2,168,112` twin-prime pairs,
discharging the first-band seed supply hypothesis `2168112 ≤ finiteTwinSeeds.card`. -/
theorem finiteTwinSeeds_at_least_2168112 : 2168112 ≤ finiteTwinSeeds.card := by
  have hsub : twinPrimeSegment 45 603979821 ⊆ finiteTwinSeeds := by
    intro p hp
    simp only [twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
    exact (mem_finiteTwinSeeds p).mpr ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
  have hcard := Finset.card_le_card hsub
  rw [finiteTwinFirst288Segments] at hcard
  omega

end
end Sude
