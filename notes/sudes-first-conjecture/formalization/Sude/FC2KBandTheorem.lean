import Sude.FC2KSubbandDischarge
import Sude.FC2KPrefixCert0
import Sude.FC2KPrefixCert1
import Sude.FC2KPrefixCert2
import Sude.FC2KPrefixCert3
import Sude.FC2KPrefixCert4
import Sude.FC2KPrefixCert5
import Sude.FC2KPrefixCert6
import Sude.FC2KPrefixCert7
import Sude.FC2KPrefixCert8

/-!
# FC2K Band Theorem (`2001 ≤ n ≤ 19483`, Odd `n`)

Assembles `fc2kPrefixProfile0` .. `fc2kPrefixProfile8` and the 21 kernel-checked
sub-band parameter records `fc2kSpecB00` .. `fc2kSpecB20` via `fc2k_hasSquare_of_spec`
to prove `HasSquare n` for every odd `n` in `2001 ≤ n ≤ 19483`.
-/

namespace Sude

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000

/-- Sub-band B00: `2001 ≤ n ≤ 2031` (Prefix Cert 0). -/
def fc2kSpecB00 : FC2KSubbandSpec where
  n_lo := 2001
  n_hi := 2031
  J_max := 1
  W_ord := 15
  W_diag := 0
  N_bins := 18
  δ := 43 / 10000
  ε := 31 / 1000
  c_lo := 4417 / 10000
  c_hi := 1433 / 2500
  a_X := 3329
  S_lo_up := 8219
  X_lo := 67542259
  b_X := 3337
  a_Xh := 3336
  S_hi_up := 8380
  X_hi := 70215337
  S_lo := 8218
  c_W := 91073 / 500000000
  c_N := 13003 / 2000
  c_B := 800749 / 250000
  brStages := [
    { M := 1027, wLow := .wordCap 0 1 20857, wHigh := .aboveMaxHi }
  ]
  wHalf := .wordCap 0 1 0
  wFull := .wordCap 0 4 0

private theorem fc2kSpecB00_valid :
    checkFC2KSubbandSpec 25 13122 6191285 44530357
      (planTotalSpanWords fc2kSubCerts0 fc2kPlan0)
      fc2kPlan0.windowCaps fc2kPlan0.octWindowCaps fc2kSpecB00 = true := by
  decide +kernel

/-- Sub-band B01: `2033 ≤ n ≤ 2079` (Prefix Cert 0). -/
def fc2kSpecB01 : FC2KSubbandSpec where
  n_lo := 2033
  n_hi := 2079
  J_max := 1
  W_ord := 15
  W_diag := 0
  N_bins := 13
  δ := 11 / 2000
  ε := 31 / 1000
  c_lo := 4467 / 10000
  c_hi := 5723 / 10000
  a_X := 3335
  S_lo_up := 8358
  X_lo := 69855867
  b_X := 3346
  a_Xh := 3345
  S_hi_up := 8590
  X_hi := 73783575
  S_lo := 8357
  c_W := 248809 / 1000000000
  c_N := 659 / 100
  c_B := 3251367 / 1000000
  brStages := [
    { M := 1053, wLow := .wordCap 0 1 0, wHigh := .aboveMaxHi }
  ]
  wHalf := .wordCap 1 1 0
  wFull := .wordCap 1 4 0

private theorem fc2kSpecB01_valid :
    checkFC2KSubbandSpec 25 13122 6191285 44530357
      (planTotalSpanWords fc2kSubCerts0 fc2kPlan0)
      fc2kPlan0.windowCaps fc2kPlan0.octWindowCaps fc2kSpecB01 = true := by
  decide +kernel

/-- Sub-band B02: `2081 ≤ n ≤ 2179` (Prefix Cert 0). -/
def fc2kSpecB02 : FC2KSubbandSpec where
  n_lo := 2081
  n_hi := 2179
  J_max := 1
  W_ord := 16
  W_diag := 0
  N_bins := 12
  δ := 3 / 500
  ε := 29 / 1000
  c_lo := 4531 / 10000
  c_hi := 2861 / 5000
  a_X := 3344
  S_lo_up := 8568
  X_lo := 73407241
  b_X := 3364
  a_Xh := 3363
  S_hi_up := 9029
  X_hi := 81513988
  S_lo := 8567
  c_W := 13813 / 50000000
  c_N := 1747 / 250
  c_B := 648017 / 200000
  brStages := [
    { M := 1106, wLow := .wordCap 2 1 29171, wHigh := .aboveMaxHi }
  ]
  wHalf := .wordCap 5 1 0
  wFull := .wordCap 6 1 0

private theorem fc2kSpecB02_valid :
    checkFC2KSubbandSpec 25 13122 6191285 44530357
      (planTotalSpanWords fc2kSubCerts0 fc2kPlan0)
      fc2kPlan0.windowCaps fc2kPlan0.octWindowCaps fc2kSpecB02 = true := by
  decide +kernel

/-- Sub-band B03: `2181 ≤ n ≤ 2349` (Prefix Cert 1). -/
def fc2kSpecB03 : FC2KSubbandSpec where
  n_lo := 2181
  n_hi := 2349
  J_max := 1
  W_ord := 18
  W_diag := 0
  N_bins := 11
  δ := 7 / 1000
  ε := 17 / 500
  c_lo := 256 / 625
  c_hi := 5661 / 10000
  a_X := 3363
  S_lo_up := 9008
  X_lo := 81127207
  b_X := 3394
  a_Xh := 3393
  S_hi_up := 9779
  X_hi := 95623922
  S_lo := 9007
  c_W := 165399 / 500000000
  c_N := 7709 / 1000
  c_B := 922041 / 250000
  brStages := [
    { M := 1198, wLow := .octCap 0 1 0, wHigh := .octCap 6 1 0 }
  ]
  wHalf := .octCap 1 1 0
  wFull := .octCap 1 4 0

private theorem fc2kSpecB03_valid :
    checkFC2KSubbandSpec 25 15342 8628221 69036061
      (planTotalSpanWords fc2kSubCerts1 fc2kPlan1)
      fc2kPlan1.windowCaps fc2kPlan1.octWindowCaps fc2kSpecB03 = true := by
  decide +kernel

/-- Sub-band B04: `2351 ≤ n ≤ 2549` (Prefix Cert 1). -/
def fc2kSpecB04 : FC2KSubbandSpec where
  n_lo := 2351
  n_hi := 2549
  J_max := 1
  W_ord := 17
  W_diag := 0
  N_bins := 13
  δ := 11 / 2000
  ε := 3 / 100
  c_lo := 1093 / 2500
  c_hi := 5609 / 10000
  a_X := 3392
  S_lo_up := 9755
  X_lo := 95145796
  b_X := 3426
  a_Xh := 3425
  S_hi_up := 10665
  X_hi := 113724550
  S_lo := 9754
  c_W := 50131 / 200000000
  c_N := 3701 / 500
  c_B := 3188077 / 1000000
  brStages := [
    { M := 1307, wLow := .octCap 1 1 0, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 2 1 0
  wFull := .octCap 3 1 0

private theorem fc2kSpecB04_valid :
    checkFC2KSubbandSpec 25 15342 8628221 69036061
      (planTotalSpanWords fc2kSubCerts1 fc2kPlan1)
      fc2kPlan1.windowCaps fc2kPlan1.octWindowCaps fc2kSpecB04 = true := by
  decide +kernel

/-- Sub-band B05: `2551 ≤ n ≤ 2749` (Prefix Cert 2). -/
def fc2kSpecB05 : FC2KSubbandSpec where
  n_lo := 2551
  n_hi := 2749
  J_max := 2
  W_ord := 22
  W_diag := 16
  N_bins := 10
  δ := 1 / 125
  ε := 11 / 200
  c_lo := 417 / 1000
  c_hi := 2763 / 5000
  a_X := 3424
  S_lo_up := 10638
  X_lo := 113163353
  b_X := 3455
  a_Xh := 3454
  S_hi_up := 11553
  X_hi := 133455874
  S_lo := 10637
  c_W := 385943 / 1000000000
  c_N := 1849 / 200
  c_B := 4017851 / 1000000
  brStages := [
    { M := 1415, wLow := .octCap 0 1 0, wHigh := .octCap 7 1 0 },
    { M := 1415, wLow := .octCap 0 1 0, wHigh := .octCap 7 1 0 }
  ]
  wHalf := .octCap 1 2 0
  wFull := .octCap 2 6 0

private theorem fc2kSpecB05_valid :
    checkFC2KSubbandSpec 25 18042 13856789 98447383
      (planTotalSpanWords fc2kSubCerts2 fc2kPlan2)
      fc2kPlan2.windowCaps fc2kPlan2.octWindowCaps fc2kSpecB05 = true := by
  decide +kernel

/-- Sub-band B06: `2751 ≤ n ≤ 2999` (Prefix Cert 2). -/
def fc2kSpecB06 : FC2KSubbandSpec where
  n_lo := 2751
  n_hi := 2999
  J_max := 2
  W_ord := 24
  W_diag := 16
  N_bins := 10
  δ := 1 / 125
  ε := 1 / 20
  c_lo := 4401 / 10000
  c_hi := 2751 / 5000
  a_X := 3454
  S_lo_up := 11526
  X_lo := 132846263
  b_X := 3490
  a_Xh := 3489
  S_hi_up := 12671
  X_hi := 160536235
  S_lo := 11525
  c_W := 385249 / 1000000000
  c_N := 251 / 25
  c_B := 3827719 / 1000000
  brStages := [
    { M := 1552, wLow := .octCap 2 1 0, wHigh := .octCap 5 1 0 },
    { M := 1552, wLow := .octCap 2 1 0, wHigh := .octCap 9 1 0 }
  ]
  wHalf := .octCap 3 2 0
  wFull := .octCap 4 2 0

private theorem fc2kSpecB06_valid :
    checkFC2KSubbandSpec 25 18042 13856789 98447383
      (planTotalSpanWords fc2kSubCerts2 fc2kPlan2)
      fc2kPlan2.windowCaps fc2kPlan2.octWindowCaps fc2kSpecB06 = true := by
  decide +kernel

/-- Sub-band B07: `3001 ≤ n ≤ 3349` (Prefix Cert 3). -/
def fc2kSpecB07 : FC2KSubbandSpec where
  n_lo := 3001
  n_hi := 3349
  J_max := 1
  W_ord := 25
  W_diag := 18
  N_bins := 12
  δ := 7 / 1000
  ε := 7 / 200
  c_lo := 4519 / 10000
  c_hi := 543 / 1000
  a_X := 3488
  S_lo_up := 12640
  X_lo := 159764505
  b_X := 3533
  a_Xh := 3532
  S_hi_up := 14241
  X_hi := 202803376
  S_lo := 12639
  c_W := 66321 / 200000000
  c_N := 827 / 80
  c_B := 363671 / 100000
  brStages := [
    { M := 1745, wLow := .octCap 0 1 0, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 1 1 0
  wFull := .octCap 1 4 0

private theorem fc2kSpecB07_valid :
    checkFC2KSubbandSpec 26 22242 22632281 107419483
      (planTotalSpanWords fc2kSubCerts3 fc2kPlan3)
      fc2kPlan3.windowCaps fc2kPlan3.octWindowCaps fc2kSpecB07 = true := by
  decide +kernel

/-- Sub-band B08: `3351 ≤ n ≤ 3699` (Prefix Cert 3). -/
def fc2kSpecB08 : FC2KSubbandSpec where
  n_lo := 3351
  n_hi := 3699
  J_max := 1
  W_ord := 28
  W_diag := 18
  N_bins := 12
  δ := 7 / 1000
  ε := 1 / 25
  c_lo := 589 / 1250
  c_hi := 1349 / 2500
  a_X := 3531
  S_lo_up := 14208
  X_lo := 201845285
  b_X := 3572
  a_Xh := 3571
  S_hi_up := 15821
  X_hi := 250296331
  S_lo := 14207
  c_W := 165863 / 500000000
  c_N := 5759 / 500
  c_B := 432649 / 125000
  brStages := [
    { M := 1938, wLow := .octCap 1 1 89296, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 4 1 0
  wFull := .octCap 5 1 0

private theorem fc2kSpecB08_valid :
    checkFC2KSubbandSpec 26 22242 22632281 107419483
      (planTotalSpanWords fc2kSubCerts3 fc2kPlan3)
      fc2kPlan3.windowCaps fc2kPlan3.octWindowCaps fc2kSpecB08 = true := by
  decide +kernel

/-- Sub-band B09: `3701 ≤ n ≤ 4199` (Prefix Cert 4). -/
def fc2kSpecB09 : FC2KSubbandSpec where
  n_lo := 3701
  n_hi := 4199
  J_max := 2
  W_ord := 31
  W_diag := 18
  N_bins := 12
  δ := 7 / 1000
  ε := 1 / 30
  c_lo := 4397 / 10000
  c_hi := 2659 / 5000
  a_X := 3570
  S_lo_up := 15784
  X_lo := 249132350
  b_X := 3621
  a_Xh := 3620
  S_hi_up := 18090
  X_hi := 327213089
  S_lo := 15783
  c_W := 330207 / 1000000000
  c_N := 25397 / 2000
  c_B := 3966923 / 1000000
  brStages := [
    { M := 2216, wLow := .octCap 1 1 103550, wHigh := .octCap 6 1 0 },
    { M := 2216, wLow := .octCap 1 1 103550, wHigh := .octCap 8 1 0 }
  ]
  wHalf := .octCap 1 1 0
  wFull := .octCap 1 4 0

private theorem fc2kSpecB09_valid :
    checkFC2KSubbandSpec 26 28842 39186893 208957903
      (planTotalSpanWords fc2kSubCerts4 fc2kPlan4)
      fc2kPlan4.windowCaps fc2kPlan4.octWindowCaps fc2kSpecB09 = true := by
  decide +kernel

/-- Sub-band B10: `4201 ≤ n ≤ 4799` (Prefix Cert 4). -/
def fc2kSpecB10 : FC2KSubbandSpec where
  n_lo := 4201
  n_hi := 4799
  J_max := 2
  W_ord := 35
  W_diag := 18
  N_bins := 12
  δ := 7 / 1000
  ε := 1 / 30
  c_lo := 2313 / 5000
  c_hi := 5293 / 10000
  a_X := 3619
  S_lo_up := 18048
  X_lo := 325720960
  b_X := 3673
  a_Xh := 3672
  S_hi_up := 20831
  X_hi := 433891760
  S_lo := 18047
  c_W := 65769 / 200000000
  c_N := 5709 / 400
  c_B := 3762753 / 1000000
  brStages := [
    { M := 2316, wLow := .octCap 1 1 0, wHigh := .aboveMaxHi },
    { M := 2552, wLow := .octCap 2 1 0, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 0 2 0
  wFull := .octCap 4 5 0

private theorem fc2kSpecB10_valid :
    checkFC2KSubbandSpec 26 28842 39186893 208957903
      (planTotalSpanWords fc2kSubCerts4 fc2kPlan4)
      fc2kPlan4.windowCaps fc2kPlan4.octWindowCaps fc2kSpecB10 = true := by
  decide +kernel

/-- Sub-band B11: `4801 ≤ n ≤ 5499` (Prefix Cert 5). -/
def fc2kSpecB11 : FC2KSubbandSpec where
  n_lo := 4801
  n_hi := 5499
  J_max := 2
  W_ord := 38
  W_diag := 20
  N_bins := 12
  δ := 7 / 1000
  ε := 1 / 30
  c_lo := 929 / 2000
  c_hi := 523 / 1000
  a_X := 3671
  S_lo_up := 20784
  X_lo := 431953794
  b_X := 3726
  a_Xh := 3725
  S_hi_up := 24050
  X_hi := 578383577
  S_lo := 20783
  c_W := 327163 / 1000000000
  c_N := 15453 / 1000
  c_B := 960173 / 200000
  brStages := [
    { M := 2946, wLow := .octCap 1 1 22357, wHigh := .aboveMaxHi },
    { M := 2946, wLow := .octCap 1 1 22357, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 4 1 0
  wFull := .octCap 5 1 0

private theorem fc2kSpecB11_valid :
    checkFC2KSubbandSpec 27 37842 69475637 276159799
      (planTotalSpanWords fc2kSubCerts5 fc2kPlan5)
      fc2kPlan5.windowCaps fc2kPlan5.octWindowCaps fc2kSpecB11 = true := by
  decide +kernel

/-- Sub-band B12: `5501 ≤ n ≤ 6299` (Prefix Cert 5). -/
def fc2kSpecB12 : FC2KSubbandSpec where
  n_lo := 5501
  n_hi := 6299
  J_max := 2
  W_ord := 42
  W_diag := 20
  N_bins := 14
  δ := 3 / 500
  ε := 1 / 30
  c_lo := 597 / 1250
  c_hi := 5207 / 10000
  a_X := 3724
  S_lo_up := 23997
  X_lo := 575854037
  b_X := 3779
  a_Xh := 3778
  S_hi_up := 27755
  X_hi := 770307208
  S_lo := 23996
  c_W := 138159 / 500000000
  c_N := 17027 / 1000
  c_B := 845219 / 200000
  brStages := [
    { M := 3283, wLow := .octCap 2 1 0, wHigh := .aboveMaxHi },
    { M := 3400, wLow := .octCap 0 2 0, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 6 1 0
  wFull := .octCap 7 1 0

private theorem fc2kSpecB12_valid :
    checkFC2KSubbandSpec 27 37842 69475637 276159799
      (planTotalSpanWords fc2kSubCerts5 fc2kPlan5)
      fc2kPlan5.windowCaps fc2kPlan5.octWindowCaps fc2kSpecB12 = true := by
  decide +kernel

/-- Sub-band B13: `6301 ≤ n ≤ 7299` (Prefix Cert 6). -/
def fc2kSpecB13 : FC2KSubbandSpec where
  n_lo := 6301
  n_hi := 7299
  J_max := 2
  W_ord := 46
  W_diag := 20
  N_bins := 14
  δ := 3 / 500
  ε := 1 / 30
  c_lo := 4701 / 10000
  c_hi := 5139 / 10000
  a_X := 3777
  S_lo_up := 27695
  X_lo := 767008122
  b_X := 3837
  a_Xh := 3836
  S_hi_up := 32420
  X_hi := 1051049026
  S_lo := 27694
  c_W := 274361 / 1000000000
  c_N := 18601 / 1000
  c_B := 6123423 / 1000000
  brStages := [
    { M := 3971, wLow := .octCap 0 1 0, wHigh := .aboveMaxHi },
    { M := 3971, wLow := .octCap 0 1 0, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 4 1 0
  wFull := .octCap 5 1 0

private theorem fc2kSpecB13_valid :
    checkFC2KSubbandSpec 28 55842 157529207 461091979
      (planTotalSpanWords fc2kSubCerts6 fc2kPlan6)
      fc2kPlan6.windowCaps fc2kPlan6.octWindowCaps fc2kSpecB13 = true := by
  decide +kernel

/-- Sub-band B14: `7301 ≤ n ≤ 8299` (Prefix Cert 6). -/
def fc2kSpecB14 : FC2KSubbandSpec where
  n_lo := 7301
  n_hi := 8299
  J_max := 2
  W_ord := 52
  W_diag := 20
  N_bins := 14
  δ := 3 / 500
  ε := 1 / 30
  c_lo := 239 / 500
  c_hi := 2563 / 5000
  a_X := 3835
  S_lo_up := 32352
  X_lo := 1046649200
  b_X := 3886
  a_Xh := 3885
  S_hi_up := 37109
  X_hi := 1377068017
  S_lo := 32351
  c_W := 272949 / 1000000000
  c_N := 10481 / 500
  c_B := 5500987 / 1000000
  brStages := [
    { M := 4545, wLow := .octCap 3 1 69147, wHigh := .aboveMaxHi },
    { M := 4545, wLow := .octCap 3 1 69147, wHigh := .aboveMaxHi }
  ]
  wHalf := .aboveMaxHi
  wFull := .aboveMaxHi

private theorem fc2kSpecB14_valid :
    checkFC2KSubbandSpec 28 55842 157529207 461091979
      (planTotalSpanWords fc2kSubCerts6 fc2kPlan6)
      fc2kPlan6.windowCaps fc2kPlan6.octWindowCaps fc2kSpecB14 = true := by
  decide +kernel

/-- Sub-band B15: `8301 ≤ n ≤ 9299` (Prefix Cert 6). -/
def fc2kSpecB15 : FC2KSubbandSpec where
  n_lo := 8301
  n_hi := 9299
  J_max := 2
  W_ord := 56
  W_diag := 20
  N_bins := 14
  δ := 3 / 500
  ε := 1 / 30
  c_lo := 239 / 500
  c_hi := 511 / 1000
  a_X := 3885
  S_lo_up := 37038
  X_lo := 1371787475
  b_X := 3931
  a_Xh := 3930
  S_hi_up := 41834
  X_hi := 1750021194
  S_lo := 37037
  c_W := 271347 / 1000000000
  c_N := 2817 / 125
  c_B := 2578601 / 500000
  brStages := [
    { M := 4533, wLow := .octCap 3 1 0, wHigh := .aboveMaxHi },
    { M := 5124, wLow := .octCap 6 1 180291, wHigh := .aboveMaxHi }
  ]
  wHalf := .aboveMaxHi
  wFull := .aboveMaxHi

private theorem fc2kSpecB15_valid :
    checkFC2KSubbandSpec 28 55842 157529207 461091979
      (planTotalSpanWords fc2kSubCerts6 fc2kPlan6)
      fc2kPlan6.windowCaps fc2kPlan6.octWindowCaps fc2kSpecB15 = true := by
  decide +kernel

/-- Sub-band B16: `9301 ≤ n ≤ 10999` (Prefix Cert 7). -/
def fc2kSpecB16 : FC2KSubbandSpec where
  n_lo := 9301
  n_hi := 10999
  J_max := 3
  W_ord := 70
  W_diag := 30
  N_bins := 14
  δ := 1 / 200
  ε := 1 / 40
  c_lo := 4771 / 10000
  c_hi := 317 / 625
  a_X := 3929
  S_lo_up := 41749
  X_lo := 1742958945
  b_X := 3996
  a_Xh := 3995
  S_hi_up := 49910
  X_hi := 2491005167
  S_lo := 41748
  c_W := 221887 / 1000000000
  c_N := 1161 / 40
  c_B := 1246893 / 100000
  brStages := [
    { M := 4798, wLow := .octCap 0 1 0, wHigh := .aboveMaxHi },
    { M := 6113, wLow := .octCap 1 1 295881, wHigh := .aboveMaxHi },
    { M := 6113, wLow := .octCap 1 1 295881, wHigh := .aboveMaxHi }
  ]
  wHalf := .octCap 0 1 0
  wFull := .octCap 6 1 0

private theorem fc2kSpecB16_valid :
    checkFC2KSubbandSpec 28 93042 347562017 864641065
      (planTotalSpanWords fc2kSubCerts7 fc2kPlan7)
      fc2kPlan7.windowCaps fc2kPlan7.octWindowCaps fc2kSpecB16 = true := by
  decide +kernel

/-- Sub-band B17: `11001 ≤ n ≤ 12999` (Prefix Cert 7). -/
def fc2kSpecB17 : FC2KSubbandSpec where
  n_lo := 11001
  n_hi := 12999
  J_max := 3
  W_ord := 78
  W_diag := 30
  N_bins := 14
  δ := 1 / 200
  ε := 1 / 40
  c_lo := 239 / 500
  c_hi := 5061 / 10000
  a_X := 3994
  S_lo_up := 49812
  X_lo := 2481202147
  b_X := 4061
  a_Xh := 4060
  S_hi_up := 59489
  X_hi := 3538825835
  S_lo := 49811
  c_W := 219797 / 1000000000
  c_N := 6457 / 200
  c_B := 13276953 / 1000000
  brStages := [
    { M := 4793, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 6676, wLow := .octCap 2 3 0, wHigh := .aboveMaxHi },
    { M := 7286, wLow := .octCap 0 2 0, wHigh := .aboveMaxHi }
  ]
  wHalf := .aboveMaxHi
  wFull := .aboveMaxHi

private theorem fc2kSpecB17_valid :
    checkFC2KSubbandSpec 28 93042 347562017 864641065
      (planTotalSpanWords fc2kSubCerts7 fc2kPlan7)
      fc2kPlan7.windowCaps fc2kPlan7.octWindowCaps fc2kSpecB17 = true := by
  decide +kernel

/-- Sub-band B18: `13001 ≤ n ≤ 15499` (Prefix Cert 7). -/
def fc2kSpecB18 : FC2KSubbandSpec where
  n_lo := 13001
  n_hi := 15499
  J_max := 4
  W_ord := 84
  W_diag := 30
  N_bins := 14
  δ := 9 / 2000
  ε := 1 / 40
  c_lo := 239 / 500
  c_hi := 2523 / 5000
  a_X := 4059
  S_lo_up := 59374
  X_lo := 3525242828
  b_X := 4129
  a_Xh := 4128
  S_hi_up := 71551
  X_hi := 5119493314
  S_lo := 59373
  c_W := 97507 / 500000000
  c_N := 17659 / 500
  c_B := 3592411 / 250000
  brStages := [
    { M := 4837, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 6737, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 8764, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 8764, wLow := .aboveMaxHi, wHigh := .aboveMaxHi }
  ]
  wHalf := .aboveMaxHi
  wFull := .aboveMaxHi

private theorem fc2kSpecB18_valid :
    checkFC2KSubbandSpec 28 93042 347562017 864641065
      (planTotalSpanWords fc2kSubCerts7 fc2kPlan7)
      fc2kPlan7.windowCaps fc2kPlan7.octWindowCaps fc2kSpecB18 = true := by
  decide +kernel

/-- Sub-band B19: `15501 ≤ n ≤ 17499` (Prefix Cert 8). -/
def fc2kSpecB19 : FC2KSubbandSpec where
  n_lo := 15501
  n_hi := 17499
  J_max := 4
  W_ord := 88
  W_diag := 30
  N_bins := 14
  δ := 7 / 2000
  ε := 1 / 40
  c_lo := 239 / 500
  c_hi := 5023 / 10000
  a_X := 4127
  S_lo_up := 71417
  X_lo := 5100346160
  b_X := 4176
  a_Xh := 4175
  S_hi_up := 81266
  X_hi := 6604036896
  S_lo := 71416
  c_W := 149639 / 1000000000
  c_N := 4776 / 125
  c_B := 14633577 / 1000000
  brStages := [
    { M := 4567, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 6361, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 8860, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 9953, wLow := .aboveMaxHi, wHigh := .aboveMaxHi }
  ]
  wHalf := .aboveMaxHi
  wFull := .aboveMaxHi

private theorem fc2kSpecB19_valid :
    checkFC2KSubbandSpec 28 116946 440228507 943544989
      (planTotalSpanWords fc2kSubCerts8 fc2kPlan8)
      fc2kPlan8.windowCaps fc2kPlan8.octWindowCaps fc2kSpecB19 = true := by
  decide +kernel

/-- Sub-band B20: `17501 ≤ n ≤ 19483` (Prefix Cert 8). -/
def fc2kSpecB20 : FC2KSubbandSpec where
  n_lo := 17501
  n_hi := 19483
  J_max := 5
  W_ord := 92
  W_diag := 30
  N_bins := 14
  δ := 7 / 2000
  ε := 1 / 40
  c_lo := 239 / 500
  c_hi := 5013 / 10000
  a_X := 4174
  S_lo_up := 81116
  X_lo := 6579773429
  b_X := 4218
  a_Xh := 4217
  S_hi_up := 90956
  X_hi := 8272897339
  S_lo := 81115
  c_W := 148757 / 1000000000
  c_N := 19961 / 500
  c_B := 7949681 / 500000
  brStages := [
    { M := 4501, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 6268, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 8731, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 11140, wLow := .aboveMaxHi, wHigh := .aboveMaxHi },
    { M := 11140, wLow := .aboveMaxHi, wHigh := .aboveMaxHi }
  ]
  wHalf := .aboveMaxHi
  wFull := .aboveMaxHi

private theorem fc2kSpecB20_valid :
    checkFC2KSubbandSpec 28 116946 440228507 943544989
      (planTotalSpanWords fc2kSubCerts8 fc2kPlan8)
      fc2kPlan8.windowCaps fc2kPlan8.octWindowCaps fc2kSpecB20 = true := by
  decide +kernel

/-- Every odd order `n` in the FC2K band `2001 ≤ n ≤ 19483` admits a valid Sude square. -/
theorem fc2k_hasSquare
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (rs : RSPrimeCountImports)
    (upper : RSIndexUpper) (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 19483) (hodd : Odd n) :
    HasSquare n := by
  have hodd' : Odd n := hodd
  rcases hodd' with ⟨k_odd, hk_odd⟩
  by_cases h00 : n ≤ 2031
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile0
      fc2kSpecB00 fc2kSpecB00_valid hnlo h00 hodd
  by_cases h01 : n ≤ 2079
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile0
      fc2kSpecB01 fc2kSpecB01_valid (show 2033 ≤ n by omega) h01 hodd
  by_cases h02 : n ≤ 2179
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile0
      fc2kSpecB02 fc2kSpecB02_valid (show 2081 ≤ n by omega) h02 hodd
  by_cases h03 : n ≤ 2349
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile1
      fc2kSpecB03 fc2kSpecB03_valid (show 2181 ≤ n by omega) h03 hodd
  by_cases h04 : n ≤ 2549
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile1
      fc2kSpecB04 fc2kSpecB04_valid (show 2351 ≤ n by omega) h04 hodd
  by_cases h05 : n ≤ 2749
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile2
      fc2kSpecB05 fc2kSpecB05_valid (show 2551 ≤ n by omega) h05 hodd
  by_cases h06 : n ≤ 2999
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile2
      fc2kSpecB06 fc2kSpecB06_valid (show 2751 ≤ n by omega) h06 hodd
  by_cases h07 : n ≤ 3349
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile3
      fc2kSpecB07 fc2kSpecB07_valid (show 3001 ≤ n by omega) h07 hodd
  by_cases h08 : n ≤ 3699
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile3
      fc2kSpecB08 fc2kSpecB08_valid (show 3351 ≤ n by omega) h08 hodd
  by_cases h09 : n ≤ 4199
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile4
      fc2kSpecB09 fc2kSpecB09_valid (show 3701 ≤ n by omega) h09 hodd
  by_cases h10 : n ≤ 4799
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile4
      fc2kSpecB10 fc2kSpecB10_valid (show 4201 ≤ n by omega) h10 hodd
  by_cases h11 : n ≤ 5499
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile5
      fc2kSpecB11 fc2kSpecB11_valid (show 4801 ≤ n by omega) h11 hodd
  by_cases h12 : n ≤ 6299
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile5
      fc2kSpecB12 fc2kSpecB12_valid (show 5501 ≤ n by omega) h12 hodd
  by_cases h13 : n ≤ 7299
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile6
      fc2kSpecB13 fc2kSpecB13_valid (show 6301 ≤ n by omega) h13 hodd
  by_cases h14 : n ≤ 8299
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile6
      fc2kSpecB14 fc2kSpecB14_valid (show 7301 ≤ n by omega) h14 hodd
  by_cases h15 : n ≤ 9299
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile6
      fc2kSpecB15 fc2kSpecB15_valid (show 8301 ≤ n by omega) h15 hodd
  by_cases h16 : n ≤ 10999
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile7
      fc2kSpecB16 fc2kSpecB16_valid (show 9301 ≤ n by omega) h16 hodd
  by_cases h17 : n ≤ 12999
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile7
      fc2kSpecB17 fc2kSpecB17_valid (show 11001 ≤ n by omega) h17 hodd
  by_cases h18 : n ≤ 15499
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile7
      fc2kSpecB18 fc2kSpecB18_valid (show 13001 ≤ n by omega) h18 hodd
  by_cases h19 : n ≤ 17499
  · exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile8
      fc2kSpecB19 fc2kSpecB19_valid (show 15501 ≤ n by omega) h19 hodd
  exact fc2k_hasSquare_of_spec bmor imp rs upper sharp upperSharp fc2kPrefixProfile8
    fc2kSpecB20 fc2kSpecB20_valid (show 17501 ≤ n by omega) hnhi hodd

end Sude
