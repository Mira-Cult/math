import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 0

Certifies `P = 25` power-of-two prime-pair stages (`qCert = 13122`, `1` chunk(s) of `13122`)
in `[6191285, 44530357]` via `1` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 1745`).
-/

namespace Sude

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/0 for FC2K certificate 0 (`13` active super-chunks). -/
def fc2kSubCert0_0 : PrefixSubCert where
  corrLo := 6191285
  numSuperChunks := 13
  activeChunkMask := 0x1fff
  numChunks := 25
  qSub := 13122
  maxHi := 44530357
  chunks := [
    (24, { startWord := 0, endWord := 56, endBitCutoff := 3003, subMod := 1 }),
    (23, { startWord := 0, endWord := 54, endBitCutoff := 4807, subMod := 1 }),
    (22, { startWord := 48, endWord := 103, endBitCutoff := 7334, subMod := 1 }),
    (21, { startWord := 42, endWord := 96, endBitCutoff := 7364, subMod := 1 }),
    (20, { startWord := 60, endWord := 118, endBitCutoff := 8004, subMod := 1 }),
    (19, { startWord := 160, endWord := 215, endBitCutoff := 6751, subMod := 1 }),
    (18, { startWord := 261, endWord := 318, endBitCutoff := 6258, subMod := 1 }),
    (17, { startWord := 385, endWord := 444, endBitCutoff := 8100, subMod := 1 }),
    (16, { startWord := 445, endWord := 504, endBitCutoff := 7685, subMod := 1 }),
    (15, { startWord := 520, endWord := 580, endBitCutoff := 7817, subMod := 1 }),
    (14, { startWord := 584, endWord := 645, endBitCutoff := 7235, subMod := 1 }),
    (13, { startWord := 317, endWord := 383, endBitCutoff := 7245, subMod := 1 }),
    (12, { startWord := 181, endWord := 252, endBitCutoff := 7694, subMod := 1 }),
    (11, { startWord := 84, endWord := 155, endBitCutoff := 7601, subMod := 1 }),
    (10, { startWord := 0, endWord := 75, endBitCutoff := 1580, subMod := 1 }),
    (9, { startWord := 646, endWord := 711, endBitCutoff := 6800, subMod := 1 }),
    (8, { startWord := 712, endWord := 779, endBitCutoff := 7960, subMod := 1 }),
    (7, { startWord := 240, endWord := 317, endBitCutoff := 8071, subMod := 1 }),
    (6, { startWord := 445, endWord := 521, endBitCutoff := 7460, subMod := 1 }),
    (5, { startWord := 506, endWord := 587, endBitCutoff := 7808, subMod := 1 }),
    (4, { startWord := 365, endWord := 444, endBitCutoff := 7182, subMod := 1 }),
    (3, { startWord := 581, endWord := 663, endBitCutoff := 7321, subMod := 1 }),
    (2, { startWord := 118, endWord := 206, endBitCutoff := 7902, subMod := 1 }),
    (1, { startWord := 0, endWord := 100, endBitCutoff := 4006, subMod := 1 }),
    (0, { startWord := 267, endWord := 361, endBitCutoff := 7666, subMod := 1 })
  ]
  windowCaps := [
    { minWordIdx := 218, spanWords := 24, cap := 25597 },
    { minWordIdx := 230, spanWords := 25, cap := 26655 },
    { minWordIdx := 248, spanWords := 28, cap := 29848 },
    { minWordIdx := 472, spanWords := 23, cap := 18501 },
    { minWordIdx := 472, spanWords := 88, cap := 67636 },
    { minWordIdx := 486, spanWords := 28, cap := 22221 },
    { minWordIdx := 486, spanWords := 108, cap := 82909 },
    { minWordIdx := 517, spanWords := 31, cap := 24447 },
    { minWordIdx := 517, spanWords := 119, cap := 90466 },
    { minWordIdx := 885, spanWords := 24, cap := 0 },
    { minWordIdx := 919, spanWords := 25, cap := 0 },
    { minWordIdx := 971, spanWords := 28, cap := 0 }
  ]
  octCounts := [
    (0, 9343), (1, 9523), (2, 9378), (3, 9317), (4, 9204), (5, 9824), (6, 10632), (7, 9276), (8, 9648), (9, 8598),
    (10, 8804), (11, 9754), (12, 8023), (13, 6720), (14, 7053), (15, 7778), (16, 8637), (17, 8633), (18, 8832), (19, 7915),
    (20, 7033), (21, 6640), (22, 7516), (23, 8715), (24, 8705), (25, 8397), (26, 6636), (27, 5966), (28, 6569), (29, 6098),
    (30, 7326), (31, 6538), (32, 5326), (33, 7712), (34, 8753), (35, 8368), (36, 8476), (37, 8433), (38, 8380), (39, 8346),
    (40, 7106), (41, 6694), (42, 6763), (43, 7483), (44, 7414), (45, 6495), (46, 7278), (47, 7182), (48, 6201), (49, 7035),
    (50, 6211), (51, 6336), (52, 6298), (53, 6338), (54, 6242), (55, 6201), (56, 6412), (57, 6066), (58, 5985), (59, 6073),
    (60, 6096), (61, 6147), (62, 6222), (63, 6200), (64, 6110), (65, 6243), (66, 6078), (67, 6006), (68, 6063), (69, 5943),
    (70, 5827), (71, 5838), (72, 6173), (73, 6958), (74, 6035), (75, 5971), (76, 6092), (77, 5918), (78, 6008), (79, 5991),
    (80, 6051), (81, 5894), (82, 5782), (83, 3335), (84, 3503), (85, 4243), (86, 4834), (87, 4745), (88, 4705), (89, 4550),
    (90, 4436), (91, 4381), (92, 3825), (93, 3317), (94, 3443), (95, 3348), (96, 3404), (97, 1747)
  ]

theorem fc2kSubCert0_0_valid : checkPrefixSubCert fc2kSubCert0_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf0_0 : VerifiedSubCertProfile fc2kSubCert0_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert0_0 fc2kSubCert0_0_valid)

def fc2kSubCerts0 : List PrefixSubCert := [fc2kSubCert0_0]

def fc2kPlan0 : MultiSubCertPlan where
  P := 25
  M := 1
  qSub := 13122
  qCert := 13122
  corrLo := 6191285
  maxHi := 44530357
  numOcts := 100
  routes := [
    [(0, 24)],
    [(0, 23)],
    [(0, 22)],
    [(0, 21)],
    [(0, 20)],
    [(0, 19)],
    [(0, 18)],
    [(0, 17)],
    [(0, 16)],
    [(0, 15)],
    [(0, 14)],
    [(0, 13)],
    [(0, 12)],
    [(0, 11)],
    [(0, 10)],
    [(0, 9)],
    [(0, 8)],
    [(0, 7)],
    [(0, 6)],
    [(0, 5)],
    [(0, 4)],
    [(0, 3)],
    [(0, 2)],
    [(0, 1)],
    [(0, 0)]
  ]
  windowCaps := [
    { minWordIdx := 218, spanWords := 24, cap := 25597 },
    { minWordIdx := 230, spanWords := 25, cap := 26655 },
    { minWordIdx := 248, spanWords := 28, cap := 29848 },
    { minWordIdx := 472, spanWords := 23, cap := 18501 },
    { minWordIdx := 472, spanWords := 88, cap := 67636 },
    { minWordIdx := 486, spanWords := 28, cap := 22221 },
    { minWordIdx := 486, spanWords := 108, cap := 82909 },
    { minWordIdx := 517, spanWords := 31, cap := 24447 },
    { minWordIdx := 517, spanWords := 119, cap := 90466 },
    { minWordIdx := 885, spanWords := 24, cap := 0 },
    { minWordIdx := 919, spanWords := 25, cap := 0 },
    { minWordIdx := 971, spanWords := 28, cap := 0 }
  ]
  octWindowCaps := []

theorem fc2kPlan0_valid : checkMultiSubCertPlan fc2kSubCerts0 fc2kPlan0 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs0 :
    ∀ g : Fin fc2kSubCerts0.length,
      VerifiedSubCertProfile (fc2kSubCerts0[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf0_0
  | ⟨k + 1, h⟩ => False.elim (by change k + 1 < 1 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 0. -/
noncomputable def fc2kPrefixProfile0 :
    GeneralPrefixProfile 25 13122 6191285 44530357 :=
  assembleGeneralPrefixProfile fc2kSubCerts0 fc2kPlan0 fc2kPlan0_valid fc2kSubProfs0

end Sude
