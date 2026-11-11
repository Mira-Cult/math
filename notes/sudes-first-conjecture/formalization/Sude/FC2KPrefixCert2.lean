import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 2

Certifies `P = 25` power-of-two prime-pair stages (`qCert = 18042`, `1` chunk(s) of `18042`)
in `[13856789, 98447383]` via `2` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 2327`).
-/

namespace Sude

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/1 for FC2K certificate 2 (`18` active super-chunks). -/
def fc2kSubCert2_0 : PrefixSubCert where
  corrLo := 13856789
  numSuperChunks := 18
  activeChunkMask := 0x3ffff
  numChunks := 19
  qSub := 18042
  maxHi := 98447383
  chunks := [
    (24, { startWord := 0, endWord := 81, endBitCutoff := 5046, subMod := 1 }),
    (23, { startWord := 0, endWord := 79, endBitCutoff := 4784, subMod := 1 }),
    (22, { startWord := 81, endWord := 160, endBitCutoff := 7545, subMod := 1 }),
    (21, { startWord := 78, endWord := 157, endBitCutoff := 7763, subMod := 1 }),
    (20, { startWord := 242, endWord := 329, endBitCutoff := 7790, subMod := 1 }),
    (19, { startWord := 396, endWord := 480, endBitCutoff := 7618, subMod := 1 }),
    (18, { startWord := 144, endWord := 236, endBitCutoff := 6711, subMod := 1 }),
    (17, { startWord := 496, endWord := 581, endBitCutoff := 7830, subMod := 1 }),
    (16, { startWord := 584, endWord := 670, endBitCutoff := 6749, subMod := 1 }),
    (15, { startWord := 765, endWord := 852, endBitCutoff := 7799, subMod := 1 }),
    (14, { startWord := 0, endWord := 104, endBitCutoff := 4928, subMod := 1 }),
    (13, { startWord := 858, endWord := 946, endBitCutoff := 7671, subMod := 1 }),
    (12, { startWord := 946, endWord := 1035, endBitCutoff := 7503, subMod := 1 }),
    (11, { startWord := 1033, endWord := 1123, endBitCutoff := 6995, subMod := 1 }),
    (10, { startWord := 330, endWord := 436, endBitCutoff := 7894, subMod := 1 }),
    (9, { startWord := 662, endWord := 762, endBitCutoff := 8095, subMod := 1 }),
    (7, { startWord := 95, endWord := 209, endBitCutoff := 6173, subMod := 1 }),
    (4, { startWord := 446, endWord := 555, endBitCutoff := 8148, subMod := 1 }),
    (3, { startWord := 214, endWord := 328, endBitCutoff := 6936, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 6356), (1, 6502), (2, 6369), (3, 6471), (4, 6423), (5, 6345), (6, 6487), (7, 6358), (8, 6423), (9, 6554),
    (10, 6341), (11, 6446), (12, 8279), (13, 6639), (14, 6421), (15, 6469), (16, 6405), (17, 6384), (18, 7508), (19, 7791),
    (20, 6925), (21, 7269), (22, 7434), (23, 7353), (24, 7292), (25, 7395), (26, 6002), (27, 7072), (28, 7100), (29, 6652),
    (30, 6097), (31, 5497), (32, 6233), (33, 6156), (34, 6132), (35, 6544), (36, 7639), (37, 7458), (38, 7490), (39, 7419),
    (40, 7447), (41, 5275), (42, 5128), (43, 6077), (44, 6109), (45, 6142), (46, 5533), (47, 4725), (48, 4850), (49, 5528),
    (50, 6229), (51, 6034), (52, 6577), (53, 6110), (54, 4991), (55, 4082), (56, 5888), (57, 5948), (58, 5879), (59, 5907),
    (60, 4913), (61, 4583), (62, 6159), (63, 6021), (64, 6150), (65, 6051), (66, 5999), (67, 5967), (68, 5870), (69, 4578),
    (70, 3366), (71, 3283), (72, 2823), (73, 3254), (74, 3297), (75, 3365), (76, 3322), (77, 3438), (78, 3381), (79, 3407),
    (80, 3391), (81, 3316), (82, 3938), (83, 5682), (84, 3612), (85, 4088), (86, 4595), (87, 4625), (88, 4576), (89, 4609),
    (90, 4692), (91, 4565), (92, 4635), (93, 4606), (94, 4465), (95, 3030), (96, 3202), (97, 3377), (98, 3232), (99, 3265),
    (100, 3264), (101, 3293), (102, 3208), (103, 3321), (104, 3417), (105, 3164), (106, 2360), (107, 2474), (108, 3204), (109, 3212),
    (110, 3233), (111, 3289), (112, 3215), (113, 3236), (114, 3316), (115, 3150), (116, 3210), (117, 3279), (118, 3507), (119, 3241),
    (120, 3175), (121, 3344), (122, 3284), (123, 3217), (124, 3238), (125, 3165), (126, 3189), (127, 3222), (128, 3122), (129, 4250),
    (130, 3212), (131, 3261), (132, 3149), (133, 3173), (134, 3220), (135, 3231), (136, 3193), (137, 3157), (138, 3107), (139, 3246),
    (140, 1531)
  ]

theorem fc2kSubCert2_0_valid : checkPrefixSubCert fc2kSubCert2_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf2_0 : VerifiedSubCertProfile fc2kSubCert2_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert2_0 fc2kSubCert2_0_valid)

/-- Sub-certificate 1/1 for FC2K certificate 2 (`9` active super-chunks). -/
def fc2kSubCert2_1 : PrefixSubCert where
  corrLo := 13856789
  numSuperChunks := 27
  activeChunkMask := 0x7fc0000
  numChunks := 6
  qSub := 18042
  maxHi := 98447383
  chunks := [
    (8, { startWord := 1152, endWord := 1243, endBitCutoff := 3017, subMod := 1 }),
    (6, { startWord := 1248, endWord := 1338, endBitCutoff := 7982, subMod := 1 }),
    (5, { startWord := 1339, endWord := 1430, endBitCutoff := 7923, subMod := 1 }),
    (2, { startWord := 1431, endWord := 1523, endBitCutoff := 7817, subMod := 1 }),
    (1, { startWord := 1526, endWord := 1618, endBitCutoff := 8128, subMod := 1 }),
    (0, { startWord := 1627, endWord := 1720, endBitCutoff := 7638, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (144, 3138), (145, 3075), (146, 3284), (147, 3151), (148, 3257), (149, 3104), (150, 3086), (151, 3181), (152, 3108), (153, 3058),
    (154, 3255), (155, 1387), (156, 3177), (157, 3301), (158, 3127), (159, 3089), (160, 3124), (161, 3199), (162, 3224), (163, 3071),
    (164, 3219), (165, 3207), (166, 3157), (167, 3225), (168, 3171), (169, 3109), (170, 3122), (171, 3146), (172, 3132), (173, 3061),
    (174, 3159), (175, 3048), (176, 3083), (177, 3321), (178, 3060), (179, 3100), (180, 3064), (181, 3086), (182, 3068), (183, 3208),
    (184, 3130), (185, 3056), (186, 3168), (187, 3024), (188, 3168), (189, 3112), (190, 2360), (191, 3224), (192, 3078), (193, 3178),
    (194, 3156), (195, 3028), (196, 3058), (197, 3104), (198, 3092), (199, 3114), (200, 3130), (201, 2962), (202, 1136), (203, 1970),
    (204, 3048), (205, 3130), (206, 2962), (207, 3096), (208, 3124), (209, 3070), (210, 3032), (211, 3004), (212, 3102), (213, 3084),
    (214, 3094), (215, 368)
  ]

theorem fc2kSubCert2_1_valid : checkPrefixSubCert fc2kSubCert2_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf2_1 : VerifiedSubCertProfile fc2kSubCert2_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert2_1 fc2kSubCert2_1_valid)

def fc2kSubCerts2 : List PrefixSubCert := [fc2kSubCert2_0, fc2kSubCert2_1]

def fc2kPlan2 : MultiSubCertPlan where
  P := 25
  M := 1
  qSub := 18042
  qCert := 18042
  corrLo := 13856789
  maxHi := 98447383
  numOcts := 220
  routes := [
    [(1, 5)],
    [(1, 4)],
    [(1, 3)],
    [(0, 18)],
    [(0, 17)],
    [(1, 2)],
    [(1, 1)],
    [(0, 16)],
    [(1, 0)],
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
  windowCaps := []
  octWindowCaps := [
    { minWordIdx := 36, spanWords := 7, cap := 47856 },
    { minWordIdx := 49, spanWords := 7, cap := 42217 },
    { minWordIdx := 49, spanWords := 8, cap := 46800 },
    { minWordIdx := 86, spanWords := 9, cap := 41368 },
    { minWordIdx := 86, spanWords := 30, cap := 107830 },
    { minWordIdx := 108, spanWords := 10, cap := 33243 },
    { minWordIdx := 108, spanWords := 36, cap := 112300 },
    { minWordIdx := 175, spanWords := 7, cap := 21907 },
    { minWordIdx := 176, spanWords := 7, cap := 21907 },
    { minWordIdx := 212, spanWords := 8, cap := 9648 },
    { minWordIdx := 213, spanWords := 7, cap := 6546 }
  ]

theorem fc2kPlan2_valid : checkMultiSubCertPlan fc2kSubCerts2 fc2kPlan2 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs2 :
    ∀ g : Fin fc2kSubCerts2.length,
      VerifiedSubCertProfile (fc2kSubCerts2[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf2_0
  | ⟨1, _⟩ => fc2kSubProf2_1
  | ⟨k + 2, h⟩ => False.elim (by change k + 2 < 2 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 2. -/
noncomputable def fc2kPrefixProfile2 :
    GeneralPrefixProfile 25 18042 13856789 98447383 :=
  assembleGeneralPrefixProfile fc2kSubCerts2 fc2kPlan2 fc2kPlan2_valid fc2kSubProfs2

end Sude
