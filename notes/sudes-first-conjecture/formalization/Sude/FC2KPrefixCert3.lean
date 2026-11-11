import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 3

Certifies `P = 26` power-of-two prime-pair stages (`qCert = 22242`, `1` chunk(s) of `22242`)
in `[22632281, 107419483]` via `2` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 3351`).
-/

namespace Sude

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/1 for FC2K certificate 3 (`15` active super-chunks). -/
def fc2kSubCert3_0 : PrefixSubCert where
  corrLo := 22632281
  numSuperChunks := 24
  activeChunkMask := 0xe01eff
  numChunks := 16
  qSub := 22242
  maxHi := 107419483
  chunks := [
    (25, { startWord := 4, endWord := 111, endBitCutoff := 7623, subMod := 1 }),
    (24, { startWord := 712, endWord := 823, endBitCutoff := 7606, subMod := 1 }),
    (23, { startWord := 44, endWord := 155, endBitCutoff := 6985, subMod := 1 }),
    (22, { startWord := 0, endWord := 101, endBitCutoff := 1582, subMod := 1 }),
    (21, { startWord := 108, endWord := 223, endBitCutoff := 7986, subMod := 1 }),
    (20, { startWord := 148, endWord := 273, endBitCutoff := 4385, subMod := 1 }),
    (19, { startWord := 0, endWord := 145, endBitCutoff := 3051, subMod := 1 }),
    (18, { startWord := 288, endWord := 397, endBitCutoff := 6199, subMod := 1 }),
    (17, { startWord := 376, endWord := 505, endBitCutoff := 2161, subMod := 1 }),
    (16, { startWord := 640, endWord := 758, endBitCutoff := 5596, subMod := 1 }),
    (15, { startWord := 688, endWord := 824, endBitCutoff := 5652, subMod := 1 }),
    (14, { startWord := 576, endWord := 698, endBitCutoff := 2585, subMod := 1 }),
    (13, { startWord := 224, endWord := 383, endBitCutoff := 4560, subMod := 1 }),
    (12, { startWord := 0, endWord := 171, endBitCutoff := 6002, subMod := 1 }),
    (11, { startWord := 1344, endWord := 1483, endBitCutoff := 7970, subMod := 1 }),
    (10, { startWord := 1372, endWord := 1532, endBitCutoff := 3422, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 6585), (1, 7129), (2, 7668), (3, 8177), (4, 8287), (5, 8698), (6, 9156), (7, 9193), (8, 9024), (9, 9132),
    (10, 9094), (11, 9016), (12, 8688), (13, 8029), (14, 7847), (15, 7750), (16, 7537), (17, 7696), (18, 7460), (19, 6996),
    (20, 6342), (21, 5217), (22, 4735), (23, 4940), (24, 7106), (25, 7459), (26, 7511), (27, 7498), (28, 8059), (29, 7859),
    (30, 8105), (31, 8193), (32, 8052), (33, 8017), (34, 5792), (35, 5605), (36, 6760), (37, 7308), (38, 7400), (39, 6433),
    (40, 6020), (41, 5998), (42, 5907), (43, 5906), (44, 5916), (45, 5906), (46, 5822), (47, 6978), (48, 6644), (49, 6575),
    (50, 5593), (51, 4304), (52, 4322), (53, 4335), (54, 4321), (55, 4302), (56, 4391), (57, 4572), (58, 4576), (59, 4550),
    (60, 4484), (61, 4587), (62, 3447), (63, 1589), (72, 3288), (73, 3415), (74, 3336), (75, 3252), (76, 3303), (77, 3265),
    (78, 3245), (79, 3380), (80, 5308), (81, 5715), (82, 5786), (83, 5801), (84, 5822), (85, 5760), (86, 7753), (87, 6439),
    (88, 5784), (89, 6537), (90, 6542), (91, 6502), (92, 6525), (93, 6452), (94, 6467), (95, 4553), (96, 4457), (97, 4427),
    (98, 4409), (99, 4266), (100, 4572), (101, 4406), (102, 4411), (103, 516), (168, 3083), (169, 3064), (170, 3042), (171, 5243),
    (172, 6435), (173, 6474), (174, 7173), (175, 7462), (176, 7441), (177, 7474), (178, 7439), (179, 7352), (180, 7458), (181, 7370),
    (182, 7463), (183, 7356), (184, 7098), (185, 5309), (186, 4270), (187, 4073), (188, 3497), (189, 3076), (190, 3118), (191, 1682)
  ]

theorem fc2kSubCert3_0_valid : checkPrefixSubCert fc2kSubCert3_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf3_0 : VerifiedSubCertProfile fc2kSubCert3_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert3_0 fc2kSubCert3_0_valid)

/-- Sub-certificate 1/1 for FC2K certificate 3 (`11` active super-chunks). -/
def fc2kSubCert3_1 : PrefixSubCert where
  corrLo := 22632281
  numSuperChunks := 27
  activeChunkMask := 0x71fe000
  numChunks := 10
  qSub := 22242
  maxHi := 107419483
  chunks := [
    (9, { startWord := 832, endWord := 942, endBitCutoff := 1933, subMod := 1 }),
    (8, { startWord := 896, endWord := 1018, endBitCutoff := 1540, subMod := 1 }),
    (7, { startWord := 832, endWord := 986, endBitCutoff := 5618, subMod := 1 }),
    (6, { startWord := 952, endWord := 1084, endBitCutoff := 7041, subMod := 1 }),
    (5, { startWord := 1024, endWord := 1150, endBitCutoff := 7150, subMod := 1 }),
    (4, { startWord := 1084, endWord := 1212, endBitCutoff := 3960, subMod := 1 }),
    (3, { startWord := 1152, endWord := 1276, endBitCutoff := 7534, subMod := 1 }),
    (2, { startWord := 1212, endWord := 1340, endBitCutoff := 4493, subMod := 1 }),
    (1, { startWord := 1536, endWord := 1651, endBitCutoff := 6013, subMod := 1 }),
    (0, { startWord := 1596, endWord := 1724, endBitCutoff := 4513, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (104, 5711), (105, 5662), (106, 5683), (107, 5779), (108, 5635), (109, 5675), (110, 5615), (111, 5741), (112, 7537), (113, 7631),
    (114, 7694), (115, 7646), (116, 7592), (117, 7318), (118, 5702), (119, 7564), (120, 7561), (121, 7710), (122, 7377), (123, 6212),
    (124, 5674), (125, 5758), (126, 5654), (127, 3799), (128, 5711), (129, 5651), (130, 5478), (131, 5472), (132, 5605), (133, 5625),
    (134, 5711), (135, 5909), (136, 5552), (137, 5684), (138, 5554), (139, 5539), (140, 5585), (141, 5442), (142, 5646), (143, 5258),
    (144, 5628), (145, 5560), (146, 5610), (147, 5666), (148, 5814), (149, 5654), (150, 5520), (151, 5639), (152, 5701), (153, 5573),
    (154, 5641), (155, 5760), (156, 5486), (157, 5516), (158, 5492), (159, 4600), (160, 3148), (161, 3114), (162, 3120), (163, 3084),
    (164, 3160), (165, 3081), (166, 3171), (167, 1782), (192, 3146), (193, 2962), (194, 3116), (195, 3014), (196, 3140), (197, 2946),
    (198, 3114), (199, 4190), (200, 5534), (201, 5474), (202, 5466), (203, 5406), (204, 5428), (205, 5538), (206, 4166), (207, 3192),
    (208, 2990), (209, 3182), (210, 3054), (211, 3000), (212, 3132), (213, 3130), (214, 2906), (215, 1742)
  ]

theorem fc2kSubCert3_1_valid : checkPrefixSubCert fc2kSubCert3_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf3_1 : VerifiedSubCertProfile fc2kSubCert3_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert3_1 fc2kSubCert3_1_valid)

def fc2kSubCerts3 : List PrefixSubCert := [fc2kSubCert3_0, fc2kSubCert3_1]

def fc2kPlan3 : MultiSubCertPlan where
  P := 26
  M := 1
  qSub := 22242
  qCert := 22242
  corrLo := 22632281
  maxHi := 107419483
  numOcts := 298
  routes := [
    [(1, 9)],
    [(1, 8)],
    [(1, 7)],
    [(1, 6)],
    [(1, 5)],
    [(1, 4)],
    [(1, 3)],
    [(1, 2)],
    [(1, 1)],
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
    { minWordIdx := 44, spanWords := 10, cap := 73988 },
    { minWordIdx := 71, spanWords := 12, cap := 87560 },
    { minWordIdx := 117, spanWords := 11, cap := 81086 },
    { minWordIdx := 117, spanWords := 38, cap := 221757 },
    { minWordIdx := 160, spanWords := 15, cap := 104547 },
    { minWordIdx := 160, spanWords := 55, cap := 244338 },
    { minWordIdx := 239, spanWords := 10, cap := 0 },
    { minWordIdx := 318, spanWords := 12, cap := 0 }
  ]

theorem fc2kPlan3_valid : checkMultiSubCertPlan fc2kSubCerts3 fc2kPlan3 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs3 :
    ∀ g : Fin fc2kSubCerts3.length,
      VerifiedSubCertProfile (fc2kSubCerts3[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf3_0
  | ⟨1, _⟩ => fc2kSubProf3_1
  | ⟨k + 2, h⟩ => False.elim (by change k + 2 < 2 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 3. -/
noncomputable def fc2kPrefixProfile3 :
    GeneralPrefixProfile 26 22242 22632281 107419483 :=
  assembleGeneralPrefixProfile fc2kSubCerts3 fc2kPlan3 fc2kPlan3_valid fc2kSubProfs3

end Sude
