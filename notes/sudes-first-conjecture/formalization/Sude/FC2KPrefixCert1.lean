import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 1

Certifies `P = 25` power-of-two prime-pair stages (`qCert = 15342`, `1` chunk(s) of `15342`)
in `[8628221, 69036061]` via `2` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 1950`).
-/

namespace Sude

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/1 for FC2K certificate 1 (`18` active super-chunks). -/
def fc2kSubCert1_0 : PrefixSubCert where
  corrLo := 8628221
  numSuperChunks := 18
  activeChunkMask := 0x3ffff
  numChunks := 24
  qSub := 15342
  maxHi := 69036061
  chunks := [
    (24, { startWord := 0, endWord := 67, endBitCutoff := 2840, subMod := 1 }),
    (23, { startWord := 0, endWord := 65, endBitCutoff := 816, subMod := 1 }),
    (22, { startWord := 49, endWord := 115, endBitCutoff := 7759, subMod := 1 }),
    (21, { startWord := 60, endWord := 124, endBitCutoff := 7797, subMod := 1 }),
    (20, { startWord := 76, endWord := 146, endBitCutoff := 8062, subMod := 1 }),
    (19, { startWord := 183, endWord := 255, endBitCutoff := 6974, subMod := 1 }),
    (18, { startWord := 272, endWord := 341, endBitCutoff := 6072, subMod := 1 }),
    (17, { startWord := 398, endWord := 468, endBitCutoff := 7406, subMod := 1 }),
    (16, { startWord := 474, endWord := 544, endBitCutoff := 7441, subMod := 1 }),
    (15, { startWord := 549, endWord := 620, endBitCutoff := 7894, subMod := 1 }),
    (14, { startWord := 618, endWord := 693, endBitCutoff := 7675, subMod := 1 }),
    (13, { startWord := 749, endWord := 822, endBitCutoff := 7003, subMod := 1 }),
    (12, { startWord := 822, endWord := 896, endBitCutoff := 8169, subMod := 1 }),
    (11, { startWord := 896, endWord := 970, endBitCutoff := 7504, subMod := 1 }),
    (10, { startWord := 113, endWord := 202, endBitCutoff := 6012, subMod := 1 }),
    (9, { startWord := 0, endWord := 91, endBitCutoff := 134, subMod := 1 }),
    (8, { startWord := 338, endWord := 423, endBitCutoff := 8168, subMod := 1 }),
    (7, { startWord := 994, endWord := 1069, endBitCutoff := 8056, subMod := 1 }),
    (6, { startWord := 1069, endWord := 1145, endBitCutoff := 6889, subMod := 1 }),
    (5, { startWord := 245, endWord := 334, endBitCutoff := 7129, subMod := 1 }),
    (3, { startWord := 424, endWord := 514, endBitCutoff := 7542, subMod := 1 }),
    (2, { startWord := 694, endWord := 783, endBitCutoff := 7278, subMod := 1 }),
    (1, { startWord := 514, endWord := 608, endBitCutoff := 6446, subMod := 1 }),
    (0, { startWord := 897, endWord := 988, endBitCutoff := 5576, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 6806), (1, 6781), (2, 6830), (3, 6676), (4, 6712), (5, 6765), (6, 7712), (7, 8429), (8, 7061), (9, 6933),
    (10, 7606), (11, 6206), (12, 5391), (13, 5413), (14, 6999), (15, 7221), (16, 6235), (17, 6341), (18, 6583), (19, 6554),
    (20, 6511), (21, 6581), (22, 6724), (23, 7355), (24, 6460), (25, 5347), (26, 4165), (27, 4517), (28, 5170), (29, 5212),
    (30, 6057), (31, 7410), (32, 6361), (33, 6395), (34, 7053), (35, 6918), (36, 6392), (37, 6285), (38, 6329), (39, 6437),
    (40, 6288), (41, 5957), (42, 5682), (43, 6353), (44, 5120), (45, 5005), (46, 4953), (47, 4874), (48, 4929), (49, 5056),
    (50, 6665), (51, 6107), (52, 6136), (53, 6272), (54, 6189), (55, 6252), (56, 6106), (57, 5968), (58, 5578), (59, 5329),
    (60, 6231), (61, 6101), (62, 6186), (63, 6080), (64, 6343), (65, 5962), (66, 5989), (67, 5917), (68, 5027), (69, 5997),
    (70, 6012), (71, 5745), (72, 6037), (73, 5970), (74, 5961), (75, 6089), (76, 3744), (77, 4564), (78, 3363), (79, 3294),
    (80, 3223), (81, 3431), (82, 3299), (83, 3441), (84, 3328), (85, 4235), (86, 4727), (87, 4727), (88, 4689), (89, 4640),
    (90, 4687), (91, 4702), (92, 4575), (93, 5358), (94, 6036), (95, 5839), (96, 5818), (97, 5795), (98, 3392), (99, 3327),
    (100, 3217), (101, 3278), (102, 3560), (103, 3384), (104, 3326), (105, 3311), (106, 3172), (107, 3238), (108, 3290), (109, 3314),
    (110, 3209), (111, 3297), (112, 5785), (113, 5993), (114, 5769), (115, 5956), (116, 5621), (117, 5796), (118, 5735), (119, 5828),
    (120, 5908), (121, 4264), (122, 3228), (123, 1936), (124, 2426), (125, 3130), (126, 3199), (127, 3239), (128, 3234), (129, 3255),
    (130, 3238), (131, 3272), (132, 3244), (133, 3507), (134, 3224), (135, 3232), (136, 3214), (137, 3109), (138, 3265), (139, 3096),
    (140, 3311), (141, 3207), (142, 3220), (143, 746)
  ]

theorem fc2kSubCert1_0_valid : checkPrefixSubCert fc2kSubCert1_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf1_0 : VerifiedSubCertProfile fc2kSubCert1_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert1_0 fc2kSubCert1_0_valid)

/-- Sub-certificate 1/1 for FC2K certificate 1 (`2` active super-chunks). -/
def fc2kSubCert1_1 : PrefixSubCert where
  corrLo := 8628221
  numSuperChunks := 20
  activeChunkMask := 0xc0000
  numChunks := 1
  qSub := 15342
  maxHi := 69036061
  chunks := [
    (4, { startWord := 1152, endWord := 1228, endBitCutoff := 4061, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (144, 3259), (145, 3243), (146, 3210), (147, 3180), (148, 3122), (149, 3150), (150, 3240), (151, 3232), (152, 3192), (153, 1856)
  ]

theorem fc2kSubCert1_1_valid : checkPrefixSubCert fc2kSubCert1_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf1_1 : VerifiedSubCertProfile fc2kSubCert1_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert1_1 fc2kSubCert1_1_valid)

def fc2kSubCerts1 : List PrefixSubCert := [fc2kSubCert1_0, fc2kSubCert1_1]

def fc2kPlan1 : MultiSubCertPlan where
  P := 25
  M := 1
  qSub := 15342
  qCert := 15342
  corrLo := 8628221
  maxHi := 69036061
  numOcts := 164
  routes := [
    [(0, 23)],
    [(0, 22)],
    [(0, 21)],
    [(0, 20)],
    [(1, 0)],
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
  windowCaps := []
  octWindowCaps := [
    { minWordIdx := 29, spanWords := 5, cap := 34137 },
    { minWordIdx := 38, spanWords := 6, cap := 37621 },
    { minWordIdx := 66, spanWords := 6, cap := 35814 },
    { minWordIdx := 66, spanWords := 19, cap := 90431 },
    { minWordIdx := 82, spanWords := 7, cap := 40698 },
    { minWordIdx := 82, spanWords := 22, cap := 96262 },
    { minWordIdx := 129, spanWords := 5, cap := 16516 },
    { minWordIdx := 155, spanWords := 6, cap := 0 }
  ]

theorem fc2kPlan1_valid : checkMultiSubCertPlan fc2kSubCerts1 fc2kPlan1 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs1 :
    ∀ g : Fin fc2kSubCerts1.length,
      VerifiedSubCertProfile (fc2kSubCerts1[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf1_0
  | ⟨1, _⟩ => fc2kSubProf1_1
  | ⟨k + 2, h⟩ => False.elim (by change k + 2 < 2 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 1. -/
noncomputable def fc2kPrefixProfile1 :
    GeneralPrefixProfile 25 15342 8628221 69036061 :=
  assembleGeneralPrefixProfile fc2kSubCerts1 fc2kPlan1 fc2kPlan1_valid fc2kSubProfs1

end Sude
