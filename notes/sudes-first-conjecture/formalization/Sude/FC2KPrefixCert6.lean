import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 6

Certifies `P = 28` power-of-two prime-pair stages (`qCert = 55842`, `6` chunk(s) of `9307`)
in `[157529207, 461091979]` via `11` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 45870`).
-/

namespace Sude

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_0 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 89
  activeChunkMask := 0x1e00000000008000000000f
  numChunks := 24
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (27, { startWord := 0, endWord := 53, endBitCutoff := 6539, subMod := 1 }),
    (27, { startWord := 54, endWord := 108, endBitCutoff := 263, subMod := 1 }),
    (27, { startWord := 109, endWord := 163, endBitCutoff := 3909, subMod := 1 }),
    (27, { startWord := 164, endWord := 218, endBitCutoff := 273, subMod := 1 }),
    (26, { startWord := 24, endWord := 76, endBitCutoff := 7473, subMod := 1 }),
    (22, { startWord := 0, endWord := 62, endBitCutoff := 4781, subMod := 1 }),
    (21, { startWord := 8, endWord := 66, endBitCutoff := 7124, subMod := 1 }),
    (21, { startWord := 67, endWord := 126, endBitCutoff := 1507, subMod := 1 }),
    (20, { startWord := 64, endWord := 128, endBitCutoff := 8130, subMod := 1 }),
    (20, { startWord := 129, endWord := 196, endBitCutoff := 6576, subMod := 1 }),
    (17, { startWord := 176, endWord := 248, endBitCutoff := 1180, subMod := 1 }),
    (16, { startWord := 2752, endWord := 2812, endBitCutoff := 6167, subMod := 1 }),
    (15, { startWord := 0, endWord := 89, endBitCutoff := 776, subMod := 1 }),
    (15, { startWord := 90, endWord := 197, endBitCutoff := 2269, subMod := 1 }),
    (14, { startWord := 160, endWord := 254, endBitCutoff := 3309, subMod := 1 }),
    (12, { startWord := 0, endWord := 94, endBitCutoff := 1275, subMod := 1 }),
    (12, { startWord := 95, endWord := 219, endBitCutoff := 2738, subMod := 1 }),
    (10, { startWord := 40, endWord := 162, endBitCutoff := 6738, subMod := 1 }),
    (6, { startWord := 112, endWord := 254, endBitCutoff := 5752, subMod := 1 }),
    (5, { startWord := 5440, endWord := 5501, endBitCutoff := 4889, subMod := 1 }),
    (5, { startWord := 5502, endWord := 5566, endBitCutoff := 4174, subMod := 1 }),
    (4, { startWord := 5568, endWord := 5631, endBitCutoff := 8043, subMod := 1 }),
    (4, { startWord := 5632, endWord := 5693, endBitCutoff := 7155, subMod := 1 }),
    (2, { startWord := 0, endWord := 174, endBitCutoff := 4350, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 7885), (1, 8619), (2, 8386), (3, 9228), (4, 9122), (5, 10046), (6, 10212), (7, 10000), (8, 9955), (9, 9726),
    (10, 9539), (11, 9391), (12, 10095), (13, 10411), (14, 11261), (15, 11262), (16, 10805), (17, 10709), (18, 10656), (19, 10608),
    (20, 10647), (21, 10705), (22, 11259), (23, 11326), (24, 11032), (25, 10037), (26, 9500), (27, 8141), (28, 7603), (29, 7455),
    (30, 6793), (31, 4717), (344, 2952), (345, 3733), (346, 3816), (347, 3868), (348, 3793), (349, 3806), (350, 3807), (351, 2146),
    (680, 2566), (681, 2695), (682, 3054), (683, 3724), (684, 3641), (685, 3649), (686, 3711), (687, 3589), (688, 3747), (689, 3579),
    (690, 3664), (691, 3715), (692, 3644), (693, 3688), (694, 3634), (695, 3315), (696, 3538), (697, 3750), (698, 3736), (699, 3736),
    (700, 3729), (701, 3595), (702, 3611), (703, 3537), (704, 3815), (705, 3698), (706, 3580), (707, 3745), (708, 3632), (709, 3689),
    (710, 2716), (711, 1962)
  ]

theorem fc2kSubCert6_0_valid : checkPrefixSubCert fc2kSubCert6_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_0 : VerifiedSubCertProfile fc2kSubCert6_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_0 fc2kSubCert6_0_valid)

/-- Sub-certificate 1/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_1 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 92
  activeChunkMask := 0xe0000000003800000000070
  numChunks := 21
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (27, { startWord := 256, endWord := 309, endBitCutoff := 7077, subMod := 1 }),
    (27, { startWord := 310, endWord := 364, endBitCutoff := 4982, subMod := 1 }),
    (26, { startWord := 280, endWord := 332, endBitCutoff := 2178, subMod := 1 }),
    (26, { startWord := 333, endWord := 386, endBitCutoff := 7530, subMod := 1 }),
    (26, { startWord := 387, endWord := 440, endBitCutoff := 1587, subMod := 1 }),
    (21, { startWord := 256, endWord := 324, endBitCutoff := 4051, subMod := 1 }),
    (20, { startWord := 256, endWord := 322, endBitCutoff := 667, subMod := 1 }),
    (20, { startWord := 323, endWord := 386, endBitCutoff := 6906, subMod := 1 }),
    (17, { startWord := 256, endWord := 342, endBitCutoff := 3302, subMod := 1 }),
    (17, { startWord := 343, endWord := 421, endBitCutoff := 5244, subMod := 1 }),
    (15, { startWord := 256, endWord := 373, endBitCutoff := 5423, subMod := 1 }),
    (14, { startWord := 256, endWord := 387, endBitCutoff := 4974, subMod := 1 }),
    (12, { startWord := 256, endWord := 401, endBitCutoff := 4336, subMod := 1 }),
    (11, { startWord := 344, endWord := 446, endBitCutoff := 7492, subMod := 1 }),
    (11, { startWord := 3008, endWord := 3070, endBitCutoff := 8010, subMod := 1 }),
    (11, { startWord := 3071, endWord := 3134, endBitCutoff := 292, subMod := 1 }),
    (10, { startWord := 256, endWord := 426, endBitCutoff := 4340, subMod := 1 }),
    (9, { startWord := 3136, endWord := 3194, endBitCutoff := 1618, subMod := 1 }),
    (6, { startWord := 256, endWord := 443, endBitCutoff := 1929, subMod := 1 }),
    (4, { startWord := 5696, endWord := 5757, endBitCutoff := 7584, subMod := 1 }),
    (3, { startWord := 5824, endWord := 5880, endBitCutoff := 6059, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (32, 10684), (33, 11225), (34, 11228), (35, 11487), (36, 11564), (37, 11837), (38, 11894), (39, 11856), (40, 11759), (41, 11418),
    (42, 11540), (43, 12471), (44, 12433), (45, 12185), (46, 11706), (47, 11161), (48, 10670), (49, 10382), (50, 9536), (51, 9234),
    (52, 8909), (53, 6773), (54, 5820), (55, 3517), (376, 3414), (377, 3753), (378, 3772), (379, 3642), (380, 3837), (381, 3794),
    (382, 3652), (383, 3754), (384, 3727), (385, 3664), (386, 3970), (387, 3669), (388, 3686), (389, 3708), (390, 3782), (391, 3207),
    (392, 3825), (393, 3897), (394, 3816), (395, 3790), (396, 3153), (397, 2768), (398, 2677), (399, 806), (712, 2576), (713, 2638),
    (714, 3021), (715, 3694), (716, 3626), (717, 3667), (718, 3664), (719, 3121), (720, 1365), (721, 1345), (722, 1363), (723, 1372),
    (724, 1362), (725, 1392), (726, 1331), (727, 1354), (728, 2833), (729, 2580), (730, 2712), (731, 2540), (732, 2674), (733, 2680),
    (734, 2670), (735, 262)
  ]

theorem fc2kSubCert6_1_valid : checkPrefixSubCert fc2kSubCert6_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_1 : VerifiedSubCertProfile fc2kSubCert6_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_1 fc2kSubCert6_1_valid)

/-- Sub-certificate 2/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_2 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 52
  activeChunkMask := 0xc0000e0000780
  numChunks := 25
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (26, { startWord := 472, endWord := 525, endBitCutoff := 218, subMod := 1 }),
    (26, { startWord := 526, endWord := 579, endBitCutoff := 7857, subMod := 1 }),
    (25, { startWord := 496, endWord := 548, endBitCutoff := 7749, subMod := 1 }),
    (25, { startWord := 549, endWord := 602, endBitCutoff := 2472, subMod := 1 }),
    (25, { startWord := 603, endWord := 655, endBitCutoff := 7784, subMod := 1 }),
    (25, { startWord := 1856, endWord := 1910, endBitCutoff := 5019, subMod := 1 }),
    (22, { startWord := 448, endWord := 509, endBitCutoff := 7927, subMod := 1 }),
    (21, { startWord := 448, endWord := 507, endBitCutoff := 5842, subMod := 1 }),
    (21, { startWord := 508, endWord := 570, endBitCutoff := 4016, subMod := 1 }),
    (20, { startWord := 448, endWord := 527, endBitCutoff := 6072, subMod := 1 }),
    (20, { startWord := 528, endWord := 604, endBitCutoff := 6982, subMod := 1 }),
    (19, { startWord := 1856, endWord := 1926, endBitCutoff := 881, subMod := 1 }),
    (18, { startWord := 632, endWord := 692, endBitCutoff := 7228, subMod := 1 }),
    (18, { startWord := 1928, endWord := 1990, endBitCutoff := 1618, subMod := 1 }),
    (17, { startWord := 448, endWord := 545, endBitCutoff := 655, subMod := 1 }),
    (17, { startWord := 546, endWord := 644, endBitCutoff := 3511, subMod := 1 }),
    (15, { startWord := 448, endWord := 555, endBitCutoff := 2099, subMod := 1 }),
    (15, { startWord := 556, endWord := 659, endBitCutoff := 7701, subMod := 1 }),
    (14, { startWord := 448, endWord := 592, endBitCutoff := 1374, subMod := 1 }),
    (14, { startWord := 593, endWord := 697, endBitCutoff := 1996, subMod := 1 }),
    (12, { startWord := 448, endWord := 609, endBitCutoff := 7640, subMod := 1 }),
    (11, { startWord := 448, endWord := 636, endBitCutoff := 1288, subMod := 1 }),
    (10, { startWord := 448, endWord := 665, endBitCutoff := 5515, subMod := 1 }),
    (9, { startWord := 3200, endWord := 3270, endBitCutoff := 3664, subMod := 1 }),
    (6, { startWord := 448, endWord := 691, endBitCutoff := 431, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (56, 11485), (57, 11680), (58, 11606), (59, 11787), (60, 11687), (61, 12156), (62, 12737), (63, 12604), (64, 12329), (65, 12188),
    (66, 12475), (67, 12731), (68, 12616), (69, 12794), (70, 12881), (71, 12572), (72, 12281), (73, 12095), (74, 11782), (75, 11997),
    (76, 11138), (77, 11331), (78, 10994), (79, 11308), (80, 10955), (81, 9920), (82, 8271), (83, 6749), (84, 6515), (85, 6057),
    (86, 4820), (87, 1818), (232, 2904), (233, 3814), (234, 4097), (235, 4880), (236, 4818), (237, 4800), (238, 4607), (239, 3538),
    (240, 3378), (241, 3656), (242, 4426), (243, 4188), (244, 3813), (245, 3795), (246, 3819), (247, 3931), (248, 3544), (249, 2616),
    (250, 1542), (251, 1339), (252, 951), (400, 3349), (401, 3788), (402, 4187), (403, 4746), (404, 4768), (405, 4710), (406, 4554),
    (407, 4690), (408, 4384), (409, 2084), (410, 1389), (411, 1418), (412, 1367), (413, 1101)
  ]

theorem fc2kSubCert6_2_valid : checkPrefixSubCert fc2kSubCert6_2 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_2 : VerifiedSubCertProfile fc2kSubCert6_2 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_2 fc2kSubCert6_2_valid)

/-- Sub-certificate 3/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_3 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 56
  activeChunkMask := 0xe0100700c00000
  numChunks := 12
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (25, { startWord := 2048, endWord := 2103, endBitCutoff := 488, subMod := 1 }),
    (25, { startWord := 2104, endWord := 2158, endBitCutoff := 5268, subMod := 1 }),
    (24, { startWord := 1408, endWord := 1468, endBitCutoff := 1197, subMod := 1 }),
    (24, { startWord := 1469, endWord := 1522, endBitCutoff := 7227, subMod := 1 }),
    (24, { startWord := 2136, endWord := 2189, endBitCutoff := 4850, subMod := 1 }),
    (24, { startWord := 2816, endWord := 2870, endBitCutoff := 3768, subMod := 1 }),
    (19, { startWord := 1408, endWord := 1468, endBitCutoff := 2983, subMod := 1 }),
    (18, { startWord := 2048, endWord := 2112, endBitCutoff := 8171, subMod := 1 }),
    (16, { startWord := 2160, endWord := 2226, endBitCutoff := 2373, subMod := 1 }),
    (15, { startWord := 1472, endWord := 1533, endBitCutoff := 5647, subMod := 1 }),
    (9, { startWord := 3392, endWord := 3454, endBitCutoff := 4733, subMod := 1 }),
    (9, { startWord := 3455, endWord := 3524, endBitCutoff := 7111, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (176, 2508), (177, 2447), (178, 2846), (179, 3701), (180, 3710), (181, 3670), (182, 3704), (183, 3042), (184, 4487), (185, 4642),
    (186, 4093), (187, 3848), (188, 3784), (189, 3909), (190, 3197), (191, 2254), (256, 2688), (257, 3454), (258, 3779), (259, 3804),
    (260, 3624), (261, 4342), (262, 4544), (263, 4650), (264, 3835), (265, 3112), (266, 2592), (267, 4002), (268, 3816), (269, 3735),
    (270, 4318), (271, 4601), (272, 4697), (273, 4340), (274, 3749), (275, 3411), (276, 2690), (277, 2657), (278, 1323), (352, 2260),
    (353, 2738), (354, 2826), (355, 2726), (356, 2784), (357, 2726), (358, 2507), (359, 47), (424, 2704), (425, 2649), (426, 3022),
    (427, 3622), (428, 3500), (429, 3642), (430, 3542), (431, 3413), (432, 3664), (433, 3451), (434, 3530), (435, 3627), (436, 3613),
    (437, 4491), (438, 4623), (439, 4577), (440, 3190), (441, 1410), (442, 1319), (443, 1365), (444, 195)
  ]

theorem fc2kSubCert6_3_valid : checkPrefixSubCert fc2kSubCert6_3 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_3 : VerifiedSubCertProfile fc2kSubCert6_3 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_3 fc2kSubCert6_3_valid)

/-- Sub-certificate 4/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_4 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 69
  activeChunkMask := 0x1c6100610000000000
  numChunks := 11
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (24, { startWord := 2904, endWord := 2959, endBitCutoff := 4230, subMod := 1 }),
    (24, { startWord := 3584, endWord := 3640, endBitCutoff := 30, subMod := 1 }),
    (23, { startWord := 2560, endWord := 2620, endBitCutoff := 5395, subMod := 1 }),
    (23, { startWord := 3904, endWord := 3960, endBitCutoff := 313, subMod := 1 }),
    (23, { startWord := 3961, endWord := 4017, endBitCutoff := 3064, subMod := 1 }),
    (16, { startWord := 2560, endWord := 2619, endBitCutoff := 5437, subMod := 1 }),
    (11, { startWord := 2880, endWord := 2950, endBitCutoff := 2694, subMod := 1 }),
    (9, { startWord := 3904, endWord := 3966, endBitCutoff := 1898, subMod := 1 }),
    (8, { startWord := 3968, endWord := 4029, endBitCutoff := 3633, subMod := 1 }),
    (7, { startWord := 4224, endWord := 4288, endBitCutoff := 7727, subMod := 1 }),
    (7, { startWord := 4289, endWord := 4360, endBitCutoff := 2678, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (320, 3373), (321, 3728), (322, 3752), (323, 3644), (324, 3721), (325, 3702), (326, 3647), (327, 2354), (360, 2650), (361, 2675),
    (362, 3033), (363, 4373), (364, 4419), (365, 4537), (366, 4379), (367, 4232), (368, 4104), (369, 2474), (370, 352), (448, 2229),
    (449, 2620), (450, 2706), (451, 2668), (452, 2655), (453, 2667), (454, 2702), (455, 367), (488, 3651), (489, 3739), (490, 3702),
    (491, 3753), (492, 3709), (493, 3693), (494, 3726), (495, 3068), (496, 3671), (497, 3728), (498, 3715), (499, 3628), (500, 3697),
    (501, 3628), (502, 2878), (503, 1856), (528, 2650), (529, 2778), (530, 3004), (531, 3543), (532, 3587), (533, 4245), (534, 4506),
    (535, 4604), (536, 4579), (537, 4505), (538, 4661), (539, 4601), (540, 3921), (541, 3489), (542, 3454), (543, 3529), (544, 3380),
    (545, 113)
  ]

theorem fc2kSubCert6_4_valid : checkPrefixSubCert fc2kSubCert6_4 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_4 : VerifiedSubCertProfile fc2kSubCert6_4 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_4 fc2kSubCert6_4_valid)

/-- Sub-certificate 5/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_5 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 76
  activeChunkMask := 0x8638000000000006800
  numChunks := 11
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (23, { startWord := 4080, endWord := 4135, endBitCutoff := 5535, subMod := 1 }),
    (23, { startWord := 4136, endWord := 4192, endBitCutoff := 446, subMod := 1 }),
    (23, { startWord := 4464, endWord := 4519, endBitCutoff := 1452, subMod := 1 }),
    (22, { startWord := 704, endWord := 755, endBitCutoff := 5895, subMod := 1 }),
    (19, { startWord := 832, endWord := 884, endBitCutoff := 7760, subMod := 1 }),
    (18, { startWord := 888, endWord := 946, endBitCutoff := 5151, subMod := 1 }),
    (16, { startWord := 704, endWord := 763, endBitCutoff := 3894, subMod := 1 }),
    (8, { startWord := 4032, endWord := 4089, endBitCutoff := 582, subMod := 1 }),
    (7, { startWord := 4096, endWord := 4163, endBitCutoff := 5898, subMod := 1 }),
    (7, { startWord := 4416, endWord := 4486, endBitCutoff := 6527, subMod := 1 }),
    (4, { startWord := 4800, endWord := 4861, endBitCutoff := 5699, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (88, 3431), (89, 3940), (90, 3914), (91, 3853), (92, 3861), (93, 3905), (94, 3276), (95, 1741), (104, 1462), (105, 1454),
    (106, 1942), (107, 2874), (108, 2917), (109, 3688), (110, 3652), (111, 3881), (112, 4438), (113, 4014), (114, 3905), (115, 3809),
    (116, 2815), (117, 2842), (118, 1922), (119, 920), (504, 2621), (505, 2799), (506, 2610), (507, 2632), (508, 2736), (509, 2671),
    (510, 3662), (511, 1631), (512, 3526), (513, 3512), (514, 3566), (515, 3454), (516, 3508), (517, 3624), (518, 3483), (519, 3533),
    (520, 2315), (521, 1349), (522, 1302), (523, 1301), (524, 7), (552, 3018), (553, 3552), (554, 3524), (555, 3488), (556, 3467),
    (557, 3488), (558, 4432), (559, 4486), (560, 4265), (561, 2719), (562, 2677), (563, 2667), (564, 2571), (565, 1307), (566, 874),
    (600, 2965), (601, 3747), (602, 3656), (603, 3779), (604, 3727), (605, 3741), (606, 3727), (607, 2579)
  ]

theorem fc2kSubCert6_5_valid : checkPrefixSubCert fc2kSubCert6_5 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_5 : VerifiedSubCertProfile fc2kSubCert6_5 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_5 fc2kSubCert6_5_valid)

/-- Sub-certificate 6/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_6 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 25
  activeChunkMask := 0x13f9000
  numChunks := 12
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (22, { startWord := 960, endWord := 1011, endBitCutoff := 5480, subMod := 1 }),
    (22, { startWord := 1112, endWord := 1165, endBitCutoff := 2813, subMod := 1 }),
    (22, { startWord := 1166, endWord := 1218, endBitCutoff := 2569, subMod := 1 }),
    (21, { startWord := 1088, endWord := 1147, endBitCutoff := 3311, subMod := 1 }),
    (19, { startWord := 1184, endWord := 1241, endBitCutoff := 777, subMod := 1 }),
    (19, { startWord := 1242, endWord := 1296, endBitCutoff := 4577, subMod := 1 }),
    (19, { startWord := 1297, endWord := 1356, endBitCutoff := 4796, subMod := 1 }),
    (18, { startWord := 960, endWord := 1021, endBitCutoff := 3600, subMod := 1 }),
    (18, { startWord := 1022, endWord := 1073, endBitCutoff := 6562, subMod := 1 }),
    (17, { startWord := 768, endWord := 819, endBitCutoff := 6718, subMod := 1 }),
    (16, { startWord := 1016, endWord := 1083, endBitCutoff := 1682, subMod := 1 }),
    (16, { startWord := 1536, endWord := 1589, endBitCutoff := 6883, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (96, 1987), (97, 2883), (98, 2846), (99, 2876), (100, 2873), (101, 2812), (102, 2135), (103, 202), (120, 2628), (121, 3478),
    (122, 3803), (123, 3819), (124, 3759), (125, 3738), (126, 3116), (127, 4343), (128, 4933), (129, 4837), (130, 4987), (131, 5056),
    (132, 5160), (133, 5119), (134, 4101), (135, 2272), (136, 1293), (137, 1246), (138, 1264), (139, 2612), (140, 2689), (141, 3602),
    (142, 4074), (143, 3438), (144, 2784), (145, 2788), (146, 3209), (147, 3804), (148, 3793), (149, 3843), (150, 4372), (151, 5055),
    (152, 4243), (153, 3943), (154, 2907), (155, 2758), (156, 2774), (157, 2659), (158, 2816), (159, 2776), (160, 3583), (161, 4057),
    (162, 4013), (163, 3851), (164, 3828), (165, 3839), (166, 3928), (167, 3806), (168, 3867), (169, 3526), (170, 2694), (171, 2701),
    (172, 1664), (173, 892), (192, 2239), (193, 2792), (194, 2755), (195, 2831), (196, 2837), (197, 2655), (198, 2429), (199, 76)
  ]

theorem fc2kSubCert6_6_valid : checkPrefixSubCert fc2kSubCert6_6 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_6 : VerifiedSubCertProfile fc2kSubCert6_6 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_6 fc2kSubCert6_6_valid)

/-- Sub-certificate 7/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_7 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 40
  activeChunkMask := 0xf81e000000
  numChunks := 16
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (14, { startWord := 1600, endWord := 1653, endBitCutoff := 2119, subMod := 1 }),
    (14, { startWord := 1654, endWord := 1707, endBitCutoff := 1088, subMod := 1 }),
    (13, { startWord := 1664, endWord := 1726, endBitCutoff := 1687, subMod := 1 }),
    (13, { startWord := 1727, endWord := 1780, endBitCutoff := 1404, subMod := 1 }),
    (13, { startWord := 1781, endWord := 1834, endBitCutoff := 3988, subMod := 1 }),
    (13, { startWord := 2240, endWord := 2294, endBitCutoff := 142, subMod := 1 }),
    (13, { startWord := 2295, endWord := 2348, endBitCutoff := 5805, subMod := 1 }),
    (13, { startWord := 2349, endWord := 2403, endBitCutoff := 1964, subMod := 1 }),
    (12, { startWord := 2240, endWord := 2307, endBitCutoff := 5354, subMod := 1 }),
    (12, { startWord := 2344, endWord := 2410, endBitCutoff := 2845, subMod := 1 }),
    (11, { startWord := 1784, endWord := 1848, endBitCutoff := 397, subMod := 1 }),
    (10, { startWord := 1712, endWord := 1779, endBitCutoff := 4897, subMod := 1 }),
    (10, { startWord := 2408, endWord := 2462, endBitCutoff := 1943, subMod := 1 }),
    (10, { startWord := 2463, endWord := 2516, endBitCutoff := 7738, subMod := 1 }),
    (9, { startWord := 2496, endWord := 2554, endBitCutoff := 7062, subMod := 1 }),
    (8, { startWord := 2416, endWord := 2484, endBitCutoff := 5492, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (200, 2634), (201, 2868), (202, 2733), (203, 2772), (204, 2839), (205, 2814), (206, 2587), (207, 2792), (208, 4914), (209, 5079),
    (210, 5077), (211, 5167), (212, 4890), (213, 3695), (214, 4998), (215, 4715), (216, 4992), (217, 5109), (218, 4925), (219, 4923),
    (220, 4981), (221, 4993), (222, 3625), (223, 4949), (224, 5012), (225, 4779), (226, 4845), (227, 5000), (228, 5134), (229, 3552),
    (230, 2863), (231, 42), (280, 4943), (281, 4977), (282, 4854), (283, 5006), (284, 4934), (285, 4811), (286, 4633), (287, 4983),
    (288, 3810), (289, 2786), (290, 2830), (291, 2805), (292, 2762), (293, 4771), (294, 4968), (295, 4945), (296, 4934), (297, 4925),
    (298, 4970), (299, 4932), (300, 3682), (301, 3398), (302, 4986), (303, 4905), (304, 4994), (305, 4990), (306, 4956), (307, 4644),
    (308, 4802), (309, 4945), (310, 4014), (311, 2820), (312, 4925), (313, 4861), (314, 4030), (315, 2708), (316, 2730), (317, 2786),
    (318, 2837), (319, 934)
  ]

theorem fc2kSubCert6_7_valid : checkPrefixSubCert fc2kSubCert6_7 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_7 : VerifiedSubCertProfile fc2kSubCert6_7 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_7 fc2kSubCert6_7_valid)

/-- Sub-certificate 8/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_8 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 73
  activeChunkMask := 0x1801e10060000000000
  numChunks := 14
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (8, { startWord := 2624, endWord := 2678, endBitCutoff := 4214, subMod := 1 }),
    (8, { startWord := 2679, endWord := 2733, endBitCutoff := 1422, subMod := 1 }),
    (8, { startWord := 3328, endWord := 3382, endBitCutoff := 6136, subMod := 1 }),
    (7, { startWord := 2680, endWord := 2745, endBitCutoff := 2434, subMod := 1 }),
    (7, { startWord := 4544, endWord := 4598, endBitCutoff := 7758, subMod := 1 }),
    (6, { startWord := 3648, endWord := 3703, endBitCutoff := 1442, subMod := 1 }),
    (6, { startWord := 3704, endWord := 3758, endBitCutoff := 6492, subMod := 1 }),
    (6, { startWord := 3759, endWord := 3814, endBitCutoff := 3129, subMod := 1 }),
    (5, { startWord := 3648, endWord := 3717, endBitCutoff := 4960, subMod := 1 }),
    (5, { startWord := 3718, endWord := 3787, endBitCutoff := 5076, subMod := 1 }),
    (5, { startWord := 3816, endWord := 3871, endBitCutoff := 5057, subMod := 1 }),
    (5, { startWord := 4592, endWord := 4649, endBitCutoff := 4868, subMod := 1 }),
    (4, { startWord := 3840, endWord := 3901, endBitCutoff := 6121, subMod := 1 }),
    (4, { startWord := 4600, endWord := 4666, endBitCutoff := 5349, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (328, 2724), (329, 2785), (330, 2645), (331, 2800), (332, 2688), (333, 2762), (334, 2589), (335, 4973), (336, 4994), (337, 4894),
    (338, 4935), (339, 4943), (340, 4809), (341, 4116), (342, 2738), (343, 447), (416, 2621), (417, 2730), (418, 2738), (419, 2757),
    (420, 2768), (421, 2664), (422, 2336), (456, 4874), (457, 4803), (458, 4754), (459, 4841), (460, 4902), (461, 4875), (462, 4541),
    (463, 4869), (464, 4773), (465, 4740), (466, 4823), (467, 4753), (468, 4899), (469, 4861), (470, 4828), (471, 4872), (472, 4855),
    (473, 3601), (474, 2740), (475, 2702), (476, 2164), (477, 2626), (478, 2750), (479, 2750), (480, 4759), (481, 4806), (482, 4754),
    (483, 4780), (484, 2671), (485, 2680), (486, 2806), (487, 1846), (568, 2662), (569, 2778), (570, 2652), (571, 2730), (572, 2718),
    (573, 2799), (574, 4417), (575, 4736), (576, 4846), (577, 4610), (578, 4772), (579, 4727), (580, 4845), (581, 3027), (582, 2663),
    (583, 860)
  ]

theorem fc2kSubCert6_8_valid : checkPrefixSubCert fc2kSubCert6_8 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_8 : VerifiedSubCertProfile fc2kSubCert6_8 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_8 fc2kSubCert6_8_valid)

/-- Sub-certificate 9/10 for FC2K certificate 6 (`9` active super-chunks). -/
def fc2kSubCert6_9 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 97
  activeChunkMask := 0x1f00036000000000000000000
  numChunks := 13
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (3, { startWord := 5888, endWord := 5945, endBitCutoff := 2604, subMod := 1 }),
    (3, { startWord := 5946, endWord := 6001, endBitCutoff := 8077, subMod := 1 }),
    (3, { startWord := 6002, endWord := 6059, endBitCutoff := 801, subMod := 1 }),
    (3, { startWord := 6060, endWord := 6117, endBitCutoff := 670, subMod := 1 }),
    (3, { startWord := 6118, endWord := 6175, endBitCutoff := 4534, subMod := 1 }),
    (2, { startWord := 4672, endWord := 4727, endBitCutoff := 7388, subMod := 1 }),
    (2, { startWord := 4728, endWord := 4783, endBitCutoff := 1004, subMod := 1 }),
    (2, { startWord := 4864, endWord := 4919, endBitCutoff := 5544, subMod := 1 }),
    (2, { startWord := 4920, endWord := 4975, endBitCutoff := 850, subMod := 1 }),
    (1, { startWord := 4728, endWord := 4795, endBitCutoff := 6134, subMod := 1 }),
    (1, { startWord := 4864, endWord := 4934, endBitCutoff := 7717, subMod := 1 }),
    (0, { startWord := 5888, endWord := 5959, endBitCutoff := 6605, subMod := 1 }),
    (0, { startWord := 5960, endWord := 6032, endBitCutoff := 3429, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (584, 2670), (585, 2624), (586, 2652), (587, 2616), (588, 2710), (589, 2668), (590, 2674), (591, 4774), (592, 4780), (593, 4690),
    (594, 4882), (595, 4710), (596, 4902), (597, 4596), (598, 2677), (599, 1217), (608, 4694), (609, 4742), (610, 4816), (611, 4748),
    (612, 4756), (613, 4698), (614, 4696), (615, 4868), (616, 4578), (617, 2772), (618, 2630), (619, 2752), (620, 2692), (621, 2400),
    (736, 4518), (737, 4630), (738, 4734), (739, 4626), (740, 4742), (741, 4734), (742, 4708), (743, 4520), (744, 4688), (745, 4760),
    (746, 4788), (747, 4718), (748, 4692), (749, 4578), (750, 4586), (751, 4742), (752, 4682), (753, 4726), (754, 2674), (755, 2682),
    (756, 2532), (757, 2335), (758, 2635), (759, 2556), (760, 2682), (761, 2548), (762, 2592), (763, 2596), (764, 2344), (765, 2524),
    (766, 2560), (767, 2582), (768, 2596), (769, 2656), (770, 2540), (771, 2492)
  ]

theorem fc2kSubCert6_9_valid : checkPrefixSubCert fc2kSubCert6_9 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_9 : VerifiedSubCertProfile fc2kSubCert6_9 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_9 fc2kSubCert6_9_valid)

/-- Sub-certificate 10/10 for FC2K certificate 6 (`7` active super-chunks). -/
def fc2kSubCert6_10 : PrefixSubCert where
  corrLo := 157529207
  numSuperChunks := 85
  activeChunkMask := 0x1fc0000000000000000000
  numChunks := 9
  qSub := 9307
  maxHi := 461091979
  chunks := [
    (2, { startWord := 4992, endWord := 5048, endBitCutoff := 7299, subMod := 1 }),
    (1, { startWord := 4992, endWord := 5059, endBitCutoff := 172, subMod := 1 }),
    (1, { startWord := 5060, endWord := 5116, endBitCutoff := 9, subMod := 1 }),
    (1, { startWord := 5117, endWord := 5172, endBitCutoff := 6990, subMod := 1 }),
    (1, { startWord := 5173, endWord := 5228, endBitCutoff := 7644, subMod := 1 }),
    (0, { startWord := 5176, endWord := 5243, endBitCutoff := 5512, subMod := 1 }),
    (0, { startWord := 5244, endWord := 5300, endBitCutoff := 1141, subMod := 1 }),
    (0, { startWord := 5301, endWord := 5356, endBitCutoff := 693, subMod := 1 }),
    (0, { startWord := 5357, endWord := 5413, endBitCutoff := 6535, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (624, 4666), (625, 4724), (626, 4808), (627, 4816), (628, 4746), (629, 4782), (630, 4752), (631, 2922), (632, 2334), (633, 2572),
    (634, 2792), (635, 2604), (636, 2720), (637, 2542), (638, 2742), (639, 2364), (640, 2622), (641, 2718), (642, 2586), (643, 2682),
    (644, 2716), (645, 2672), (646, 2624), (647, 4738), (648, 4872), (649, 4744), (650, 4690), (651, 4718), (652, 4706), (653, 3962),
    (654, 2530), (655, 2556), (656, 2504), (657, 2624), (658, 2718), (659, 2706), (660, 2720), (661, 2598), (662, 2462), (663, 2698),
    (664, 2662), (665, 2638), (666, 2674), (667, 2716), (668, 2722), (669, 2388), (670, 2578), (671, 2630), (672, 2688), (673, 2622),
    (674, 2566), (675, 2672), (676, 1918)
  ]

theorem fc2kSubCert6_10_valid : checkPrefixSubCert fc2kSubCert6_10 = true := by
  decide +kernel

private noncomputable def fc2kSubProf6_10 : VerifiedSubCertProfile fc2kSubCert6_10 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert6_10 fc2kSubCert6_10_valid)

def fc2kSubCerts6 : List PrefixSubCert := [fc2kSubCert6_0, fc2kSubCert6_1, fc2kSubCert6_2, fc2kSubCert6_3, fc2kSubCert6_4, fc2kSubCert6_5, fc2kSubCert6_6, fc2kSubCert6_7, fc2kSubCert6_8, fc2kSubCert6_9, fc2kSubCert6_10]

def fc2kPlan6 : MultiSubCertPlan where
  P := 28
  M := 6
  qSub := 9307
  qCert := 55842
  corrLo := 157529207
  maxHi := 461091979
  numOcts := 1306
  routes := [
    [(10, 5), (10, 6), (10, 7), (10, 8), (9, 11), (9, 12)],
    [(9, 9), (9, 10), (10, 1), (10, 2), (10, 3), (10, 4)],
    [(0, 23), (9, 5), (9, 6), (9, 7), (9, 8), (10, 0)],
    [(1, 20), (9, 0), (9, 1), (9, 2), (9, 3), (9, 4)],
    [(8, 12), (8, 13), (5, 10), (0, 21), (0, 22), (1, 19)],
    [(8, 8), (8, 9), (8, 10), (8, 11), (0, 19), (0, 20)],
    [(0, 18), (1, 18), (2, 24), (8, 5), (8, 6), (8, 7)],
    [(8, 3), (5, 8), (4, 9), (4, 10), (5, 9), (8, 4)],
    [(7, 15), (8, 0), (8, 1), (8, 2), (4, 8), (5, 7)],
    [(7, 14), (1, 17), (2, 23), (3, 10), (3, 11), (4, 7)],
    [(0, 17), (1, 16), (2, 22), (7, 11), (7, 12), (7, 13)],
    [(1, 13), (2, 21), (7, 10), (4, 6), (1, 14), (1, 15)],
    [(0, 15), (0, 16), (1, 12), (2, 20), (7, 8), (7, 9)],
    [(7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)],
    [(0, 14), (1, 11), (2, 18), (2, 19), (7, 0), (7, 1)],
    [(0, 12), (0, 13), (1, 10), (2, 16), (2, 17), (3, 9)],
    [(5, 6), (6, 10), (6, 11), (3, 8), (4, 5), (0, 11)],
    [(0, 10), (1, 8), (1, 9), (2, 14), (2, 15), (6, 9)],
    [(2, 12), (5, 5), (6, 7), (6, 8), (2, 13), (3, 7)],
    [(5, 4), (6, 4), (6, 5), (6, 6), (3, 6), (2, 11)],
    [(0, 8), (0, 9), (1, 6), (1, 7), (2, 9), (2, 10)],
    [(0, 6), (0, 7), (1, 5), (2, 7), (2, 8), (6, 3)],
    [(0, 5), (2, 6), (5, 3), (6, 0), (6, 1), (6, 2)],
    [(4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2)],
    [(3, 2), (3, 3), (3, 4), (3, 5), (4, 0), (4, 1)],
    [(2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1)],
    [(0, 4), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1)],
    [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1)]
  ]
  windowCaps := []
  octWindowCaps := [
    { minWordIdx := 87, spanWords := 42, cap := 179059 },
    { minWordIdx := 87, spanWords := 44, cap := 184460 },
    { minWordIdx := 265, spanWords := 42, cap := 174627 },
    { minWordIdx := 265, spanWords := 57, cap := 225362 },
    { minWordIdx := 421, spanWords := 48, cap := 186140 },
    { minWordIdx := 421, spanWords := 190, cap := 624894 },
    { minWordIdx := 472, spanWords := 71, cap := 250071 },
    { minWordIdx := 663, spanWords := 42, cap := 144217 },
    { minWordIdx := 720, spanWords := 63, cap := 160133 },
    { minWordIdx := 720, spanWords := 248, cap := 160133 },
    { minWordIdx := 1023, spanWords := 44, cap := 0 },
    { minWordIdx := 1024, spanWords := 42, cap := 0 },
    { minWordIdx := 1069, spanWords := 79, cap := 0 },
    { minWordIdx := 1069, spanWords := 314, cap := 0 },
    { minWordIdx := 1544, spanWords := 57, cap := 0 },
    { minWordIdx := 1558, spanWords := 42, cap := 0 },
    { minWordIdx := 1988, spanWords := 42, cap := 0 },
    { minWordIdx := 2150, spanWords := 71, cap := 0 }
  ]

theorem fc2kPlan6_valid : checkMultiSubCertPlan fc2kSubCerts6 fc2kPlan6 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs6 :
    ∀ g : Fin fc2kSubCerts6.length,
      VerifiedSubCertProfile (fc2kSubCerts6[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf6_0
  | ⟨1, _⟩ => fc2kSubProf6_1
  | ⟨2, _⟩ => fc2kSubProf6_2
  | ⟨3, _⟩ => fc2kSubProf6_3
  | ⟨4, _⟩ => fc2kSubProf6_4
  | ⟨5, _⟩ => fc2kSubProf6_5
  | ⟨6, _⟩ => fc2kSubProf6_6
  | ⟨7, _⟩ => fc2kSubProf6_7
  | ⟨8, _⟩ => fc2kSubProf6_8
  | ⟨9, _⟩ => fc2kSubProf6_9
  | ⟨10, _⟩ => fc2kSubProf6_10
  | ⟨k + 11, h⟩ => False.elim (by change k + 11 < 11 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 6. -/
noncomputable def fc2kPrefixProfile6 :
    GeneralPrefixProfile 28 55842 157529207 461091979 :=
  assembleGeneralPrefixProfile fc2kSubCerts6 fc2kPlan6 fc2kPlan6_valid fc2kSubProfs6

end Sude
