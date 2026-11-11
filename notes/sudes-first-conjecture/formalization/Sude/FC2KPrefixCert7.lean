import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 7

Certifies `P = 28` power-of-two prime-pair stages (`qCert = 93042`, `6` chunk(s) of `15507`)
in `[347562017, 864641065]` via `18` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 83521`).
-/

namespace Sude

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_0 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 89
  activeChunkMask := 0x1e000000000180000000007
  numChunks := 11
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (27, { startWord := 0, endWord := 95, endBitCutoff := 2568, subMod := 1 }),
    (27, { startWord := 96, endWord := 191, endBitCutoff := 5743, subMod := 1 }),
    (26, { startWord := 24, endWord := 117, endBitCutoff := 3519, subMod := 1 }),
    (26, { startWord := 2752, endWord := 2848, endBitCutoff := 6891, subMod := 1 }),
    (20, { startWord := 0, endWord := 114, endBitCutoff := 8068, subMod := 1 }),
    (18, { startWord := 48, endWord := 178, endBitCutoff := 1929, subMod := 1 }),
    (17, { startWord := 2752, endWord := 2867, endBitCutoff := 6796, subMod := 1 }),
    (14, { startWord := 0, endWord := 169, endBitCutoff := 1602, subMod := 1 }),
    (13, { startWord := 16, endWord := 185, endBitCutoff := 7831, subMod := 1 }),
    (11, { startWord := 5440, endWord := 5563, endBitCutoff := 7774, subMod := 1 }),
    (11, { startWord := 5564, endWord := 5680, endBitCutoff := 623, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 4510), (1, 4604), (2, 6310), (3, 6858), (4, 7095), (5, 7444), (6, 8297), (7, 8535), (8, 8571), (9, 8717),
    (10, 8662), (11, 8527), (12, 8774), (13, 8571), (14, 8056), (15, 7383), (16, 7328), (17, 7434), (18, 7454), (19, 7358),
    (20, 7016), (21, 5780), (22, 4784), (23, 2509), (344, 3618), (345, 4598), (346, 4613), (347, 4625), (348, 4574), (349, 4561),
    (350, 4566), (351, 4670), (352, 4747), (353, 4665), (354, 4631), (355, 4769), (356, 2695), (357, 2588), (358, 1908), (359, 200),
    (680, 2523), (681, 2551), (682, 2746), (683, 3333), (684, 3468), (685, 3974), (686, 4371), (687, 4424), (688, 4542), (689, 4367),
    (690, 4390), (691, 4503), (692, 4421), (693, 4417), (694, 4374), (695, 4390), (696, 4373), (697, 3903), (698, 3418), (699, 3293),
    (700, 3433), (701, 3440), (702, 3287), (703, 3388), (704, 3387), (705, 3305), (706, 3040), (707, 2516), (708, 2458), (709, 2479),
    (710, 35)
  ]

theorem fc2kSubCert7_0_valid : checkPrefixSubCert fc2kSubCert7_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_0 : VerifiedSubCertProfile fc2kSubCert7_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_0 fc2kSubCert7_0_valid)

/-- Sub-certificate 1/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_1 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 93
  activeChunkMask := 0x1e0000000001800000000070
  numChunks := 11
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (27, { startWord := 256, endWord := 351, endBitCutoff := 4293, subMod := 1 }),
    (27, { startWord := 352, endWord := 447, endBitCutoff := 7361, subMod := 1 }),
    (26, { startWord := 280, endWord := 374, endBitCutoff := 7370, subMod := 1 }),
    (26, { startWord := 3008, endWord := 3104, endBitCutoff := 5374, subMod := 1 }),
    (20, { startWord := 256, endWord := 372, endBitCutoff := 3816, subMod := 1 }),
    (18, { startWord := 256, endWord := 393, endBitCutoff := 5916, subMod := 1 }),
    (17, { startWord := 3008, endWord := 3123, endBitCutoff := 6284, subMod := 1 }),
    (14, { startWord := 256, endWord := 428, endBitCutoff := 6966, subMod := 1 }),
    (13, { startWord := 256, endWord := 430, endBitCutoff := 5474, subMod := 1 }),
    (11, { startWord := 5696, endWord := 5819, endBitCutoff := 4592, subMod := 1 }),
    (11, { startWord := 5820, endWord := 5934, endBitCutoff := 8165, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (32, 6801), (33, 7422), (34, 7575), (35, 8202), (36, 8046), (37, 8503), (38, 8694), (39, 8704), (40, 8676), (41, 8667),
    (42, 8614), (43, 8630), (44, 8540), (45, 8696), (46, 8166), (47, 7286), (48, 7374), (49, 6876), (50, 6460), (51, 6006),
    (52, 5509), (53, 4607), (54, 1271), (55, 1252), (376, 3584), (377, 4581), (378, 4593), (379, 4721), (380, 4651), (381, 4597),
    (382, 4601), (383, 4766), (384, 4555), (385, 4659), (386, 4583), (387, 4800), (388, 2761), (389, 2489), (390, 1903), (391, 184),
    (712, 2544), (713, 2532), (714, 2768), (715, 3454), (716, 3346), (717, 3996), (718, 4521), (719, 4336), (720, 4486), (721, 4424),
    (722, 4417), (723, 4481), (724, 4310), (725, 4478), (726, 4357), (727, 4319), (728, 4550), (729, 3819), (730, 3360), (731, 3329),
    (732, 3397), (733, 3411), (734, 3386), (735, 3362), (736, 3517), (737, 3425), (738, 3034), (739, 2589), (740, 2462), (741, 2139)
  ]

theorem fc2kSubCert7_1_valid : checkPrefixSubCert fc2kSubCert7_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_1 : VerifiedSubCertProfile fc2kSubCert7_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_1 fc2kSubCert7_1_valid)

/-- Sub-certificate 2/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_2 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 97
  activeChunkMask := 0x1e00000000018000000000700
  numChunks := 11
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (27, { startWord := 512, endWord := 607, endBitCutoff := 6294, subMod := 1 }),
    (27, { startWord := 608, endWord := 703, endBitCutoff := 729, subMod := 1 }),
    (26, { startWord := 536, endWord := 630, endBitCutoff := 1222, subMod := 1 }),
    (26, { startWord := 3264, endWord := 3361, endBitCutoff := 890, subMod := 1 }),
    (20, { startWord := 512, endWord := 627, endBitCutoff := 742, subMod := 1 }),
    (18, { startWord := 512, endWord := 650, endBitCutoff := 5817, subMod := 1 }),
    (16, { startWord := 3264, endWord := 3382, endBitCutoff := 5647, subMod := 1 }),
    (14, { startWord := 512, endWord := 684, endBitCutoff := 3477, subMod := 1 }),
    (13, { startWord := 512, endWord := 686, endBitCutoff := 2244, subMod := 1 }),
    (11, { startWord := 5952, endWord := 6075, endBitCutoff := 5090, subMod := 1 }),
    (10, { startWord := 6096, endWord := 6201, endBitCutoff := 1871, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (64, 6740), (65, 7353), (66, 7638), (67, 8180), (68, 8176), (69, 8517), (70, 8664), (71, 8725), (72, 8605), (73, 8588),
    (74, 8689), (75, 8650), (76, 8692), (77, 8672), (78, 8037), (79, 7384), (80, 7504), (81, 7000), (82, 6473), (83, 6040),
    (84, 5542), (85, 4307), (86, 1293), (87, 1108), (408, 3766), (409, 4655), (410, 4466), (411, 4594), (412, 4464), (413, 4620),
    (414, 4600), (415, 4504), (416, 4627), (417, 4646), (418, 4576), (419, 4656), (420, 2738), (421, 2575), (422, 2335), (423, 206),
    (744, 2484), (745, 2480), (746, 2861), (747, 3346), (748, 3340), (749, 4011), (750, 4419), (751, 4436), (752, 4379), (753, 4543),
    (754, 4388), (755, 4359), (756, 4479), (757, 4503), (758, 4447), (759, 3419), (760, 2552), (761, 1887), (762, 3549), (763, 3526),
    (764, 3498), (765, 3532), (766, 3571), (767, 3593), (768, 3619), (769, 3474), (770, 3202), (771, 2539), (772, 2632), (773, 2556),
    (774, 2513), (775, 412)
  ]

theorem fc2kSubCert7_2_valid : checkPrefixSubCert fc2kSubCert7_2 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_2 : VerifiedSubCertProfile fc2kSubCert7_2 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_2 fc2kSubCert7_2_valid)

/-- Sub-certificate 3/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_3 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 36
  activeChunkMask := 0xf00007800
  numChunks := 13
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (25, { startWord := 712, endWord := 805, endBitCutoff := 7090, subMod := 1 }),
    (25, { startWord := 806, endWord := 899, endBitCutoff := 7746, subMod := 1 }),
    (21, { startWord := 2048, endWord := 2162, endBitCutoff := 155, subMod := 1 }),
    (20, { startWord := 704, endWord := 810, endBitCutoff := 3918, subMod := 1 }),
    (20, { startWord := 811, endWord := 910, endBitCutoff := 8173, subMod := 1 }),
    (19, { startWord := 2168, endWord := 2278, endBitCutoff := 5699, subMod := 1 }),
    (18, { startWord := 704, endWord := 831, endBitCutoff := 1038, subMod := 1 }),
    (15, { startWord := 832, endWord := 956, endBitCutoff := 4726, subMod := 1 }),
    (14, { startWord := 704, endWord := 881, endBitCutoff := 6341, subMod := 1 }),
    (13, { startWord := 704, endWord := 905, endBitCutoff := 3986, subMod := 1 }),
    (9, { startWord := 744, endWord := 956, endBitCutoff := 8093, subMod := 1 }),
    (7, { startWord := 704, endWord := 947, endBitCutoff := 1489, subMod := 1 }),
    (7, { startWord := 2048, endWord := 2170, endBitCutoff := 2454, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (88, 7393), (89, 8424), (90, 8544), (91, 8580), (92, 8333), (93, 9727), (94, 9945), (95, 9855), (96, 9849), (97, 9739),
    (98, 9837), (99, 9940), (100, 9912), (101, 9803), (102, 9860), (103, 9739), (104, 9984), (105, 9919), (106, 9868), (107, 9747),
    (108, 9741), (109, 9844), (110, 9018), (111, 8945), (112, 8640), (113, 7936), (114, 6889), (115, 6633), (116, 6716), (117, 6654),
    (118, 5997), (119, 3115), (256, 3453), (257, 3471), (258, 3425), (259, 3890), (260, 4352), (261, 4388), (262, 4366), (263, 4355),
    (264, 4488), (265, 4382), (266, 4684), (267, 5268), (268, 5378), (269, 5263), (270, 4615), (271, 3828), (272, 3565), (273, 3674),
    (274, 4453), (275, 4464), (276, 4433), (277, 4435), (278, 4502), (279, 4570), (280, 4463), (281, 3755), (282, 3796), (283, 2755),
    (284, 2411), (285, 1267), (286, 1279), (287, 628)
  ]

theorem fc2kSubCert7_3_valid : checkPrefixSubCert fc2kSubCert7_3 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_3 : VerifiedSubCertProfile fc2kSubCert7_3 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_3 fc2kSubCert7_3_valid)

/-- Sub-certificate 4/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_4 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 59
  activeChunkMask := 0x60000f000038000
  numChunks := 10
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (25, { startWord := 960, endWord := 1054, endBitCutoff := 5636, subMod := 1 }),
    (25, { startWord := 1055, endWord := 1148, endBitCutoff := 7343, subMod := 1 }),
    (25, { startWord := 2304, endWord := 2400, endBitCutoff := 1454, subMod := 1 }),
    (21, { startWord := 2304, endWord := 2432, endBitCutoff := 1821, subMod := 1 }),
    (20, { startWord := 960, endWord := 1066, endBitCutoff := 7866, subMod := 1 }),
    (18, { startWord := 960, endWord := 1085, endBitCutoff := 378, subMod := 1 }),
    (17, { startWord := 2432, endWord := 2551, endBitCutoff := 782, subMod := 1 }),
    (16, { startWord := 3648, endWord := 3753, endBitCutoff := 1409, subMod := 1 }),
    (15, { startWord := 960, endWord := 1111, endBitCutoff := 1707, subMod := 1 }),
    (14, { startWord := 960, endWord := 1136, endBitCutoff := 4103, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (120, 6712), (121, 7406), (122, 7602), (123, 7359), (124, 7374), (125, 7933), (126, 8106), (127, 8260), (128, 7953), (129, 7965),
    (130, 8087), (131, 7886), (132, 8172), (133, 7544), (134, 7349), (135, 7131), (136, 6563), (137, 6327), (138, 5890), (139, 3754),
    (140, 3713), (141, 3588), (142, 1560), (143, 836), (288, 2216), (289, 2197), (290, 2628), (291, 3545), (292, 3561), (293, 3514),
    (294, 3513), (295, 3498), (296, 3584), (297, 3521), (298, 3847), (299, 4378), (300, 3342), (301, 3313), (302, 3257), (303, 3324),
    (304, 3514), (305, 4074), (306, 4056), (307, 4181), (308, 4110), (309, 4065), (310, 4151), (311, 4174), (312, 4215), (313, 4182),
    (314, 3642), (315, 2650), (316, 2585), (317, 2575), (318, 2444), (319, 693), (456, 2141), (457, 2620), (458, 2929), (459, 3577),
    (460, 3592), (461, 3556), (462, 3725), (463, 3604), (464, 3560), (465, 3662), (466, 3532), (467, 3646), (468, 3504), (469, 1999),
    (470, 874)
  ]

theorem fc2kSubCert7_4_valid : checkPrefixSubCert fc2kSubCert7_4 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_4 : VerifiedSubCertProfile fc2kSubCert7_4 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_4 fc2kSubCert7_4_valid)

/-- Sub-certificate 5/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_5 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 63
  activeChunkMask := 0x60000700c6000000
  numChunks := 9
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (25, { startWord := 2560, endWord := 2656, endBitCutoff := 3113, subMod := 1 }),
    (24, { startWord := 1944, endWord := 2042, endBitCutoff := 3096, subMod := 1 }),
    (23, { startWord := 1600, endWord := 1705, endBitCutoff := 410, subMod := 1 }),
    (19, { startWord := 2560, endWord := 2673, endBitCutoff := 5714, subMod := 1 }),
    (17, { startWord := 1608, endWord := 1715, endBitCutoff := 3309, subMod := 1 }),
    (17, { startWord := 1920, endWord := 2036, endBitCutoff := 2044, subMod := 1 }),
    (16, { startWord := 1600, endWord := 1723, endBitCutoff := 7692, subMod := 1 }),
    (16, { startWord := 3904, endWord := 4011, endBitCutoff := 2111, subMod := 1 }),
    (2, { startWord := 3904, endWord := 4030, endBitCutoff := 7968, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (200, 3100), (201, 4787), (202, 5413), (203, 5342), (204, 5316), (205, 5372), (206, 5353), (207, 5326), (208, 5256), (209, 5312),
    (210, 5391), (211, 5562), (212, 5465), (213, 4660), (214, 4105), (215, 1775), (240, 1784), (241, 2682), (242, 2743), (243, 4468),
    (244, 4363), (245, 4357), (246, 4410), (247, 4502), (248, 4458), (249, 4517), (250, 4448), (251, 4503), (252, 4458), (253, 4609),
    (254, 4142), (255, 1584), (320, 2411), (321, 2407), (322, 2703), (323, 3466), (324, 3520), (325, 3509), (326, 3576), (327, 3644),
    (328, 4282), (329, 4566), (330, 4518), (331, 4467), (332, 3508), (333, 3418), (334, 2506), (335, 2467), (336, 2359), (337, 1292),
    (338, 1277), (339, 1291), (340, 841), (488, 4280), (489, 4562), (490, 4931), (491, 5399), (492, 5412), (493, 5206), (494, 5340),
    (495, 5250), (496, 5436), (497, 5386), (498, 5392), (499, 5410), (500, 5326), (501, 4651), (502, 3362), (503, 2192)
  ]

theorem fc2kSubCert7_5_valid : checkPrefixSubCert fc2kSubCert7_5 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_5 : VerifiedSubCertProfile fc2kSubCert7_5 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_5 fc2kSubCert7_5_valid)

/-- Sub-certificate 6/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_6 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 77
  activeChunkMask := 0x180300e6000000000000
  numChunks := 7
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (24, { startWord := 3416, endWord := 3512, endBitCutoff := 4624, subMod := 1 }),
    (24, { startWord := 4120, endWord := 4217, endBitCutoff := 4827, subMod := 1 }),
    (23, { startWord := 3136, endWord := 3236, endBitCutoff := 2, subMod := 1 }),
    (19, { startWord := 3392, endWord := 3507, endBitCutoff := 4825, subMod := 1 }),
    (17, { startWord := 3136, endWord := 3244, endBitCutoff := 8153, subMod := 1 }),
    (12, { startWord := 4800, endWord := 4919, endBitCutoff := 8005, subMod := 1 }),
    (11, { startWord := 4096, endWord := 4209, endBitCutoff := 7650, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (392, 2656), (393, 3499), (394, 3394), (395, 3420), (396, 3448), (397, 3537), (398, 3527), (399, 3553), (400, 3459), (401, 3574),
    (402, 3618), (403, 3560), (404, 2933), (405, 1994), (406, 349), (424, 1156), (425, 1108), (426, 1581), (427, 3474), (428, 3547),
    (429, 3625), (430, 3559), (431, 3572), (432, 3460), (433, 3304), (434, 3724), (435, 4326), (436, 4344), (437, 4428), (438, 3871),
    (439, 2468), (440, 2370), (441, 1383), (442, 1342), (443, 1266), (444, 1279), (445, 1321), (446, 1312), (447, 208), (512, 3209),
    (513, 3597), (514, 3556), (515, 4712), (516, 4612), (517, 4609), (518, 4639), (519, 4718), (520, 4634), (521, 4674), (522, 4673),
    (523, 4664), (524, 4034), (525, 3545), (526, 1892), (527, 260), (600, 3009), (601, 3217), (602, 3270), (603, 3194), (604, 3262),
    (605, 3268), (606, 3241), (607, 3211), (608, 3216), (609, 3252), (610, 3207), (611, 3168), (612, 2910), (613, 2577), (614, 2501),
    (615, 18)
  ]

theorem fc2kSubCert7_6_valid : checkPrefixSubCert fc2kSubCert7_6 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_6 : VerifiedSubCertProfile fc2kSubCert7_6 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_6 fc2kSubCert7_6_valid)

/-- Sub-certificate 7/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_7 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 81
  activeChunkMask := 0x1e03c0000000000000000
  numChunks := 6
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (24, { startWord := 4248, endWord := 4345, endBitCutoff := 2150, subMod := 1 }),
    (24, { startWord := 4346, endWord := 4442, endBitCutoff := 5364, subMod := 1 }),
    (21, { startWord := 4224, endWord := 4331, endBitCutoff := 4659, subMod := 1 }),
    (21, { startWord := 4928, endWord := 5036, endBitCutoff := 2582, subMod := 1 }),
    (12, { startWord := 4336, endWord := 4464, endBitCutoff := 2622, subMod := 1 }),
    (12, { startWord := 5040, endWord := 5163, endBitCutoff := 1744, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (528, 1167), (529, 1139), (530, 1150), (531, 2407), (532, 2472), (533, 2437), (534, 2404), (535, 2543), (536, 2348), (537, 2450),
    (538, 2785), (539, 3583), (540, 3543), (541, 2950), (542, 4069), (543, 4122), (544, 4139), (545, 4292), (546, 4212), (547, 4275),
    (548, 4141), (549, 4214), (550, 4056), (551, 4229), (552, 3359), (553, 3282), (554, 3269), (555, 2799), (556, 2559), (557, 2521),
    (558, 126), (616, 2025), (617, 2357), (618, 2453), (619, 2407), (620, 2398), (621, 2412), (622, 2421), (623, 2349), (624, 2414),
    (625, 2440), (626, 2873), (627, 3565), (628, 3392), (629, 3075), (630, 4127), (631, 4248), (632, 4252), (633, 4231), (634, 4086),
    (635, 4214), (636, 4151), (637, 4221), (638, 4386), (639, 4227), (640, 3206), (641, 2536), (642, 2527), (643, 2546), (644, 2557),
    (645, 946)
  ]

theorem fc2kSubCert7_7_valid : checkPrefixSubCert fc2kSubCert7_7 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_7 : VerifiedSubCertProfile fc2kSubCert7_7 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_7 fc2kSubCert7_7_valid)

/-- Sub-certificate 8/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_8 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 104
  activeChunkMask := 0xc6000600c00000000000000000
  numChunks := 6
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (24, { startWord := 4504, endWord := 4602, endBitCutoff := 1112, subMod := 1 }),
    (23, { startWord := 6208, endWord := 6306, endBitCutoff := 826, subMod := 1 }),
    (12, { startWord := 4480, endWord := 4598, endBitCutoff := 8027, subMod := 1 }),
    (12, { startWord := 5184, endWord := 5302, endBitCutoff := 3492, subMod := 1 }),
    (10, { startWord := 6208, endWord := 6317, endBitCutoff := 2084, subMod := 1 }),
    (10, { startWord := 6528, endWord := 6636, endBitCutoff := 3378, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (560, 2611), (561, 2604), (562, 2464), (563, 3191), (564, 3357), (565, 3180), (566, 3281), (567, 3148), (568, 3353), (569, 3216),
    (570, 3153), (571, 3151), (572, 3238), (573, 3169), (574, 3067), (575, 338), (648, 2983), (649, 3257), (650, 3269), (651, 3223),
    (652, 3234), (653, 3277), (654, 3277), (655, 3285), (656, 3197), (657, 3339), (658, 3262), (659, 3208), (660, 3040), (661, 2487),
    (662, 2183), (776, 3535), (777, 3482), (778, 3552), (779, 3548), (780, 3499), (781, 3500), (782, 3393), (783, 3502), (784, 3506),
    (785, 3488), (786, 3618), (787, 3527), (788, 2752), (789, 1619), (816, 2530), (817, 2453), (818, 2795), (819, 3439), (820, 3552),
    (821, 3453), (822, 3537), (823, 3598), (824, 3470), (825, 3516), (826, 3584), (827, 3522), (828, 3429), (829, 2491), (830, 1152)
  ]

theorem fc2kSubCert7_8_valid : checkPrefixSubCert fc2kSubCert7_8 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_8 : VerifiedSubCertProfile fc2kSubCert7_8 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_8 fc2kSubCert7_8_valid)

/-- Sub-certificate 9/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_9 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 116
  activeChunkMask := 0xc6318000000000000000000000000
  numChunks := 7
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (23, { startWord := 6336, endWord := 6434, endBitCutoff := 1135, subMod := 1 }),
    (23, { startWord := 6656, endWord := 6754, endBitCutoff := 4020, subMod := 1 }),
    (23, { startWord := 6976, endWord := 7075, endBitCutoff := 1855, subMod := 1 }),
    (10, { startWord := 6336, endWord := 6444, endBitCutoff := 1215, subMod := 1 }),
    (10, { startWord := 6656, endWord := 6774, endBitCutoff := 2615, subMod := 1 }),
    (10, { startWord := 6976, endWord := 7094, endBitCutoff := 6170, subMod := 1 }),
    (9, { startWord := 7296, endWord := 7405, endBitCutoff := 2125, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (792, 3521), (793, 3550), (794, 3526), (795, 3515), (796, 3429), (797, 3691), (798, 3563), (799, 3599), (800, 3534), (801, 3411),
    (802, 3530), (803, 3605), (804, 2743), (805, 1304), (832, 3523), (833, 3392), (834, 3846), (835, 4552), (836, 4581), (837, 4552),
    (838, 4529), (839, 4547), (840, 4561), (841, 4472), (842, 4609), (843, 4530), (844, 3788), (845, 3537), (846, 3009), (872, 3408),
    (873, 3592), (874, 3852), (875, 4528), (876, 4532), (877, 4504), (878, 4424), (879, 4439), (880, 4595), (881, 4488), (882, 4582),
    (883, 4549), (884, 3989), (885, 3458), (886, 3088), (912, 2425), (913, 2443), (914, 2812), (915, 3475), (916, 3446), (917, 3501),
    (918, 3374), (919, 3451), (920, 3496), (921, 3429), (922, 3474), (923, 3578), (924, 3543), (925, 2708), (926, 1267), (927, 99)
  ]

theorem fc2kSubCert7_9_valid : checkPrefixSubCert fc2kSubCert7_9 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_9 : VerifiedSubCertProfile fc2kSubCert7_9 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_9 fc2kSubCert7_9_valid)

/-- Sub-certificate 10/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_10 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 29
  activeChunkMask := 0x19fc0000
  numChunks := 20
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (22, { startWord := 1176, endWord := 1269, endBitCutoff := 3832, subMod := 1 }),
    (22, { startWord := 1270, endWord := 1364, endBitCutoff := 5229, subMod := 1 }),
    (21, { startWord := 1248, endWord := 1345, endBitCutoff := 2744, subMod := 1 }),
    (21, { startWord := 1346, endWord := 1451, endBitCutoff := 3452, subMod := 1 }),
    (19, { startWord := 1152, endWord := 1257, endBitCutoff := 7349, subMod := 1 }),
    (19, { startWord := 1258, endWord := 1383, endBitCutoff := 2267, subMod := 1 }),
    (19, { startWord := 1384, endWord := 1509, endBitCutoff := 2011, subMod := 1 }),
    (18, { startWord := 1152, endWord := 1290, endBitCutoff := 2140, subMod := 1 }),
    (16, { startWord := 1488, endWord := 1596, endBitCutoff := 1901, subMod := 1 }),
    (16, { startWord := 1728, endWord := 1823, endBitCutoff := 2859, subMod := 1 }),
    (15, { startWord := 1152, endWord := 1324, endBitCutoff := 5240, subMod := 1 }),
    (15, { startWord := 1325, endWord := 1511, endBitCutoff := 1738, subMod := 1 }),
    (15, { startWord := 1728, endWord := 1840, endBitCutoff := 7324, subMod := 1 }),
    (14, { startWord := 1152, endWord := 1367, endBitCutoff := 4446, subMod := 1 }),
    (13, { startWord := 1152, endWord := 1396, endBitCutoff := 5394, subMod := 1 }),
    (13, { startWord := 1397, endWord := 1575, endBitCutoff := 3231, subMod := 1 }),
    (9, { startWord := 1152, endWord := 1472, endBitCutoff := 7971, subMod := 1 }),
    (7, { startWord := 1152, endWord := 1528, endBitCutoff := 7247, subMod := 1 }),
    (6, { startWord := 1376, endWord := 1597, endBitCutoff := 3459, subMod := 1 }),
    (2, { startWord := 1304, endWord := 1598, endBitCutoff := 8147, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (144, 9132), (145, 9749), (146, 9835), (147, 10638), (148, 10375), (149, 10391), (150, 10338), (151, 10346), (152, 10212), (153, 10360),
    (154, 10231), (155, 10386), (156, 10694), (157, 10680), (158, 10804), (159, 10699), (160, 10833), (161, 10386), (162, 10132), (163, 10495),
    (164, 10522), (165, 10418), (166, 10593), (167, 11014), (168, 11168), (169, 11466), (170, 11235), (171, 10234), (172, 10984), (173, 10774),
    (174, 10932), (175, 10843), (176, 10863), (177, 10923), (178, 10875), (179, 10838), (180, 10791), (181, 10713), (182, 10577), (183, 10621),
    (184, 9979), (185, 10084), (186, 10524), (187, 10757), (188, 10687), (189, 9720), (190, 9638), (191, 8838), (192, 7555), (193, 7540),
    (194, 7627), (195, 7788), (196, 7473), (197, 6123), (198, 6214), (199, 4605), (216, 4328), (217, 4691), (218, 4666), (219, 4700),
    (220, 4877), (221, 4717), (222, 4529), (223, 4668), (224, 4728), (225, 4763), (226, 4760), (227, 4617), (228, 2820), (229, 2658),
    (230, 506)
  ]

theorem fc2kSubCert7_10_valid : checkPrefixSubCert fc2kSubCert7_10 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_10 : VerifiedSubCertProfile fc2kSubCert7_10 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_10 fc2kSubCert7_10_valid)

/-- Sub-certificate 11/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_11 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 127
  activeChunkMask := 0x6db00000000000000000000000000000
  numChunks := 7
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (22, { startWord := 7448, endWord := 7547, endBitCutoff := 3058, subMod := 1 }),
    (22, { startWord := 7640, endWord := 7739, endBitCutoff := 3345, subMod := 1 }),
    (22, { startWord := 7832, endWord := 7931, endBitCutoff := 1545, subMod := 1 }),
    (8, { startWord := 7424, endWord := 7532, endBitCutoff := 1307, subMod := 1 }),
    (8, { startWord := 7616, endWord := 7735, endBitCutoff := 3173, subMod := 1 }),
    (8, { startWord := 7808, endWord := 7927, endBitCutoff := 6344, subMod := 1 }),
    (7, { startWord := 8000, endWord := 8112, endBitCutoff := 1804, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (928, 2558), (929, 2558), (930, 2457), (931, 3458), (932, 3558), (933, 3521), (934, 3437), (935, 3533), (936, 3494), (937, 3357),
    (938, 3455), (939, 3465), (940, 3567), (941, 2419), (942, 1186), (943, 498), (952, 3201), (953, 3628), (954, 3431), (955, 4460),
    (956, 4462), (957, 4451), (958, 4370), (959, 4507), (960, 4493), (961, 4469), (962, 4512), (963, 4509), (964, 4119), (965, 3639),
    (966, 3263), (967, 514), (976, 3035), (977, 3543), (978, 3521), (979, 4471), (980, 4460), (981, 4476), (982, 4422), (983, 4412),
    (984, 4503), (985, 4489), (986, 4564), (987, 4540), (988, 4184), (989, 3540), (990, 3362), (991, 506), (1000, 3105), (1001, 3439),
    (1002, 3420), (1003, 3393), (1004, 3356), (1005, 3330), (1006, 3421), (1007, 3381), (1008, 3505), (1009, 3497), (1010, 3445), (1011, 3472),
    (1012, 3175), (1013, 2512), (1014, 70)
  ]

theorem fc2kSubCert7_11_valid : checkPrefixSubCert fc2kSubCert7_11 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_11 : VerifiedSubCertProfile fc2kSubCert7_11 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_11 fc2kSubCert7_11_valid)

/-- Sub-certificate 12/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_12 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 132
  activeChunkMask := 0xd80000000000000001800600000000000
  numChunks := 7
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (22, { startWord := 8152, endWord := 8250, endBitCutoff := 5587, subMod := 1 }),
    (15, { startWord := 2880, endWord := 2975, endBitCutoff := 1815, subMod := 1 }),
    (12, { startWord := 2888, endWord := 3001, endBitCutoff := 6869, subMod := 1 }),
    (9, { startWord := 3776, endWord := 3872, endBitCutoff := 6631, subMod := 1 }),
    (8, { startWord := 3784, endWord := 3896, endBitCutoff := 7071, subMod := 1 }),
    (7, { startWord := 8128, endWord := 8237, endBitCutoff := 694, subMod := 1 }),
    (6, { startWord := 8320, endWord := 8436, endBitCutoff := 3935, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (360, 2455), (361, 4649), (362, 4766), (363, 4632), (364, 4659), (365, 4703), (366, 4604), (367, 4733), (368, 4606), (369, 4745),
    (370, 4560), (371, 4530), (372, 2581), (373, 2567), (374, 2622), (375, 616), (472, 2623), (473, 4585), (474, 4619), (475, 4646),
    (476, 4790), (477, 4654), (478, 4567), (479, 4704), (480, 4675), (481, 4579), (482, 4670), (483, 4637), (484, 2829), (485, 2569),
    (486, 2595), (487, 286), (1016, 2540), (1017, 2535), (1018, 2564), (1019, 3383), (1020, 3450), (1021, 3424), (1022, 3467), (1023, 3472),
    (1024, 3491), (1025, 3463), (1026, 3472), (1027, 3511), (1028, 3454), (1029, 2618), (1030, 1268), (1031, 409), (1040, 3093), (1041, 3332),
    (1042, 3263), (1043, 3262), (1044, 3319), (1045, 3293), (1046, 3288), (1047, 3350), (1048, 3352), (1049, 3394), (1050, 3193), (1051, 3341),
    (1052, 3167), (1053, 2498), (1054, 1376)
  ]

theorem fc2kSubCert7_12_valid : checkPrefixSubCert fc2kSubCert7_12 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_12 : VerifiedSubCertProfile fc2kSubCert7_12 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_12 fc2kSubCert7_12_valid)

/-- Sub-certificate 13/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_13 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 113
  activeChunkMask := 0x18c00001803000000000000000000
  numChunks := 8
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (9, { startWord := 4608, endWord := 4705, endBitCutoff := 1820, subMod := 1 }),
    (9, { startWord := 5312, endWord := 5408, endBitCutoff := 5619, subMod := 1 }),
    (8, { startWord := 4608, endWord := 4724, endBitCutoff := 5282, subMod := 1 }),
    (8, { startWord := 5312, endWord := 5428, endBitCutoff := 3840, subMod := 1 }),
    (7, { startWord := 6784, endWord := 6883, endBitCutoff := 2833, subMod := 1 }),
    (6, { startWord := 6784, endWord := 6902, endBitCutoff := 1026, subMod := 1 }),
    (6, { startWord := 7104, endWord := 7203, endBitCutoff := 1606, subMod := 1 }),
    (5, { startWord := 7112, endWord := 7228, endBitCutoff := 7444, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (576, 4646), (577, 4605), (578, 4654), (579, 4492), (580, 4469), (581, 4537), (582, 4678), (583, 4520), (584, 4597), (585, 4528),
    (586, 4497), (587, 4755), (588, 2853), (589, 2709), (590, 1488), (664, 4678), (665, 4526), (666, 4515), (667, 4560), (668, 4647),
    (669, 4596), (670, 4654), (671, 4627), (672, 4634), (673, 4617), (674, 4575), (675, 4730), (676, 2772), (677, 2501), (678, 1396),
    (848, 4486), (849, 4484), (850, 4529), (851, 4566), (852, 4385), (853, 4525), (854, 4525), (855, 4522), (856, 4523), (857, 4492),
    (858, 4515), (859, 4699), (860, 3321), (861, 2515), (862, 1941), (888, 2652), (889, 4472), (890, 4450), (891, 4405), (892, 4557),
    (893, 4497), (894, 4497), (895, 4552), (896, 4581), (897, 4588), (898, 4520), (899, 4441), (900, 3249), (901, 2494), (902, 2466),
    (903, 1607)
  ]

theorem fc2kSubCert7_13_valid : checkPrefixSubCert fc2kSubCert7_13 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_13 : VerifiedSubCertProfile fc2kSubCert7_13 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_13 fc2kSubCert7_13_valid)

/-- Sub-certificate 14/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_14 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 141
  activeChunkMask := 0x1ff000000000000000000000000000000000
  numChunks := 10
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (6, { startWord := 8448, endWord := 8548, endBitCutoff := 4649, subMod := 1 }),
    (6, { startWord := 8549, endWord := 8648, endBitCutoff := 2749, subMod := 1 }),
    (5, { startWord := 8448, endWord := 8573, endBitCutoff := 7205, subMod := 1 }),
    (5, { startWord := 8574, endWord := 8689, endBitCutoff := 4131, subMod := 1 }),
    (5, { startWord := 8690, endWord := 8790, endBitCutoff := 5334, subMod := 1 }),
    (5, { startWord := 8791, endWord := 8890, endBitCutoff := 3454, subMod := 1 }),
    (5, { startWord := 8891, endWord := 8991, endBitCutoff := 732, subMod := 1 }),
    (4, { startWord := 8904, endWord := 9019, endBitCutoff := 6443, subMod := 1 }),
    (3, { startWord := 8648, endWord := 8773, endBitCutoff := 4242, subMod := 1 }),
    (3, { startWord := 8774, endWord := 8899, endBitCutoff := 2541, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1056, 4498), (1057, 4410), (1058, 4501), (1059, 4431), (1060, 4496), (1061, 4422), (1062, 4381), (1063, 4467), (1064, 4445), (1065, 4341),
    (1066, 4376), (1067, 4505), (1068, 4269), (1069, 4518), (1070, 4538), (1071, 4382), (1072, 4319), (1073, 4548), (1074, 4538), (1075, 4605),
    (1076, 4382), (1077, 4554), (1078, 4548), (1079, 4486), (1080, 4329), (1081, 4449), (1082, 4322), (1083, 4400), (1084, 4426), (1085, 4458),
    (1086, 4407), (1087, 4657), (1088, 4383), (1089, 4390), (1090, 4411), (1091, 4458), (1092, 4279), (1093, 4524), (1094, 4481), (1095, 4336),
    (1096, 4265), (1097, 4446), (1098, 4275), (1099, 4474), (1100, 4438), (1101, 4533), (1102, 4449), (1103, 4507), (1104, 4449), (1105, 4550),
    (1106, 4429), (1107, 4573), (1108, 4634), (1109, 4444), (1110, 4397), (1111, 4290), (1112, 3311), (1113, 4422), (1114, 4498), (1115, 4528),
    (1116, 4520), (1117, 4434), (1118, 4508), (1119, 4476), (1120, 4532), (1121, 4497), (1122, 4553), (1123, 4210), (1124, 2552), (1125, 2540),
    (1126, 2548), (1127, 1188)
  ]

theorem fc2kSubCert7_14_valid : checkPrefixSubCert fc2kSubCert7_14 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_14 : VerifiedSubCertProfile fc2kSubCert7_14 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_14 fc2kSubCert7_14_valid)

/-- Sub-certificate 15/17 for FC2K certificate 7 (`8` active super-chunks). -/
def fc2kSubCert7_15 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 149
  activeChunkMask := 0x1fe00000000000000000000000000000000000
  numChunks := 9
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (4, { startWord := 9024, endWord := 9123, endBitCutoff := 3714, subMod := 1 }),
    (4, { startWord := 9124, endWord := 9224, endBitCutoff := 4065, subMod := 1 }),
    (4, { startWord := 9225, endWord := 9324, endBitCutoff := 7835, subMod := 1 }),
    (4, { startWord := 9325, endWord := 9425, endBitCutoff := 1296, subMod := 1 }),
    (4, { startWord := 9426, endWord := 9527, endBitCutoff := 4594, subMod := 1 }),
    (3, { startWord := 9024, endWord := 9147, endBitCutoff := 1119, subMod := 1 }),
    (3, { startWord := 9148, endWord := 9276, endBitCutoff := 837, subMod := 1 }),
    (3, { startWord := 9277, endWord := 9401, endBitCutoff := 3547, subMod := 1 }),
    (3, { startWord := 9402, endWord := 9527, endBitCutoff := 350, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1128, 4556), (1129, 4488), (1130, 4534), (1131, 4530), (1132, 4444), (1133, 4466), (1134, 4540), (1135, 4471), (1136, 4601), (1137, 4494),
    (1138, 4586), (1139, 4538), (1140, 4328), (1141, 4418), (1142, 4412), (1143, 4276), (1144, 4392), (1145, 4374), (1146, 4452), (1147, 4458),
    (1148, 4306), (1149, 4305), (1150, 4461), (1151, 4563), (1152, 4479), (1153, 4378), (1154, 4259), (1155, 4507), (1156, 4338), (1157, 4322),
    (1158, 4370), (1159, 4190), (1160, 4388), (1161, 4548), (1162, 4496), (1163, 4410), (1164, 4598), (1165, 4490), (1166, 4576), (1167, 4521),
    (1168, 4425), (1169, 4426), (1170, 4463), (1171, 4331), (1172, 4506), (1173, 4542), (1174, 4523), (1175, 4223), (1176, 4566), (1177, 4512),
    (1178, 4247), (1179, 4305), (1180, 4240), (1181, 4436), (1182, 4414), (1183, 4552), (1184, 4384), (1185, 4437), (1186, 4393), (1187, 4416),
    (1188, 4503), (1189, 4397), (1190, 4022)
  ]

theorem fc2kSubCert7_15_valid : checkPrefixSubCert fc2kSubCert7_15 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_15 : VerifiedSubCertProfile fc2kSubCert7_15 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_15 fc2kSubCert7_15_valid)

/-- Sub-certificate 16/17 for FC2K certificate 7 (`9` active super-chunks). -/
def fc2kSubCert7_16 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 158
  activeChunkMask := 0x3fe0000000000000000000000000000000000000
  numChunks := 9
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (2, { startWord := 9536, endWord := 9635, endBitCutoff := 7997, subMod := 1 }),
    (2, { startWord := 9636, endWord := 9736, endBitCutoff := 7571, subMod := 1 }),
    (2, { startWord := 9737, endWord := 9838, endBitCutoff := 3344, subMod := 1 }),
    (2, { startWord := 9839, endWord := 9938, endBitCutoff := 7231, subMod := 1 }),
    (1, { startWord := 9864, endWord := 9979, endBitCutoff := 1391, subMod := 1 }),
    (1, { startWord := 9980, endWord := 10079, endBitCutoff := 5457, subMod := 1 }),
    (0, { startWord := 9536, endWord := 9662, endBitCutoff := 4789, subMod := 1 }),
    (0, { startWord := 9663, endWord := 9789, endBitCutoff := 4975, subMod := 1 }),
    (0, { startWord := 9944, endWord := 10068, endBitCutoff := 5782, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1192, 4426), (1193, 4500), (1194, 4418), (1195, 4454), (1196, 4284), (1197, 4454), (1198, 4460), (1199, 4432), (1200, 4462), (1201, 4446),
    (1202, 4446), (1203, 4460), (1204, 4352), (1205, 4470), (1206, 4482), (1207, 4400), (1208, 4410), (1209, 4306), (1210, 4392), (1211, 4542),
    (1212, 4290), (1213, 4330), (1214, 4620), (1215, 4362), (1216, 4426), (1217, 4430), (1218, 4472), (1219, 4410), (1220, 4342), (1221, 4450),
    (1222, 4426), (1223, 3772), (1224, 2536), (1225, 2468), (1226, 2420), (1227, 2408), (1228, 2408), (1229, 2258), (1230, 2466), (1231, 2414),
    (1232, 2504), (1233, 4516), (1234, 4344), (1235, 4586), (1236, 4478), (1237, 4410), (1238, 4516), (1239, 4460), (1240, 4482), (1241, 4366),
    (1242, 3256), (1243, 4534), (1244, 4458), (1245, 4502), (1246, 4530), (1247, 4224), (1248, 4422), (1249, 4386), (1250, 4298), (1251, 4472),
    (1252, 4560), (1253, 4478), (1254, 4592), (1255, 4418), (1256, 4500), (1257, 4516), (1258, 3598), (1259, 2416)
  ]

theorem fc2kSubCert7_16_valid : checkPrefixSubCert fc2kSubCert7_16 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_16 : VerifiedSubCertProfile fc2kSubCert7_16 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_16 fc2kSubCert7_16_valid)

/-- Sub-certificate 17/17 for FC2K certificate 7 (`7` active super-chunks). -/
def fc2kSubCert7_17 : PrefixSubCert where
  corrLo := 347562017
  numSuperChunks := 165
  activeChunkMask := 0x1fc000000000000000000000000000000000000000
  numChunks := 7
  qSub := 15507
  maxHi := 864641065
  chunks := [
    (1, { startWord := 10112, endWord := 10213, endBitCutoff := 2173, subMod := 1 }),
    (1, { startWord := 10214, endWord := 10315, endBitCutoff := 601, subMod := 1 }),
    (1, { startWord := 10316, endWord := 10418, endBitCutoff := 448, subMod := 1 }),
    (1, { startWord := 10419, endWord := 10519, endBitCutoff := 7668, subMod := 1 }),
    (0, { startWord := 10112, endWord := 10237, endBitCutoff := 2866, subMod := 1 }),
    (0, { startWord := 10238, endWord := 10363, endBitCutoff := 2902, subMod := 1 }),
    (0, { startWord := 10364, endWord := 10489, endBitCutoff := 5885, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1264, 4318), (1265, 4326), (1266, 4468), (1267, 4444), (1268, 4334), (1269, 4376), (1270, 4448), (1271, 4356), (1272, 4378), (1273, 4414),
    (1274, 4556), (1275, 4532), (1276, 4294), (1277, 4504), (1278, 4322), (1279, 4396), (1280, 4336), (1281, 4496), (1282, 4302), (1283, 4522),
    (1284, 4268), (1285, 4513), (1286, 4541), (1287, 4508), (1288, 4422), (1289, 4214), (1290, 4398), (1291, 4402), (1292, 4408), (1293, 4456),
    (1294, 4486), (1295, 4184), (1296, 4348), (1297, 4396), (1298, 4364), (1299, 4308), (1300, 4428), (1301, 4386), (1302, 4074), (1303, 4526),
    (1304, 4440), (1305, 4556), (1306, 4438), (1307, 4412), (1308, 4472), (1309, 4488), (1310, 4380), (1311, 2762), (1312, 2442), (1313, 2488),
    (1314, 2468)
  ]

theorem fc2kSubCert7_17_valid : checkPrefixSubCert fc2kSubCert7_17 = true := by
  decide +kernel

private noncomputable def fc2kSubProf7_17 : VerifiedSubCertProfile fc2kSubCert7_17 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert7_17 fc2kSubCert7_17_valid)

def fc2kSubCerts7 : List PrefixSubCert := [fc2kSubCert7_0, fc2kSubCert7_1, fc2kSubCert7_2, fc2kSubCert7_3, fc2kSubCert7_4, fc2kSubCert7_5, fc2kSubCert7_6, fc2kSubCert7_7, fc2kSubCert7_8, fc2kSubCert7_9, fc2kSubCert7_10, fc2kSubCert7_11, fc2kSubCert7_12, fc2kSubCert7_13, fc2kSubCert7_14, fc2kSubCert7_15, fc2kSubCert7_16, fc2kSubCert7_17]

def fc2kPlan7 : MultiSubCertPlan where
  P := 28
  M := 6
  qSub := 15507
  qCert := 93042
  corrLo := 347562017
  maxHi := 864641065
  numOcts := 1842
  routes := [
    [(16, 6), (16, 7), (16, 8), (17, 4), (17, 5), (17, 6)],
    [(16, 4), (16, 5), (17, 0), (17, 1), (17, 2), (17, 3)],
    [(10, 19), (5, 8), (16, 0), (16, 1), (16, 2), (16, 3)],
    [(14, 8), (14, 9), (15, 5), (15, 6), (15, 7), (15, 8)],
    [(14, 7), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4)],
    [(13, 7), (14, 2), (14, 3), (14, 4), (14, 5), (14, 6)],
    [(10, 18), (13, 5), (13, 6), (12, 6), (14, 0), (14, 1)],
    [(3, 11), (10, 17), (3, 12), (13, 4), (11, 6), (12, 5)],
    [(12, 4), (13, 2), (13, 3), (11, 3), (11, 4), (11, 5)],
    [(3, 10), (10, 16), (12, 3), (13, 0), (13, 1), (9, 6)],
    [(2, 10), (8, 4), (9, 3), (8, 5), (9, 4), (9, 5)],
    [(6, 6), (0, 9), (0, 10), (1, 9), (1, 10), (2, 9)],
    [(12, 2), (7, 4), (8, 2), (6, 5), (7, 5), (8, 3)],
    [(0, 8), (1, 8), (2, 8), (3, 9), (10, 14), (10, 15)],
    [(0, 7), (1, 7), (2, 7), (3, 8), (4, 9), (10, 13)],
    [(3, 7), (4, 8), (10, 10), (10, 11), (10, 12), (12, 1)],
    [(10, 8), (5, 6), (10, 9), (2, 6), (4, 7), (5, 7)],
    [(5, 4), (5, 5), (4, 6), (0, 6), (1, 6), (6, 4)],
    [(0, 5), (1, 5), (2, 5), (3, 6), (4, 5), (10, 7)],
    [(10, 4), (10, 5), (10, 6), (3, 5), (5, 3), (6, 3)],
    [(0, 4), (1, 4), (2, 4), (3, 3), (3, 4), (4, 4)],
    [(10, 2), (10, 3), (3, 2), (4, 3), (7, 2), (7, 3)],
    [(10, 0), (10, 1), (11, 0), (11, 1), (11, 2), (12, 0)],
    [(5, 2), (6, 2), (8, 1), (9, 0), (9, 1), (9, 2)],
    [(5, 1), (6, 0), (6, 1), (7, 0), (7, 1), (8, 0)],
    [(3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0)],
    [(0, 2), (1, 2), (2, 2), (0, 3), (1, 3), (2, 3)],
    [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]
  ]
  windowCaps := []
  octWindowCaps := [
    { minWordIdx := 225, spanWords := 81, cap := 354482 },
    { minWordIdx := 225, spanWords := 101, cap := 439397 },
    { minWordIdx := 653, spanWords := 42, cap := 186991 },
    { minWordIdx := 696, spanWords := 143, cap := 620320 },
    { minWordIdx := 951, spanWords := 81, cap := 354482 },
    { minWordIdx := 1020, spanWords := 84, cap := 367722 },
    { minWordIdx := 1020, spanWords := 336, cap := 1167510 },
    { minWordIdx := 1360, spanWords := 156, cap := 0 },
    { minWordIdx := 1360, spanWords := 205, cap := 0 },
    { minWordIdx := 1593, spanWords := 42, cap := 0 },
    { minWordIdx := 1827, spanWords := 119, cap := 0 },
    { minWordIdx := 1827, spanWords := 477, cap := 0 },
    { minWordIdx := 1977, spanWords := 42, cap := 0 },
    { minWordIdx := 2280, spanWords := 81, cap := 0 },
    { minWordIdx := 2346, spanWords := 101, cap := 0 },
    { minWordIdx := 2366, spanWords := 81, cap := 0 },
    { minWordIdx := 2917, spanWords := 42, cap := 0 },
    { minWordIdx := 2922, spanWords := 42, cap := 0 },
    { minWordIdx := 2967, spanWords := 171, cap := 0 },
    { minWordIdx := 2967, spanWords := 688, cap := 0 },
    { minWordIdx := 3520, spanWords := 81, cap := 0 },
    { minWordIdx := 3714, spanWords := 143, cap := 0 },
    { minWordIdx := 4246, spanWords := 42, cap := 0 },
    { minWordIdx := 4849, spanWords := 81, cap := 0 },
    { minWordIdx := 5645, spanWords := 205, cap := 0 },
    { minWordIdx := 5695, spanWords := 156, cap := 0 }
  ]

theorem fc2kPlan7_valid : checkMultiSubCertPlan fc2kSubCerts7 fc2kPlan7 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs7 :
    ∀ g : Fin fc2kSubCerts7.length,
      VerifiedSubCertProfile (fc2kSubCerts7[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf7_0
  | ⟨1, _⟩ => fc2kSubProf7_1
  | ⟨2, _⟩ => fc2kSubProf7_2
  | ⟨3, _⟩ => fc2kSubProf7_3
  | ⟨4, _⟩ => fc2kSubProf7_4
  | ⟨5, _⟩ => fc2kSubProf7_5
  | ⟨6, _⟩ => fc2kSubProf7_6
  | ⟨7, _⟩ => fc2kSubProf7_7
  | ⟨8, _⟩ => fc2kSubProf7_8
  | ⟨9, _⟩ => fc2kSubProf7_9
  | ⟨10, _⟩ => fc2kSubProf7_10
  | ⟨11, _⟩ => fc2kSubProf7_11
  | ⟨12, _⟩ => fc2kSubProf7_12
  | ⟨13, _⟩ => fc2kSubProf7_13
  | ⟨14, _⟩ => fc2kSubProf7_14
  | ⟨15, _⟩ => fc2kSubProf7_15
  | ⟨16, _⟩ => fc2kSubProf7_16
  | ⟨17, _⟩ => fc2kSubProf7_17
  | ⟨k + 18, h⟩ => False.elim (by change k + 18 < 18 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 7. -/
noncomputable def fc2kPrefixProfile7 :
    GeneralPrefixProfile 28 93042 347562017 864641065 :=
  assembleGeneralPrefixProfile fc2kSubCerts7 fc2kPlan7 fc2kPlan7_valid fc2kSubProfs7

end Sude
