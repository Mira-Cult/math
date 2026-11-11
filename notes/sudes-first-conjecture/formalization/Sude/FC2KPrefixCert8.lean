import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 8

Certifies `P = 28` power-of-two prime-pair stages (`qCert = 116946`, `6` chunk(s) of `19491`)
in `[440228507, 943544989]` via `16` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 64307`).
-/

namespace Sude

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_0 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 90
  activeChunkMask := 0x3e00000000000000000000f
  numChunks := 13
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (27, { startWord := 0, endWord := 120, endBitCutoff := 3743, subMod := 1 }),
    (27, { startWord := 121, endWord := 242, endBitCutoff := 6574, subMod := 1 }),
    (22, { startWord := 5440, endWord := 5579, endBitCutoff := 2674, subMod := 1 }),
    (21, { startWord := 8, endWord := 145, endBitCutoff := 6966, subMod := 1 }),
    (20, { startWord := 64, endWord := 211, endBitCutoff := 6699, subMod := 1 }),
    (18, { startWord := 0, endWord := 170, endBitCutoff := 1982, subMod := 1 }),
    (14, { startWord := 40, endWord := 251, endBitCutoff := 4795, subMod := 1 }),
    (13, { startWord := 5440, endWord := 5594, endBitCutoff := 6312, subMod := 1 }),
    (13, { startWord := 5595, endWord := 5743, endBitCutoff := 6294, subMod := 1 }),
    (11, { startWord := 0, endWord := 243, endBitCutoff := 7702, subMod := 1 }),
    (7, { startWord := 5440, endWord := 5660, endBitCutoff := 2299, subMod := 1 }),
    (6, { startWord := 5440, endWord := 5674, endBitCutoff := 7360, subMod := 1 }),
    (1, { startWord := 5440, endWord := 5751, endBitCutoff := 983, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 4200), (1, 5810), (2, 6200), (3, 6072), (4, 5980), (5, 7304), (6, 7416), (7, 7354), (8, 7984), (9, 8010),
    (10, 8002), (11, 8197), (12, 8509), (13, 8927), (14, 9131), (15, 9185), (16, 9240), (17, 9123), (18, 8743), (19, 8450),
    (20, 8523), (21, 8201), (22, 7800), (23, 7481), (24, 7368), (25, 7441), (26, 7136), (27, 6728), (28, 6651), (29, 5952),
    (30, 4663), (31, 2111), (680, 7451), (681, 7499), (682, 7562), (683, 7764), (684, 7761), (685, 7755), (686, 7823), (687, 7764),
    (688, 7869), (689, 7695), (690, 7773), (691, 7976), (692, 7661), (693, 7747), (694, 7735), (695, 7714), (696, 7913), (697, 7390),
    (698, 7425), (699, 7418), (700, 7565), (701, 7765), (702, 7908), (703, 7958), (704, 7859), (705, 7929), (706, 7974), (707, 7367),
    (708, 6855), (709, 6200), (710, 5624), (711, 5538), (712, 5726), (713, 4869), (714, 4771), (715, 4818), (716, 4815), (717, 4763),
    (718, 2875)
  ]

theorem fc2kSubCert8_0_valid : checkPrefixSubCert fc2kSubCert8_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_0 : VerifiedSubCertProfile fc2kSubCert8_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_0 fc2kSubCert8_0_valid)

/-- Sub-certificate 1/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_1 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 95
  activeChunkMask := 0x7c00000000000000000001e0
  numChunks := 12
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (27, { startWord := 320, endWord := 442, endBitCutoff := 6046, subMod := 1 }),
    (27, { startWord := 443, endWord := 565, endBitCutoff := 3195, subMod := 1 }),
    (22, { startWord := 5760, endWord := 5899, endBitCutoff := 4087, subMod := 1 }),
    (21, { startWord := 320, endWord := 456, endBitCutoff := 1482, subMod := 1 }),
    (20, { startWord := 320, endWord := 469, endBitCutoff := 6942, subMod := 1 }),
    (18, { startWord := 320, endWord := 503, endBitCutoff := 4442, subMod := 1 }),
    (14, { startWord := 320, endWord := 544, endBitCutoff := 5942, subMod := 1 }),
    (11, { startWord := 320, endWord := 567, endBitCutoff := 7651, subMod := 1 }),
    (8, { startWord := 5896, endWord := 6044, endBitCutoff := 5940, subMod := 1 }),
    (7, { startWord := 5760, endWord := 5935, endBitCutoff := 7944, subMod := 1 }),
    (2, { startWord := 5872, endWord := 6077, endBitCutoff := 6264, subMod := 1 }),
    (1, { startWord := 5760, endWord := 5976, endBitCutoff := 1817, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (40, 7200), (41, 7819), (42, 7881), (43, 7887), (44, 7750), (45, 8162), (46, 8433), (47, 8431), (48, 8445), (49, 8411),
    (50, 8529), (51, 9094), (52, 9165), (53, 9132), (54, 9193), (55, 9179), (56, 9151), (57, 8631), (58, 8224), (59, 7802),
    (60, 7767), (61, 7765), (62, 7921), (63, 7286), (64, 6384), (65, 6131), (66, 6030), (67, 5846), (68, 3651), (69, 3453),
    (70, 3136), (71, 3), (720, 5112), (721, 5116), (722, 5426), (723, 5707), (724, 5652), (725, 5700), (726, 5660), (727, 5694),
    (728, 5696), (729, 5710), (730, 5780), (731, 5626), (732, 5606), (733, 5651), (734, 6808), (735, 6898), (736, 6833), (737, 7838),
    (738, 7671), (739, 7821), (740, 7656), (741, 7893), (742, 7352), (743, 7207), (744, 7150), (745, 7028), (746, 7158), (747, 5945),
    (748, 5697), (749, 5771), (750, 5892), (751, 5869), (752, 5833), (753, 5292), (754, 4828), (755, 4227), (756, 3123), (757, 3185),
    (758, 2997), (759, 1784)
  ]

theorem fc2kSubCert8_1_valid : checkPrefixSubCert fc2kSubCert8_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_1 : VerifiedSubCertProfile fc2kSubCert8_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_1 fc2kSubCert8_1_valid)

/-- Sub-certificate 2/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_2 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 100
  activeChunkMask := 0xf800000000000000000003c00
  numChunks := 14
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (27, { startWord := 640, endWord := 762, endBitCutoff := 6665, subMod := 1 }),
    (27, { startWord := 763, endWord := 885, endBitCutoff := 3230, subMod := 1 }),
    (21, { startWord := 640, endWord := 778, endBitCutoff := 5948, subMod := 1 }),
    (20, { startWord := 640, endWord := 791, endBitCutoff := 2943, subMod := 1 }),
    (18, { startWord := 640, endWord := 823, endBitCutoff := 4922, subMod := 1 }),
    (14, { startWord := 640, endWord := 865, endBitCutoff := 5882, subMod := 1 }),
    (11, { startWord := 640, endWord := 887, endBitCutoff := 5891, subMod := 1 }),
    (9, { startWord := 6080, endWord := 6221, endBitCutoff := 4279, subMod := 1 }),
    (9, { startWord := 6222, endWord := 6366, endBitCutoff := 2094, subMod := 1 }),
    (8, { startWord := 6080, endWord := 6248, endBitCutoff := 7499, subMod := 1 }),
    (7, { startWord := 6080, endWord := 6297, endBitCutoff := 3299, subMod := 1 }),
    (4, { startWord := 6216, endWord := 6398, endBitCutoff := 2024, subMod := 1 }),
    (2, { startWord := 6080, endWord := 6341, endBitCutoff := 7858, subMod := 1 }),
    (1, { startWord := 6080, endWord := 6381, endBitCutoff := 5818, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (80, 7275), (81, 7599), (82, 7713), (83, 7890), (84, 7853), (85, 8229), (86, 8360), (87, 8305), (88, 8367), (89, 8286),
    (90, 8759), (91, 9213), (92, 9016), (93, 9107), (94, 9111), (95, 9094), (96, 9199), (97, 8564), (98, 8357), (99, 7844),
    (100, 7826), (101, 7917), (102, 7837), (103, 7259), (104, 6477), (105, 6023), (106, 5962), (107, 6036), (108, 3950), (109, 3335),
    (110, 3129), (760, 8305), (761, 8442), (762, 8439), (763, 8517), (764, 8621), (765, 8761), (766, 8674), (767, 8603), (768, 8670),
    (769, 8525), (770, 8556), (771, 8567), (772, 8623), (773, 8510), (774, 8569), (775, 8580), (776, 8586), (777, 9412), (778, 9428),
    (779, 9338), (780, 9336), (781, 8829), (782, 8718), (783, 8663), (784, 8490), (785, 8647), (786, 8631), (787, 7996), (788, 7642),
    (789, 7890), (790, 7697), (791, 7658), (792, 7566), (793, 6113), (794, 5866), (795, 5520), (796, 4440), (797, 3888), (798, 2558),
    (799, 1982)
  ]

theorem fc2kSubCert8_2_valid : checkPrefixSubCert fc2kSubCert8_2 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_2 : VerifiedSubCertProfile fc2kSubCert8_2 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_2 fc2kSubCert8_2_valid)

/-- Sub-certificate 3/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_3 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 61
  activeChunkMask := 0x1f0000000003c000
  numChunks := 14
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (26, { startWord := 896, endWord := 1017, endBitCutoff := 2233, subMod := 1 }),
    (26, { startWord := 1018, endWord := 1139, endBitCutoff := 2532, subMod := 1 }),
    (22, { startWord := 3584, endWord := 3725, endBitCutoff := 3638, subMod := 1 }),
    (21, { startWord := 896, endWord := 1032, endBitCutoff := 6896, subMod := 1 }),
    (20, { startWord := 896, endWord := 1050, endBitCutoff := 6948, subMod := 1 }),
    (18, { startWord := 896, endWord := 1087, endBitCutoff := 3513, subMod := 1 }),
    (15, { startWord := 3584, endWord := 3729, endBitCutoff := 8040, subMod := 1 }),
    (15, { startWord := 3730, endWord := 3881, endBitCutoff := 946, subMod := 1 }),
    (14, { startWord := 896, endWord := 1140, endBitCutoff := 4373, subMod := 1 }),
    (12, { startWord := 3584, endWord := 3766, endBitCutoff := 7616, subMod := 1 }),
    (11, { startWord := 896, endWord := 1137, endBitCutoff := 8054, subMod := 1 }),
    (10, { startWord := 3584, endWord := 3837, endBitCutoff := 5099, subMod := 1 }),
    (6, { startWord := 3584, endWord := 3882, endBitCutoff := 3401, subMod := 1 }),
    (1, { startWord := 3648, endWord := 3902, endBitCutoff := 976, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (112, 7033), (113, 7443), (114, 7759), (115, 7777), (116, 7611), (117, 8041), (118, 8272), (119, 8199), (120, 8267), (121, 8347),
    (122, 8543), (123, 9065), (124, 9145), (125, 8968), (126, 9063), (127, 8792), (128, 8995), (129, 8332), (130, 8101), (131, 7993),
    (132, 7528), (133, 7633), (134, 7719), (135, 7691), (136, 7082), (137, 5979), (138, 5858), (139, 5823), (140, 5160), (141, 5338),
    (142, 2335), (448, 7547), (449, 7508), (450, 7376), (451, 7688), (452, 7624), (453, 8027), (454, 8038), (455, 8014), (456, 9106),
    (457, 9033), (458, 9254), (459, 8950), (460, 9170), (461, 8998), (462, 9042), (463, 9087), (464, 9047), (465, 8933), (466, 8728),
    (467, 8700), (468, 8739), (469, 8868), (470, 8689), (471, 7949), (472, 7972), (473, 8012), (474, 7874), (475, 7913), (476, 7973),
    (477, 8031), (478, 7801), (479, 7819), (480, 6955), (481, 6967), (482, 7116), (483, 6912), (484, 6525), (485, 4385), (486, 3583),
    (487, 1903)
  ]

theorem fc2kSubCert8_3_valid : checkPrefixSubCert fc2kSubCert8_3 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_3 : VerifiedSubCertProfile fc2kSubCert8_3 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_3 fc2kSubCert8_3_valid)

/-- Sub-certificate 4/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_4 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 65
  activeChunkMask := 0x1e0000000007c0000
  numChunks := 13
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (26, { startWord := 1176, endWord := 1298, endBitCutoff := 3511, subMod := 1 }),
    (26, { startWord := 1299, endWord := 1420, endBitCutoff := 5880, subMod := 1 }),
    (22, { startWord := 1152, endWord := 1291, endBitCutoff := 2676, subMod := 1 }),
    (21, { startWord := 1152, endWord := 1293, endBitCutoff := 7668, subMod := 1 }),
    (20, { startWord := 1152, endWord := 1325, endBitCutoff := 4996, subMod := 1 }),
    (18, { startWord := 1152, endWord := 1369, endBitCutoff := 6687, subMod := 1 }),
    (16, { startWord := 1288, endWord := 1468, endBitCutoff := 2885, subMod := 1 }),
    (15, { startWord := 3904, endWord := 4042, endBitCutoff := 1716, subMod := 1 }),
    (14, { startWord := 1152, endWord := 1441, endBitCutoff := 5740, subMod := 1 }),
    (13, { startWord := 4008, endWord := 4154, endBitCutoff := 1921, subMod := 1 }),
    (12, { startWord := 3904, endWord := 4081, endBitCutoff := 2539, subMod := 1 }),
    (11, { startWord := 1152, endWord := 1429, endBitCutoff := 2276, subMod := 1 }),
    (10, { startWord := 3904, endWord := 4124, endBitCutoff := 5120, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (144, 7114), (145, 7582), (146, 7750), (147, 8157), (148, 8100), (149, 8441), (150, 8774), (151, 8835), (152, 8681), (153, 8732),
    (154, 8802), (155, 9190), (156, 9219), (157, 9244), (158, 9207), (159, 9227), (160, 9157), (161, 9279), (162, 8798), (163, 8834),
    (164, 8864), (165, 9144), (166, 9059), (167, 9251), (168, 9159), (169, 9075), (170, 9088), (171, 8319), (172, 7605), (173, 7215),
    (174, 7065), (175, 7205), (176, 7074), (177, 6956), (178, 6118), (179, 5117), (180, 3893), (181, 3487), (182, 3265), (183, 1774),
    (488, 6304), (489, 6656), (490, 6731), (491, 6644), (492, 6827), (493, 6704), (494, 6805), (495, 6600), (496, 6615), (497, 6616),
    (498, 6783), (499, 6699), (500, 6814), (501, 7906), (502, 7862), (503, 7990), (504, 7915), (505, 7164), (506, 6747), (507, 6746),
    (508, 6876), (509, 6768), (510, 5379), (511, 5344), (512, 5306), (513, 5214), (514, 5148), (515, 4625), (516, 3487), (517, 3458),
    (518, 3452), (519, 725)
  ]

theorem fc2kSubCert8_4_valid : checkPrefixSubCert fc2kSubCert8_4 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_4 : VerifiedSubCertProfile fc2kSubCert8_4 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_4 fc2kSubCert8_4_valid)

/-- Sub-certificate 5/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_5 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 70
  activeChunkMask := 0x3e0000000007800000
  numChunks := 14
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (26, { startWord := 1472, endWord := 1593, endBitCutoff := 1624, subMod := 1 }),
    (26, { startWord := 1594, endWord := 1716, endBitCutoff := 3060, subMod := 1 }),
    (22, { startWord := 4160, endWord := 4302, endBitCutoff := 3718, subMod := 1 }),
    (21, { startWord := 1472, endWord := 1609, endBitCutoff := 1301, subMod := 1 }),
    (20, { startWord := 1472, endWord := 1628, endBitCutoff := 4652, subMod := 1 }),
    (18, { startWord := 1472, endWord := 1665, endBitCutoff := 1617, subMod := 1 }),
    (16, { startWord := 1472, endWord := 1701, endBitCutoff := 1484, subMod := 1 }),
    (15, { startWord := 4160, endWord := 4307, endBitCutoff := 2815, subMod := 1 }),
    (13, { startWord := 4160, endWord := 4333, endBitCutoff := 2100, subMod := 1 }),
    (12, { startWord := 4160, endWord := 4366, endBitCutoff := 2213, subMod := 1 }),
    (11, { startWord := 1472, endWord := 1717, endBitCutoff := 6321, subMod := 1 }),
    (10, { startWord := 4160, endWord := 4419, endBitCutoff := 4135, subMod := 1 }),
    (7, { startWord := 4280, endWord := 4477, endBitCutoff := 5365, subMod := 1 }),
    (6, { startWord := 4160, endWord := 4478, endBitCutoff := 1849, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (184, 7028), (185, 7540), (186, 7774), (187, 7882), (188, 7682), (189, 8106), (190, 8353), (191, 8393), (192, 8288), (193, 8550),
    (194, 8709), (195, 9007), (196, 8928), (197, 9123), (198, 9013), (199, 8946), (200, 8980), (201, 8312), (202, 8380), (203, 7913),
    (204, 7656), (205, 7823), (206, 7671), (207, 7971), (208, 7118), (209, 6300), (210, 5885), (211, 5631), (212, 5024), (213, 3517),
    (214, 2389), (520, 8467), (521, 8775), (522, 8714), (523, 8710), (524, 8727), (525, 8899), (526, 9087), (527, 9046), (528, 8985),
    (529, 9085), (530, 9009), (531, 8977), (532, 9214), (533, 9079), (534, 9147), (535, 9928), (536, 9932), (537, 9749), (538, 9088),
    (539, 8658), (540, 8746), (541, 8463), (542, 7850), (543, 7885), (544, 7886), (545, 7571), (546, 6631), (547, 6433), (548, 6757),
    (549, 6693), (550, 6742), (551, 6639), (552, 6125), (553, 5673), (554, 5763), (555, 5600), (556, 5186), (557, 5257), (558, 5102),
    (559, 3578)
  ]

theorem fc2kSubCert8_5_valid : checkPrefixSubCert fc2kSubCert8_5 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_5 : VerifiedSubCertProfile fc2kSubCert8_5 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_5 fc2kSubCert8_5_valid)

/-- Sub-certificate 6/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_6 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 53
  activeChunkMask := 0x1f000078000000
  numChunks := 14
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (25, { startWord := 1728, endWord := 1849, endBitCutoff := 4767, subMod := 1 }),
    (25, { startWord := 1850, endWord := 1971, endBitCutoff := 5997, subMod := 1 }),
    (22, { startWord := 3072, endWord := 3207, endBitCutoff := 4149, subMod := 1 }),
    (19, { startWord := 1728, endWord := 1866, endBitCutoff := 7867, subMod := 1 }),
    (19, { startWord := 3072, endWord := 3226, endBitCutoff := 1216, subMod := 1 }),
    (17, { startWord := 1816, endWord := 1973, endBitCutoff := 834, subMod := 1 }),
    (17, { startWord := 3072, endWord := 3259, endBitCutoff := 7928, subMod := 1 }),
    (16, { startWord := 1728, endWord := 1903, endBitCutoff := 5357, subMod := 1 }),
    (15, { startWord := 3072, endWord := 3291, endBitCutoff := 6233, subMod := 1 }),
    (14, { startWord := 1728, endWord := 1936, endBitCutoff := 2131, subMod := 1 }),
    (12, { startWord := 3224, endWord := 3389, endBitCutoff := 4928, subMod := 1 }),
    (10, { startWord := 3072, endWord := 3346, endBitCutoff := 2136, subMod := 1 }),
    (6, { startWord := 1728, endWord := 1979, endBitCutoff := 3655, subMod := 1 }),
    (6, { startWord := 3072, endWord := 3371, endBitCutoff := 4610, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (216, 6832), (217, 7261), (218, 7556), (219, 8137), (220, 7939), (221, 8044), (222, 7978), (223, 7898), (224, 7835), (225, 8057),
    (226, 7922), (227, 8668), (228, 8960), (229, 9027), (230, 8868), (231, 8807), (232, 8919), (233, 8626), (234, 8393), (235, 8590),
    (236, 7912), (237, 7761), (238, 6864), (239, 6635), (240, 6668), (241, 6745), (242, 5282), (243, 5390), (244, 5232), (245, 5303),
    (246, 4416), (247, 1367), (384, 7684), (385, 8291), (386, 8475), (387, 8999), (388, 8905), (389, 8987), (390, 9025), (391, 9012),
    (392, 9068), (393, 8879), (394, 8840), (395, 9135), (396, 9028), (397, 8942), (398, 8916), (399, 9108), (400, 8997), (401, 8672),
    (402, 8771), (403, 9226), (404, 8912), (405, 9500), (406, 9165), (407, 8908), (408, 8299), (409, 8217), (410, 8307), (411, 7793),
    (412, 7196), (413, 6972), (414, 7029), (415, 7103), (416, 7063), (417, 6463), (418, 5520), (419, 5074), (420, 4777), (421, 4050),
    (422, 2847), (423, 1701)
  ]

theorem fc2kSubCert8_6_valid : checkPrefixSubCert fc2kSubCert8_6 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_6 : VerifiedSubCertProfile fc2kSubCert8_6 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_6 fc2kSubCert8_6_valid)

/-- Sub-certificate 7/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_7 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 77
  activeChunkMask := 0x1c0000e0000380000000
  numChunks := 10
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (25, { startWord := 2048, endWord := 2170, endBitCutoff := 5170, subMod := 1 }),
    (25, { startWord := 3392, endWord := 3515, endBitCutoff := 6781, subMod := 1 }),
    (19, { startWord := 1984, endWord := 2115, endBitCutoff := 870, subMod := 1 }),
    (19, { startWord := 3392, endWord := 3546, endBitCutoff := 5606, subMod := 1 }),
    (17, { startWord := 1984, endWord := 2145, endBitCutoff := 2261, subMod := 1 }),
    (17, { startWord := 3392, endWord := 3573, endBitCutoff := 6535, subMod := 1 }),
    (16, { startWord := 1984, endWord := 2166, endBitCutoff := 674, subMod := 1 }),
    (13, { startWord := 4736, endWord := 4888, endBitCutoff := 5509, subMod := 1 }),
    (12, { startWord := 4736, endWord := 4897, endBitCutoff := 1686, subMod := 1 }),
    (10, { startWord := 4736, endWord := 4922, endBitCutoff := 5516, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (248, 4559), (249, 5424), (250, 5745), (251, 6247), (252, 6313), (253, 6254), (254, 6221), (255, 6300), (256, 7029), (257, 6867),
    (258, 6746), (259, 6661), (260, 6744), (261, 6691), (262, 6772), (263, 6694), (264, 6088), (265, 6027), (266, 6118), (267, 5283),
    (268, 4402), (269, 3523), (270, 3225), (271, 504), (424, 3425), (425, 4135), (426, 4550), (427, 6008), (428, 5863), (429, 5966),
    (430, 5876), (431, 5960), (432, 5928), (433, 5730), (434, 5768), (435, 5993), (436, 5911), (437, 5894), (438, 5866), (439, 5551),
    (440, 5195), (441, 5319), (442, 4435), (443, 3716), (444, 3650), (445, 3573), (446, 2149), (447, 485), (592, 5981), (593, 6052),
    (594, 6324), (595, 6574), (596, 6527), (597, 6396), (598, 6536), (599, 6488), (600, 6518), (601, 6707), (602, 6658), (603, 6568),
    (604, 6673), (605, 6629), (606, 6649), (607, 6580), (608, 6583), (609, 6634), (610, 6078), (611, 4566), (612, 2861), (613, 2508),
    (614, 2533), (615, 814)
  ]

theorem fc2kSubCert8_7_valid : checkPrefixSubCert fc2kSubCert8_7 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_7 : VerifiedSubCertProfile fc2kSubCert8_7 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_7 fc2kSubCert8_7_valid)

/-- Sub-certificate 8/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_8 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 105
  activeChunkMask := 0x1f0000780000000000000000000
  numChunks := 13
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (25, { startWord := 5056, endWord := 5181, endBitCutoff := 3932, subMod := 1 }),
    (25, { startWord := 5182, endWord := 5307, endBitCutoff := 7956, subMod := 1 }),
    (13, { startWord := 5056, endWord := 5214, endBitCutoff := 4383, subMod := 1 }),
    (12, { startWord := 5056, endWord := 5221, endBitCutoff := 1591, subMod := 1 }),
    (9, { startWord := 6400, endWord := 6546, endBitCutoff := 7509, subMod := 1 }),
    (9, { startWord := 6547, endWord := 6694, endBitCutoff := 4973, subMod := 1 }),
    (8, { startWord := 6400, endWord := 6565, endBitCutoff := 2160, subMod := 1 }),
    (7, { startWord := 5056, endWord := 5264, endBitCutoff := 2046, subMod := 1 }),
    (7, { startWord := 6400, endWord := 6606, endBitCutoff := 8133, subMod := 1 }),
    (6, { startWord := 5056, endWord := 5279, endBitCutoff := 1139, subMod := 1 }),
    (4, { startWord := 6400, endWord := 6646, endBitCutoff := 6666, subMod := 1 }),
    (2, { startWord := 6400, endWord := 6665, endBitCutoff := 6812, subMod := 1 }),
    (1, { startWord := 6400, endWord := 6717, endBitCutoff := 1486, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (632, 7770), (633, 7612), (634, 7624), (635, 7499), (636, 7623), (637, 7637), (638, 7654), (639, 7562), (640, 7665), (641, 7454),
    (642, 7376), (643, 7519), (644, 7626), (645, 7595), (646, 7587), (647, 7495), (648, 7641), (649, 7699), (650, 7546), (651, 7537),
    (652, 6165), (653, 5115), (654, 5236), (655, 5197), (656, 5050), (657, 5203), (658, 3560), (659, 3268), (660, 1224), (661, 1252),
    (662, 1279), (663, 640), (800, 9224), (801, 9348), (802, 9353), (803, 9379), (804, 9221), (805, 9323), (806, 9389), (807, 9444),
    (808, 9318), (809, 9332), (810, 9432), (811, 9438), (812, 9434), (813, 9346), (814, 9348), (815, 9420), (816, 9327), (817, 9317),
    (818, 9336), (819, 9347), (820, 9124), (821, 8359), (822, 8550), (823, 8328), (824, 8533), (825, 8336), (826, 7429), (827, 7489),
    (828, 7390), (829, 7374), (830, 7370), (831, 6285), (832, 6202), (833, 4929), (834, 4340), (835, 4245), (836, 3817), (837, 2440),
    (838, 2560), (839, 1680)
  ]

theorem fc2kSubCert8_8_valid : checkPrefixSubCert fc2kSubCert8_8 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_8 : VerifiedSubCertProfile fc2kSubCert8_8 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_8 fc2kSubCert8_8_valid)

/-- Sub-certificate 9/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_9 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 47
  activeChunkMask := 0x71dc00000000
  numChunks := 10
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (24, { startWord := 2176, endWord := 2297, endBitCutoff := 7014, subMod := 1 }),
    (23, { startWord := 2496, endWord := 2617, endBitCutoff := 7866, subMod := 1 }),
    (19, { startWord := 2176, endWord := 2308, endBitCutoff := 7543, subMod := 1 }),
    (19, { startWord := 2816, endWord := 2969, endBitCutoff := 6746, subMod := 1 }),
    (17, { startWord := 2176, endWord := 2334, endBitCutoff := 5012, subMod := 1 }),
    (17, { startWord := 2816, endWord := 2990, endBitCutoff := 80, subMod := 1 }),
    (16, { startWord := 2176, endWord := 2361, endBitCutoff := 7358, subMod := 1 }),
    (16, { startWord := 2432, endWord := 2561, endBitCutoff := 291, subMod := 1 }),
    (15, { startWord := 2432, endWord := 2593, endBitCutoff := 1849, subMod := 1 }),
    (10, { startWord := 2432, endWord := 2622, endBitCutoff := 228, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (272, 5132), (273, 5929), (274, 6286), (275, 6804), (276, 6700), (277, 6819), (278, 6894), (279, 6982), (280, 6766), (281, 6915),
    (282, 6736), (283, 6884), (284, 6857), (285, 6870), (286, 7063), (287, 6413), (288, 5871), (289, 5293), (290, 5346), (291, 4664),
    (292, 3038), (293, 2495), (294, 2616), (295, 1064), (304, 5681), (305, 6131), (306, 6198), (307, 6044), (308, 6086), (309, 6264),
    (310, 6113), (311, 5977), (312, 6663), (313, 6609), (314, 6783), (315, 6551), (316, 6670), (317, 6680), (318, 6650), (319, 6489),
    (320, 5730), (321, 5204), (322, 5293), (323, 5243), (324, 4013), (325, 3596), (326, 3553), (327, 2216), (352, 2654), (353, 3407),
    (354, 3872), (355, 5196), (356, 5240), (357, 5948), (358, 6156), (359, 6195), (360, 6022), (361, 6060), (362, 6130), (363, 6100),
    (364, 6010), (365, 5967), (366, 6018), (367, 6150), (368, 6249), (369, 6266), (370, 5338), (371, 4567), (372, 3943), (373, 2938),
    (374, 520)
  ]

theorem fc2kSubCert8_9_valid : checkPrefixSubCert fc2kSubCert8_9 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_9 : VerifiedSubCertProfile fc2kSubCert8_9 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_9 fc2kSubCert8_9_valid)

/-- Sub-certificate 10/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_10 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 120
  activeChunkMask := 0xf81e00000000000000000000000000
  numChunks := 11
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (24, { startWord := 6720, endWord := 6845, endBitCutoff := 3880, subMod := 1 }),
    (24, { startWord := 6846, endWord := 6971, endBitCutoff := 3953, subMod := 1 }),
    (9, { startWord := 6720, endWord := 6863, endBitCutoff := 1228, subMod := 1 }),
    (8, { startWord := 6720, endWord := 6899, endBitCutoff := 910, subMod := 1 }),
    (8, { startWord := 7360, endWord := 7503, endBitCutoff := 125, subMod := 1 }),
    (5, { startWord := 7536, endWord := 7674, endBitCutoff := 2883, subMod := 1 }),
    (4, { startWord := 6720, endWord := 6943, endBitCutoff := 5984, subMod := 1 }),
    (4, { startWord := 7360, endWord := 7552, endBitCutoff := 5096, subMod := 1 }),
    (2, { startWord := 6720, endWord := 6946, endBitCutoff := 2976, subMod := 1 }),
    (2, { startWord := 7360, endWord := 7563, endBitCutoff := 3287, subMod := 1 }),
    (1, { startWord := 6720, endWord := 6969, endBitCutoff := 2158, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (840, 8361), (841, 8483), (842, 8621), (843, 8527), (844, 8499), (845, 8485), (846, 8466), (847, 8347), (848, 8471), (849, 8467),
    (850, 8538), (851, 8551), (852, 8423), (853, 8369), (854, 8367), (855, 8316), (856, 8491), (857, 8533), (858, 7531), (859, 7483),
    (860, 7570), (861, 7462), (862, 6814), (863, 6708), (864, 6538), (865, 6527), (866, 6488), (867, 6604), (868, 3921), (869, 3461),
    (870, 3498), (871, 972), (920, 5737), (921, 5643), (922, 5658), (923, 5643), (924, 5819), (925, 6040), (926, 6275), (927, 6185),
    (928, 6254), (929, 6065), (930, 6267), (931, 6223), (932, 6174), (933, 6283), (934, 6081), (935, 6180), (936, 6225), (937, 5923),
    (938, 5194), (939, 4979), (940, 5012), (941, 4947), (942, 6544), (943, 6492), (944, 5372), (945, 4153), (946, 3518), (947, 3325),
    (948, 3531), (949, 3481), (950, 3360), (951, 3488), (952, 3551), (953, 3306), (954, 3468), (955, 3475), (956, 3285), (957, 2445),
    (958, 2521), (959, 788)
  ]

theorem fc2kSubCert8_10_valid : checkPrefixSubCert fc2kSubCert8_10 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_10 : VerifiedSubCertProfile fc2kSubCert8_10 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_10 fc2kSubCert8_10_valid)

/-- Sub-certificate 11/15 for FC2K certificate 8 (`9` active super-chunks). -/
def fc2kSubCert8_11 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 125
  activeChunkMask := 0x1f03c000000000000000000000000000
  numChunks := 9
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (24, { startWord := 7040, endWord := 7165, endBitCutoff := 4808, subMod := 1 }),
    (24, { startWord := 7166, endWord := 7292, endBitCutoff := 742, subMod := 1 }),
    (9, { startWord := 7040, endWord := 7183, endBitCutoff := 1974, subMod := 1 }),
    (8, { startWord := 7040, endWord := 7218, endBitCutoff := 5027, subMod := 1 }),
    (5, { startWord := 7680, endWord := 7817, endBitCutoff := 5625, subMod := 1 }),
    (5, { startWord := 7818, endWord := 7958, endBitCutoff := 168, subMod := 1 }),
    (4, { startWord := 7040, endWord := 7261, endBitCutoff := 7708, subMod := 1 }),
    (4, { startWord := 7680, endWord := 7861, endBitCutoff := 4793, subMod := 1 }),
    (2, { startWord := 7040, endWord := 7267, endBitCutoff := 4339, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (880, 7413), (881, 7366), (882, 7266), (883, 7445), (884, 7505), (885, 7460), (886, 7685), (887, 7536), (888, 7516), (889, 7703),
    (890, 7503), (891, 7350), (892, 7465), (893, 7533), (894, 7499), (895, 7569), (896, 7569), (897, 7273), (898, 6142), (899, 6230),
    (900, 6182), (901, 6014), (902, 5483), (903, 5076), (904, 5176), (905, 5030), (906, 4986), (907, 4568), (908, 2215), (909, 1260),
    (910, 1256), (911, 636), (960, 4462), (961, 4373), (962, 4581), (963, 4374), (964, 4476), (965, 4744), (966, 5065), (967, 5105),
    (968, 5059), (969, 5025), (970, 5025), (971, 5096), (972, 5052), (973, 5003), (974, 5074), (975, 4955), (976, 5062), (977, 5063),
    (978, 4985), (979, 5221), (980, 5059), (981, 4972), (982, 4609), (983, 3412), (984, 3599), (985, 3410), (986, 3523), (987, 3506),
    (988, 3448), (989, 3479), (990, 3369), (991, 3507), (992, 3536), (993, 3375), (994, 2985), (995, 1293), (996, 1046)
  ]

theorem fc2kSubCert8_11_valid : checkPrefixSubCert fc2kSubCert8_11 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_11 : VerifiedSubCertProfile fc2kSubCert8_11 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_11 fc2kSubCert8_11_valid)

/-- Sub-certificate 12/15 for FC2K certificate 8 (`8` active super-chunks). -/
def fc2kSubCert8_12 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 138
  activeChunkMask := 0x38ce0000000000000000000000000000000
  numChunks := 6
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (24, { startWord := 8000, endWord := 8126, endBitCutoff := 539, subMod := 1 }),
    (23, { startWord := 8320, endWord := 8446, endBitCutoff := 6498, subMod := 1 }),
    (5, { startWord := 8000, endWord := 8139, endBitCutoff := 3461, subMod := 1 }),
    (5, { startWord := 8640, endWord := 8794, endBitCutoff := 931, subMod := 1 }),
    (3, { startWord := 8032, endWord := 8189, endBitCutoff := 1430, subMod := 1 }),
    (3, { startWord := 8640, endWord := 8825, endBitCutoff := 1320, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1000, 3463), (1001, 3393), (1002, 3488), (1003, 3465), (1004, 5252), (1005, 5074), (1006, 5218), (1007, 5267), (1008, 5200), (1009, 5186),
    (1010, 5290), (1011, 5196), (1012, 5197), (1013, 5135), (1014, 5061), (1015, 5029), (1016, 4373), (1017, 3342), (1018, 2442), (1019, 2394),
    (1020, 2466), (1021, 2506), (1022, 2382), (1023, 1636), (1040, 1213), (1041, 1228), (1042, 1266), (1043, 1275), (1044, 1264), (1045, 1234),
    (1046, 1208), (1047, 1238), (1048, 1198), (1049, 1212), (1050, 1274), (1051, 1257), (1052, 1213), (1053, 1197), (1054, 1199), (1055, 1015),
    (1080, 4442), (1081, 4392), (1082, 4537), (1083, 5050), (1084, 4864), (1085, 5633), (1086, 5973), (1087, 5862), (1088, 5802), (1089, 5800),
    (1090, 5819), (1091, 5866), (1092, 5981), (1093, 5777), (1094, 5777), (1095, 5667), (1096, 5859), (1097, 5791), (1098, 5531), (1099, 3876),
    (1100, 3468), (1101, 2461), (1102, 2390), (1103, 328)
  ]

theorem fc2kSubCert8_12_valid : checkPrefixSubCert fc2kSubCert8_12 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_12 : VerifiedSubCertProfile fc2kSubCert8_12 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_12 fc2kSubCert8_12_valid)

/-- Sub-certificate 13/15 for FC2K certificate 8 (`8` active super-chunks). -/
def fc2kSubCert8_13 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 146
  activeChunkMask := 0x39c6000000000000000000000000000000000
  numChunks := 6
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (23, { startWord := 8512, endWord := 8639, endBitCutoff := 421, subMod := 1 }),
    (23, { startWord := 8832, endWord := 8959, endBitCutoff := 3682, subMod := 1 }),
    (5, { startWord := 8832, endWord := 8994, endBitCutoff := 3782, subMod := 1 }),
    (3, { startWord := 8832, endWord := 9021, endBitCutoff := 7701, subMod := 1 }),
    (3, { startWord := 9152, endWord := 9304, endBitCutoff := 835, subMod := 1 }),
    (0, { startWord := 9184, endWord := 9342, endBitCutoff := 7804, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1064, 1252), (1065, 1286), (1066, 1250), (1067, 1249), (1068, 1176), (1069, 1204), (1070, 1243), (1071, 1204), (1072, 1158), (1073, 1294),
    (1074, 1191), (1075, 1265), (1076, 1213), (1077, 1189), (1078, 1257), (1079, 1060), (1104, 4982), (1105, 5005), (1106, 5150), (1107, 5662),
    (1108, 5656), (1109, 5618), (1110, 5575), (1111, 5535), (1112, 5622), (1113, 5617), (1114, 5552), (1115, 5677), (1116, 5643), (1117, 5661),
    (1118, 5548), (1119, 5487), (1120, 4817), (1121, 4970), (1122, 4815), (1123, 4432), (1124, 3060), (1125, 2461), (1126, 2503), (1127, 1898),
    (1144, 2358), (1145, 2341), (1146, 2743), (1147, 3230), (1148, 4893), (1149, 4986), (1150, 5039), (1151, 4976), (1152, 5080), (1153, 5087),
    (1154, 5002), (1155, 4884), (1156, 5023), (1157, 5049), (1158, 4995), (1159, 4862), (1160, 5070), (1161, 4979), (1162, 4780), (1163, 2532),
    (1164, 2396), (1165, 2488), (1166, 2482), (1167, 2180)
  ]

theorem fc2kSubCert8_13_valid : checkPrefixSubCert fc2kSubCert8_13 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_13 : VerifiedSubCertProfile fc2kSubCert8_13 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_13 fc2kSubCert8_13_valid)

/-- Sub-certificate 14/15 for FC2K certificate 8 (`8` active super-chunks). -/
def fc2kSubCert8_14 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 154
  activeChunkMask := 0x39c600000000000000000000000000000000000
  numChunks := 6
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (23, { startWord := 9024, endWord := 9150, endBitCutoff := 4169, subMod := 1 }),
    (23, { startWord := 9344, endWord := 9471, endBitCutoff := 6627, subMod := 1 }),
    (3, { startWord := 9344, endWord := 9515, endBitCutoff := 945, subMod := 1 }),
    (3, { startWord := 9664, endWord := 9815, endBitCutoff := 6993, subMod := 1 }),
    (0, { startWord := 9344, endWord := 9522, endBitCutoff := 4814, subMod := 1 }),
    (0, { startWord := 9664, endWord := 9831, endBitCutoff := 6654, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1128, 1233), (1129, 1205), (1130, 1238), (1131, 1181), (1132, 1194), (1133, 1238), (1134, 1287), (1135, 1251), (1136, 1291), (1137, 1217),
    (1138, 1209), (1139, 1259), (1140, 1231), (1141, 1245), (1142, 1209), (1143, 1003), (1168, 4911), (1169, 5010), (1170, 5355), (1171, 5787),
    (1172, 5689), (1173, 5785), (1174, 5531), (1175, 5663), (1176, 5696), (1177, 5807), (1178, 5712), (1179, 5735), (1180, 5685), (1181, 5629),
    (1182, 5775), (1183, 5764), (1184, 5057), (1185, 4900), (1186, 4653), (1187, 4360), (1188, 4515), (1189, 3129), (1190, 798), (1208, 4372),
    (1209, 4294), (1210, 4723), (1211, 4959), (1212, 4893), (1213, 4977), (1214, 4907), (1215, 4922), (1216, 4976), (1217, 4947), (1218, 5029),
    (1219, 5054), (1220, 4940), (1221, 5004), (1222, 5085), (1223, 4875), (1224, 4968), (1225, 5023), (1226, 4711), (1227, 2454), (1228, 2342)
  ]

theorem fc2kSubCert8_14_valid : checkPrefixSubCert fc2kSubCert8_14 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_14 : VerifiedSubCertProfile fc2kSubCert8_14 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_14 fc2kSubCert8_14_valid)

/-- Sub-certificate 15/15 for FC2K certificate 8 (`7` active super-chunks). -/
def fc2kSubCert8_15 : PrefixSubCert where
  corrLo := 440228507
  numSuperChunks := 161
  activeChunkMask := 0x1fc00000000000000000000000000000000000000
  numChunks := 3
  qSub := 19491
  maxHi := 943544989
  chunks := [
    (0, { startWord := 9856, endWord := 9984, endBitCutoff := 6923, subMod := 1 }),
    (0, { startWord := 9985, endWord := 10111, endBitCutoff := 8096, subMod := 1 }),
    (0, { startWord := 10112, endWord := 10239, endBitCutoff := 6398, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (1232, 2438), (1233, 2388), (1234, 2440), (1235, 2450), (1236, 2438), (1237, 2390), (1238, 2470), (1239, 2390), (1240, 2438), (1241, 2476),
    (1242, 2348), (1243, 2454), (1244, 2332), (1245, 2480), (1246, 2370), (1247, 2442), (1248, 2438), (1249, 2396), (1250, 2462), (1251, 2434),
    (1252, 2488), (1253, 2428), (1254, 2502), (1255, 2466), (1256, 2438), (1257, 2514), (1258, 2460), (1259, 2410), (1260, 2446), (1261, 2440),
    (1262, 2468), (1263, 2430), (1264, 2544), (1265, 2516), (1266, 2504), (1267, 2406), (1268, 2380), (1269, 2376), (1270, 2462), (1271, 2466),
    (1272, 2470), (1273, 2390), (1274, 2504), (1275, 2434), (1276, 2342), (1277, 2398), (1278, 2468), (1279, 2322)
  ]

theorem fc2kSubCert8_15_valid : checkPrefixSubCert fc2kSubCert8_15 = true := by
  decide +kernel

private noncomputable def fc2kSubProf8_15 : VerifiedSubCertProfile fc2kSubCert8_15 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert8_15 fc2kSubCert8_15_valid)

def fc2kSubCerts8 : List PrefixSubCert := [fc2kSubCert8_0, fc2kSubCert8_1, fc2kSubCert8_2, fc2kSubCert8_3, fc2kSubCert8_4, fc2kSubCert8_5, fc2kSubCert8_6, fc2kSubCert8_7, fc2kSubCert8_8, fc2kSubCert8_9, fc2kSubCert8_10, fc2kSubCert8_11, fc2kSubCert8_12, fc2kSubCert8_13, fc2kSubCert8_14, fc2kSubCert8_15]

def fc2kPlan8 : MultiSubCertPlan where
  P := 28
  M := 6
  qSub := 19491
  qCert := 116946
  corrLo := 440228507
  maxHi := 943544989
  numOcts := 1610
  routes := [
    [(13, 5), (14, 4), (14, 5), (15, 0), (15, 1), (15, 2)],
    [(3, 13), (0, 12), (1, 11), (2, 13), (8, 12), (10, 10)],
    [(1, 10), (2, 12), (8, 11), (10, 8), (11, 8), (10, 9)],
    [(12, 4), (12, 5), (13, 3), (13, 4), (14, 2), (14, 3)],
    [(2, 11), (8, 10), (10, 6), (11, 6), (10, 7), (11, 7)],
    [(10, 5), (11, 4), (11, 5), (12, 2), (12, 3), (13, 2)],
    [(6, 12), (6, 13), (3, 12), (5, 13), (8, 9), (0, 11)],
    [(5, 12), (8, 7), (0, 10), (1, 9), (2, 10), (8, 8)],
    [(1, 8), (2, 9), (8, 6), (10, 3), (11, 3), (10, 4)],
    [(2, 7), (2, 8), (8, 4), (8, 5), (10, 2), (11, 2)],
    [(9, 9), (6, 11), (3, 11), (4, 12), (5, 11), (7, 9)],
    [(0, 9), (1, 7), (2, 6), (3, 10), (4, 11), (5, 10)],
    [(6, 10), (3, 9), (4, 10), (5, 9), (7, 8), (8, 3)],
    [(4, 9), (5, 8), (7, 7), (8, 2), (0, 7), (0, 8)],
    [(0, 6), (1, 6), (2, 5), (3, 8), (4, 8), (6, 9)],
    [(9, 8), (6, 8), (3, 6), (3, 7), (4, 7), (5, 7)],
    [(4, 6), (5, 6), (6, 7), (7, 6), (9, 6), (9, 7)],
    [(6, 5), (7, 4), (9, 4), (9, 5), (6, 6), (7, 5)],
    [(0, 5), (1, 5), (2, 4), (3, 5), (4, 5), (5, 5)],
    [(6, 3), (7, 2), (9, 2), (9, 3), (6, 4), (7, 3)],
    [(0, 4), (1, 4), (2, 3), (3, 4), (4, 4), (5, 4)],
    [(0, 3), (1, 3), (2, 2), (3, 3), (4, 3), (5, 3)],
    [(4, 2), (6, 2), (3, 2), (5, 2), (0, 2), (1, 2)],
    [(9, 1), (12, 1), (13, 0), (13, 1), (14, 0), (14, 1)],
    [(9, 0), (10, 0), (10, 1), (11, 0), (11, 1), (12, 0)],
    [(6, 0), (6, 1), (7, 0), (7, 1), (8, 0), (8, 1)],
    [(3, 0), (3, 1), (4, 0), (4, 1), (5, 0), (5, 1)],
    [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]
  ]
  windowCaps := []
  octWindowCaps := [
    { minWordIdx := 2127, spanWords := 264, cap := 0 },
    { minWordIdx := 2805, spanWords := 156, cap := 0 },
    { minWordIdx := 3069, spanWords := 301, cap := 0 },
    { minWordIdx := 3069, spanWords := 331, cap := 0 },
    { minWordIdx := 4050, spanWords := 81, cap := 0 },
    { minWordIdx := 4452, spanWords := 221, cap := 0 },
    { minWordIdx := 4452, spanWords := 887, cap := 0 },
    { minWordIdx := 4688, spanWords := 156, cap := 0 },
    { minWordIdx := 4691, spanWords := 42, cap := 0 },
    { minWordIdx := 5933, spanWords := 81, cap := 0 },
    { minWordIdx := 6016, spanWords := 42, cap := 0 },
    { minWordIdx := 6068, spanWords := 276, cap := 0 },
    { minWordIdx := 6068, spanWords := 1110, cap := 0 },
    { minWordIdx := 6575, spanWords := 42, cap := 0 },
    { minWordIdx := 6619, spanWords := 81, cap := 0 },
    { minWordIdx := 7789, spanWords := 156, cap := 0 },
    { minWordIdx := 7899, spanWords := 42, cap := 0 },
    { minWordIdx := 8358, spanWords := 264, cap := 0 },
    { minWordIdx := 8502, spanWords := 81, cap := 0 },
    { minWordIdx := 9673, spanWords := 156, cap := 0 },
    { minWordIdx := 11117, spanWords := 331, cap := 0 },
    { minWordIdx := 11147, spanWords := 301, cap := 0 }
  ]

theorem fc2kPlan8_valid : checkMultiSubCertPlan fc2kSubCerts8 fc2kPlan8 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs8 :
    ∀ g : Fin fc2kSubCerts8.length,
      VerifiedSubCertProfile (fc2kSubCerts8[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf8_0
  | ⟨1, _⟩ => fc2kSubProf8_1
  | ⟨2, _⟩ => fc2kSubProf8_2
  | ⟨3, _⟩ => fc2kSubProf8_3
  | ⟨4, _⟩ => fc2kSubProf8_4
  | ⟨5, _⟩ => fc2kSubProf8_5
  | ⟨6, _⟩ => fc2kSubProf8_6
  | ⟨7, _⟩ => fc2kSubProf8_7
  | ⟨8, _⟩ => fc2kSubProf8_8
  | ⟨9, _⟩ => fc2kSubProf8_9
  | ⟨10, _⟩ => fc2kSubProf8_10
  | ⟨11, _⟩ => fc2kSubProf8_11
  | ⟨12, _⟩ => fc2kSubProf8_12
  | ⟨13, _⟩ => fc2kSubProf8_13
  | ⟨14, _⟩ => fc2kSubProf8_14
  | ⟨15, _⟩ => fc2kSubProf8_15
  | ⟨k + 16, h⟩ => False.elim (by change k + 16 < 16 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 8. -/
noncomputable def fc2kPrefixProfile8 :
    GeneralPrefixProfile 28 116946 440228507 943544989 :=
  assembleGeneralPrefixProfile fc2kSubCerts8 fc2kPlan8 fc2kPlan8_valid fc2kSubProfs8

end Sude
