import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 5

Certifies `P = 27` power-of-two prime-pair stages (`qCert = 37842`, `2` chunk(s) of `18921`)
in `[69475637, 276159799]` via `4` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 14140`).
-/

namespace Sude

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/3 for FC2K certificate 5 (`15` active super-chunks). -/
def fc2kSubCert5_0 : PrefixSubCert where
  corrLo := 69475637
  numSuperChunks := 48
  activeChunkMask := 0xf80001e0180f
  numChunks := 16
  qSub := 18921
  maxHi := 276159799
  chunks := [
    (26, { startWord := 24, endWord := 126, endBitCutoff := 283, subMod := 1 }),
    (26, { startWord := 127, endWord := 228, endBitCutoff := 6879, subMod := 1 }),
    (25, { startWord := 0, endWord := 98, endBitCutoff := 6703, subMod := 1 }),
    (25, { startWord := 99, endWord := 198, endBitCutoff := 4949, subMod := 1 }),
    (24, { startWord := 24, endWord := 133, endBitCutoff := 4319, subMod := 1 }),
    (24, { startWord := 704, endWord := 805, endBitCutoff := 1826, subMod := 1 }),
    (22, { startWord := 2792, endWord := 2898, endBitCutoff := 7387, subMod := 1 }),
    (21, { startWord := 36, endWord := 167, endBitCutoff := 1402, subMod := 1 }),
    (16, { startWord := 112, endWord := 250, endBitCutoff := 8050, subMod := 1 }),
    (15, { startWord := 708, endWord := 829, endBitCutoff := 5440, subMod := 1 }),
    (15, { startWord := 1484, endWord := 1597, endBitCutoff := 3624, subMod := 1 }),
    (14, { startWord := 0, endWord := 172, endBitCutoff := 1209, subMod := 1 }),
    (12, { startWord := 2892, endWord := 3015, endBitCutoff := 7100, subMod := 1 }),
    (11, { startWord := 68, endWord := 254, endBitCutoff := 4757, subMod := 1 }),
    (9, { startWord := 0, endWord := 243, endBitCutoff := 3174, subMod := 1 }),
    (4, { startWord := 1344, endWord := 1478, endBitCutoff := 5915, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 6321), (1, 6303), (2, 6330), (3, 7880), (4, 8185), (5, 8442), (6, 8526), (7, 8570), (8, 9288), (9, 9842),
    (10, 9876), (11, 9791), (12, 9927), (13, 9973), (14, 10705), (15, 11016), (16, 11140), (17, 10542), (18, 10745), (19, 10634),
    (20, 10699), (21, 9759), (22, 9043), (23, 9071), (24, 8962), (25, 8410), (26, 8397), (27, 8437), (28, 8031), (29, 7827),
    (30, 6793), (31, 4350), (88, 3433), (89, 5329), (90, 5286), (91, 5187), (92, 5266), (93, 5321), (94, 5337), (95, 5259),
    (96, 5299), (97, 5196), (98, 5233), (99, 5297), (100, 4860), (101, 4116), (102, 2894), (103, 2371), (168, 2976), (169, 2910),
    (170, 3424), (171, 4149), (172, 4042), (173, 4699), (174, 4948), (175, 5103), (176, 4916), (177, 5068), (178, 5057), (179, 5082),
    (180, 5040), (181, 5026), (182, 5057), (183, 4997), (184, 4757), (185, 4006), (186, 4065), (187, 4106), (188, 4062), (189, 4071),
    (190, 3982), (191, 4114), (192, 4097), (193, 4057), (194, 4089), (195, 3505), (196, 2961), (197, 2949), (198, 2908), (199, 2224),
    (344, 983), (345, 1478), (346, 1517), (347, 1476), (348, 1531), (349, 2883), (350, 2981), (351, 2913), (352, 2850), (353, 2895),
    (354, 2859), (355, 2926), (356, 2883), (357, 2701), (358, 2913), (359, 2893), (360, 2956), (361, 3923), (362, 4322), (363, 3987),
    (364, 3966), (365, 3861), (366, 3923), (367, 3971), (368, 3952), (369, 3937), (370, 3546), (371, 3861), (372, 3887), (373, 3885),
    (374, 3876), (375, 3780), (376, 3735), (377, 1478), (378, 1336), (379, 1375), (380, 1434), (381, 1417), (382, 1456), (383, 980)
  ]

theorem fc2kSubCert5_0_valid : checkPrefixSubCert fc2kSubCert5_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf5_0 : VerifiedSubCertProfile fc2kSubCert5_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert5_0 fc2kSubCert5_0_valid)

/-- Sub-certificate 1/3 for FC2K certificate 5 (`15` active super-chunks). -/
def fc2kSubCert5_1 : PrefixSubCert where
  corrLo := 69475637
  numSuperChunks := 53
  activeChunkMask := 0x1f00000000e7f0
  numChunks := 22
  qSub := 18921
  maxHi := 276159799
  chunks := [
    (23, { startWord := 256, endWord := 354, endBitCutoff := 3617, subMod := 1 }),
    (23, { startWord := 576, endWord := 675, endBitCutoff := 4570, subMod := 1 }),
    (22, { startWord := 3072, endWord := 3179, endBitCutoff := 7919, subMod := 1 }),
    (21, { startWord := 256, endWord := 365, endBitCutoff := 4415, subMod := 1 }),
    (20, { startWord := 308, endWord := 415, endBitCutoff := 6968, subMod := 1 }),
    (20, { startWord := 416, endWord := 518, endBitCutoff := 2372, subMod := 1 }),
    (19, { startWord := 464, endWord := 576, endBitCutoff := 6006, subMod := 1 }),
    (19, { startWord := 832, endWord := 940, endBitCutoff := 5604, subMod := 1 }),
    (18, { startWord := 548, endWord := 674, endBitCutoff := 5687, subMod := 1 }),
    (17, { startWord := 376, endWord := 520, endBitCutoff := 5826, subMod := 1 }),
    (17, { startWord := 521, endWord := 685, endBitCutoff := 575, subMod := 1 }),
    (16, { startWord := 256, endWord := 411, endBitCutoff := 7473, subMod := 1 }),
    (14, { startWord := 256, endWord := 439, endBitCutoff := 5429, subMod := 1 }),
    (13, { startWord := 3132, endWord := 3246, endBitCutoff := 7754, subMod := 1 }),
    (13, { startWord := 3247, endWord := 3368, endBitCutoff := 7458, subMod := 1 }),
    (11, { startWord := 256, endWord := 490, endBitCutoff := 6699, subMod := 1 }),
    (10, { startWord := 508, endWord := 702, endBitCutoff := 7766, subMod := 1 }),
    (9, { startWord := 256, endWord := 534, endBitCutoff := 5738, subMod := 1 }),
    (8, { startWord := 448, endWord := 702, endBitCutoff := 1756, subMod := 1 }),
    (7, { startWord := 380, endWord := 701, endBitCutoff := 7417, subMod := 1 }),
    (6, { startWord := 256, endWord := 613, endBitCutoff := 2537, subMod := 1 }),
    (4, { startWord := 284, endWord := 702, endBitCutoff := 3142, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (32, 10199), (33, 10558), (34, 10559), (35, 10952), (36, 11315), (37, 11038), (38, 11370), (39, 11641), (40, 11830), (41, 11806),
    (42, 11979), (43, 12270), (44, 12244), (45, 11996), (46, 11730), (47, 12647), (48, 12856), (49, 13038), (50, 12970), (51, 12727),
    (52, 12562), (53, 12576), (54, 12632), (55, 12015), (56, 12315), (57, 12262), (58, 12488), (59, 12484), (60, 12539), (61, 12396),
    (62, 12264), (63, 12525), (64, 12980), (65, 12427), (66, 12388), (67, 11801), (68, 11990), (69, 12412), (70, 12207), (71, 12189),
    (72, 12077), (73, 12202), (74, 12078), (75, 12282), (76, 11838), (77, 11632), (78, 11623), (79, 11459), (80, 11552), (81, 11575),
    (82, 11555), (83, 11727), (84, 11004), (85, 10263), (86, 9209), (87, 6982), (104, 1508), (105, 1496), (106, 1992), (107, 3016),
    (108, 2942), (109, 2983), (110, 3024), (111, 2996), (112, 2741), (113, 2778), (114, 3156), (115, 3994), (116, 4012), (117, 3438),
    (118, 2727), (119, 2802), (120, 1831), (121, 1500), (122, 1512), (123, 1502), (124, 1515), (125, 1559), (126, 1555), (127, 184),
    (384, 1373), (385, 1359), (386, 1417), (387, 1393), (388, 1429), (389, 1428), (390, 1436), (391, 2649), (392, 3770), (393, 3799),
    (394, 3880), (395, 3937), (396, 3856), (397, 3264), (398, 2867), (399, 2756), (400, 2765), (401, 2740), (402, 2659), (403, 2763),
    (404, 2840), (405, 3516), (406, 3795), (407, 3816), (408, 3772), (409, 3987), (410, 3861), (411, 3931), (412, 3801), (413, 3876),
    (414, 3846), (415, 3941), (416, 3760), (417, 3773), (418, 3610), (419, 2634), (420, 2818), (421, 409)
  ]

theorem fc2kSubCert5_1_valid : checkPrefixSubCert fc2kSubCert5_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf5_1 : VerifiedSubCertProfile fc2kSubCert5_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert5_1 fc2kSubCert5_1_valid)

/-- Sub-certificate 2/3 for FC2K certificate 5 (`15` active super-chunks). -/
def fc2kSubCert5_2 : PrefixSubCert where
  corrLo := 69475637
  numSuperChunks := 56
  activeChunkMask := 0xe00000fe1f0000
  numChunks := 9
  qSub := 18921
  maxHi := 276159799
  chunks := [
    (18, { startWord := 1024, endWord := 1125, endBitCutoff := 902, subMod := 1 }),
    (12, { startWord := 3392, endWord := 3500, endBitCutoff := 5038, subMod := 1 }),
    (10, { startWord := 1120, endWord := 1224, endBitCutoff := 4114, subMod := 1 }),
    (8, { startWord := 1224, endWord := 1325, endBitCutoff := 6035, subMod := 1 }),
    (7, { startWord := 1600, endWord := 1703, endBitCutoff := 3259, subMod := 1 }),
    (6, { startWord := 1704, endWord := 1807, endBitCutoff := 7416, subMod := 1 }),
    (5, { startWord := 1808, endWord := 1911, endBitCutoff := 5578, subMod := 1 }),
    (5, { startWord := 1912, endWord := 2016, endBitCutoff := 3582, subMod := 1 }),
    (3, { startWord := 3464, endWord := 3581, endBitCutoff := 1408, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (128, 1539), (129, 2492), (130, 2989), (131, 3008), (132, 3022), (133, 2976), (134, 2957), (135, 3026), (136, 3043), (137, 2973),
    (138, 3001), (139, 3022), (140, 4491), (141, 3942), (142, 2992), (143, 2916), (144, 3133), (145, 2955), (146, 2933), (147, 3037),
    (148, 2930), (149, 3013), (150, 3030), (151, 2993), (152, 3070), (153, 3165), (154, 2998), (155, 3029), (156, 2998), (157, 2984),
    (158, 2993), (159, 2966), (160, 2878), (161, 2950), (162, 2935), (163, 3041), (164, 2946), (165, 2160), (200, 2961), (201, 2921),
    (202, 2934), (203, 2937), (204, 2868), (205, 2971), (206, 2980), (207, 2934), (208, 2948), (209, 2847), (210, 2913), (211, 2929),
    (212, 2699), (213, 2949), (214, 2945), (215, 2961), (216, 2867), (217, 2853), (218, 2911), (219, 2894), (220, 2928), (221, 2938),
    (222, 2860), (223, 3000), (224, 2880), (225, 2856), (226, 2792), (227, 2909), (228, 2864), (229, 2888), (230, 2963), (231, 2974),
    (232, 2958), (233, 2790), (234, 2968), (235, 2926), (236, 3016), (237, 2916), (238, 2878), (239, 2900), (240, 2786), (241, 2812),
    (242, 2892), (243, 2882), (244, 2924), (245, 2860), (246, 3002), (247, 2854), (248, 2924), (249, 2932), (250, 2950), (251, 2968),
    (252, 156), (424, 2762), (425, 2738), (426, 2874), (427, 2862), (428, 2695), (429, 2718), (430, 2722), (431, 2813), (432, 2876),
    (433, 4928), (434, 5041), (435, 4925), (436, 5047), (437, 3863), (438, 2738), (439, 2734), (440, 2796), (441, 2820), (442, 2812),
    (443, 2752), (444, 2726), (445, 2764), (446, 2792), (447, 1886)
  ]

theorem fc2kSubCert5_2_valid : checkPrefixSubCert fc2kSubCert5_2 = true := by
  decide +kernel

private noncomputable def fc2kSubProf5_2 : VerifiedSubCertProfile fc2kSubCert5_2 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert5_2 fc2kSubCert5_2_valid)

/-- Sub-certificate 3/3 for FC2K certificate 5 (`10` active super-chunks). -/
def fc2kSubCert5_3 : PrefixSubCert where
  corrLo := 69475637
  numSuperChunks := 66
  activeChunkMask := 0x3ff00000000000000
  numChunks := 7
  qSub := 18921
  maxHi := 276159799
  chunks := [
    (3, { startWord := 3584, endWord := 3692, endBitCutoff := 1200, subMod := 1 }),
    (2, { startWord := 3656, endWord := 3772, endBitCutoff := 4461, subMod := 1 }),
    (2, { startWord := 3773, endWord := 3883, endBitCutoff := 6346, subMod := 1 }),
    (1, { startWord := 3848, endWord := 3965, endBitCutoff := 4069, subMod := 1 }),
    (1, { startWord := 3966, endWord := 4076, endBitCutoff := 3647, subMod := 1 }),
    (0, { startWord := 3960, endWord := 4093, endBitCutoff := 7412, subMod := 1 }),
    (0, { startWord := 4094, endWord := 4204, endBitCutoff := 5387, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (448, 2906), (449, 2834), (450, 2834), (451, 2674), (452, 2822), (453, 2828), (454, 2896), (455, 2834), (456, 2892), (457, 4974),
    (458, 4970), (459, 5020), (460, 4874), (461, 3896), (462, 2824), (463, 2784), (464, 2734), (465, 2740), (466, 2762), (467, 2700),
    (468, 2738), (469, 2784), (470, 2776), (471, 2628), (472, 2730), (473, 2816), (474, 2762), (475, 2734), (476, 2654), (477, 2680),
    (478, 2764), (479, 2652), (480, 2758), (481, 4968), (482, 4926), (483, 4854), (484, 5018), (485, 3676), (486, 2696), (487, 2698),
    (488, 2788), (489, 2874), (490, 2782), (491, 2826), (492, 2732), (493, 2740), (494, 2678), (495, 4734), (496, 5036), (497, 4918),
    (498, 5026), (499, 4920), (500, 4742), (501, 4894), (502, 4976), (503, 4818), (504, 4988), (505, 4906), (506, 4892), (507, 4936),
    (508, 4920), (509, 3978), (510, 2758), (511, 2824), (512, 2658), (513, 2746), (514, 2740), (515, 2762), (516, 2754), (517, 2714),
    (518, 2686), (519, 2786), (520, 2780), (521, 2736), (522, 2612), (523, 2748), (524, 2706), (525, 1670)
  ]

theorem fc2kSubCert5_3_valid : checkPrefixSubCert fc2kSubCert5_3 = true := by
  decide +kernel

private noncomputable def fc2kSubProf5_3 : VerifiedSubCertProfile fc2kSubCert5_3 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert5_3 fc2kSubCert5_3_valid)

def fc2kSubCerts5 : List PrefixSubCert := [fc2kSubCert5_0, fc2kSubCert5_1, fc2kSubCert5_2, fc2kSubCert5_3]

def fc2kPlan5 : MultiSubCertPlan where
  P := 27
  M := 2
  qSub := 18921
  qCert := 37842
  corrLo := 69475637
  maxHi := 276159799
  numOcts := 786
  routes := [
    [(3, 5), (3, 6)],
    [(3, 3), (3, 4)],
    [(3, 1), (3, 2)],
    [(2, 8), (3, 0)],
    [(1, 21), (0, 15)],
    [(2, 6), (2, 7)],
    [(1, 20), (2, 5)],
    [(1, 19), (2, 4)],
    [(1, 18), (2, 3)],
    [(0, 14), (1, 17)],
    [(1, 16), (2, 2)],
    [(0, 13), (1, 15)],
    [(0, 12), (2, 1)],
    [(1, 13), (1, 14)],
    [(0, 11), (1, 12)],
    [(0, 9), (0, 10)],
    [(0, 8), (1, 11)],
    [(1, 9), (1, 10)],
    [(1, 8), (2, 0)],
    [(1, 6), (1, 7)],
    [(1, 4), (1, 5)],
    [(0, 7), (1, 3)],
    [(0, 6), (1, 2)],
    [(1, 0), (1, 1)],
    [(0, 4), (0, 5)],
    [(0, 2), (0, 3)],
    [(0, 0), (0, 1)]
  ]
  windowCaps := []
  octWindowCaps := [
    { minWordIdx := 98, spanWords := 22, cap := 100444 },
    { minWordIdx := 98, spanWords := 25, cap := 112095 },
    { minWordIdx := 190, spanWords := 32, cap := 129280 },
    { minWordIdx := 215, spanWords := 22, cap := 92104 },
    { minWordIdx := 296, spanWords := 27, cap := 112042 },
    { minWordIdx := 296, spanWords := 105, cap := 357044 },
    { minWordIdx := 453, spanWords := 36, cap := 140186 },
    { minWordIdx := 453, spanWords := 139, cap := 250824 },
    { minWordIdx := 625, spanWords := 25, cap := 0 },
    { minWordIdx := 628, spanWords := 22, cap := 0 },
    { minWordIdx := 877, spanWords := 22, cap := 0 },
    { minWordIdx := 893, spanWords := 32, cap := 0 }
  ]

theorem fc2kPlan5_valid : checkMultiSubCertPlan fc2kSubCerts5 fc2kPlan5 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs5 :
    ∀ g : Fin fc2kSubCerts5.length,
      VerifiedSubCertProfile (fc2kSubCerts5[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf5_0
  | ⟨1, _⟩ => fc2kSubProf5_1
  | ⟨2, _⟩ => fc2kSubProf5_2
  | ⟨3, _⟩ => fc2kSubProf5_3
  | ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 5. -/
noncomputable def fc2kPrefixProfile5 :
    GeneralPrefixProfile 27 37842 69475637 276159799 :=
  assembleGeneralPrefixProfile fc2kSubCerts5 fc2kPlan5 fc2kPlan5_valid fc2kSubProfs5

end Sude
