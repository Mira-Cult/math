import Sude.FastBinaryPrefixScan

/-!
# FC2K Kernel-Verified Prefix Bank Certificate 4

Certifies `P = 26` power-of-two prime-pair stages (`qCert = 28842`, `1` chunk(s) of `28842`)
in `[39186893, 208957903]` via `4` disjoint-super-chunk sub-certificate(s)
(`totalSpanWords = 4406`).
-/

namespace Sude

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Sub-certificate 0/3 for FC2K certificate 4 (`14` active super-chunks). -/
def fc2kSubCert4_0 : PrefixSubCert where
  corrLo := 39186893
  numSuperChunks := 24
  activeChunkMask := 0xe01cff
  numChunks := 11
  qSub := 28842
  maxHi := 208957903
  chunks := [
    (25, { startWord := 0, endWord := 145, endBitCutoff := 7588, subMod := 1 }),
    (24, { startWord := 0, endWord := 141, endBitCutoff := 8058, subMod := 1 }),
    (23, { startWord := 300, endWord := 443, endBitCutoff := 3918, subMod := 1 }),
    (22, { startWord := 0, endWord := 160, endBitCutoff := 2264, subMod := 1 }),
    (21, { startWord := 144, endWord := 297, endBitCutoff := 7719, subMod := 1 }),
    (20, { startWord := 160, endWord := 347, endBitCutoff := 7135, subMod := 1 }),
    (19, { startWord := 0, endWord := 198, endBitCutoff := 6166, subMod := 1 }),
    (18, { startWord := 1344, endWord := 1514, endBitCutoff := 3698, subMod := 1 }),
    (17, { startWord := 336, endWord := 505, endBitCutoff := 974, subMod := 1 }),
    (16, { startWord := 212, endWord := 467, endBitCutoff := 5075, subMod := 1 }),
    (10, { startWord := 0, endWord := 312, endBitCutoff := 3563, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (0, 7469), (1, 7432), (2, 7747), (3, 8563), (4, 8356), (5, 8477), (6, 8343), (7, 8393), (8, 8240), (9, 8377),
    (10, 8440), (11, 8328), (12, 8349), (13, 8383), (14, 8534), (15, 8531), (16, 8497), (17, 8037), (18, 7727), (19, 7483),
    (20, 7555), (21, 7923), (22, 8208), (23, 8378), (24, 8011), (25, 7789), (26, 8544), (27, 9026), (28, 8785), (29, 9588),
    (30, 9620), (31, 9711), (32, 9521), (33, 9443), (34, 9299), (35, 9456), (36, 9410), (37, 9192), (38, 9379), (39, 8441),
    (40, 8387), (41, 7756), (42, 8495), (43, 8459), (44, 8147), (45, 8189), (46, 8116), (47, 8095), (48, 7177), (49, 6545),
    (50, 6600), (51, 6617), (52, 6706), (53, 6738), (54, 6514), (55, 6116), (56, 5645), (57, 5840), (58, 4851), (59, 3196),
    (60, 3201), (61, 3255), (62, 3207), (63, 1477), (80, 1366), (81, 1596), (82, 1613), (83, 1675), (84, 1613), (85, 2695),
    (86, 3205), (87, 3287), (88, 3227), (89, 3251), (90, 3206), (91, 3237), (92, 3190), (93, 3220), (94, 3297), (95, 3159),
    (96, 3283), (97, 3194), (98, 1828), (99, 1576), (100, 1619), (101, 1584), (102, 1636), (103, 127), (168, 1506), (169, 2477),
    (170, 3467), (171, 4445), (172, 4277), (173, 4272), (174, 4313), (175, 4305), (176, 4304), (177, 4191), (178, 4221), (179, 4187),
    (180, 4209), (181, 4304), (182, 4141), (183, 4293), (184, 4261), (185, 4233), (186, 4220), (187, 4202), (188, 4021), (189, 1775),
    (190, 902)
  ]

theorem fc2kSubCert4_0_valid : checkPrefixSubCert fc2kSubCert4_0 = true := by
  decide +kernel

private noncomputable def fc2kSubProf4_0 : VerifiedSubCertProfile fc2kSubCert4_0 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert4_0 fc2kSubCert4_0_valid)

/-- Sub-certificate 1/3 for FC2K certificate 4 (`13` active super-chunks). -/
def fc2kSubCert4_1 : PrefixSubCert where
  corrLo := 39186893
  numSuperChunks := 29
  activeChunkMask := 0x1f1fe000
  numChunks := 5
  qSub := 28842
  maxHi := 208957903
  chunks := [
    (15, { startWord := 832, endWord := 980, endBitCutoff := 1762, subMod := 1 }),
    (14, { startWord := 984, endWord := 1132, endBitCutoff := 7428, subMod := 1 }),
    (13, { startWord := 1136, endWord := 1287, endBitCutoff := 3024, subMod := 1 }),
    (12, { startWord := 1536, endWord := 1690, endBitCutoff := 6044, subMod := 1 }),
    (11, { startWord := 1688, endWord := 1842, endBitCutoff := 5419, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (104, 2900), (105, 3180), (106, 3187), (107, 3116), (108, 3111), (109, 2982), (110, 3164), (111, 3097), (112, 3071), (113, 3192),
    (114, 3019), (115, 3134), (116, 3113), (117, 3261), (118, 3207), (119, 3098), (120, 3013), (121, 3015), (122, 1824), (123, 3011),
    (124, 3223), (125, 3188), (126, 3189), (127, 3066), (128, 3043), (129, 3217), (130, 3062), (131, 2974), (132, 2971), (133, 3104),
    (134, 3149), (135, 3078), (136, 3054), (137, 3044), (138, 3020), (139, 3057), (140, 3115), (141, 2119), (142, 3032), (143, 3067),
    (144, 3084), (145, 3011), (146, 3111), (147, 2986), (148, 3084), (149, 2930), (150, 3122), (151, 2957), (152, 3063), (153, 3087),
    (154, 3122), (155, 2970), (156, 3044), (157, 2993), (158, 3043), (159, 3032), (160, 2946), (192, 2929), (193, 2968), (194, 3001),
    (195, 3051), (196, 2877), (197, 3009), (198, 3004), (199, 2947), (200, 3028), (201, 2991), (202, 2773), (203, 3029), (204, 3054),
    (205, 3093), (206, 3086), (207, 2923), (208, 2954), (209, 2952), (210, 3004), (211, 3772), (212, 3093), (213, 3012), (214, 2973),
    (215, 2978), (216, 3026), (217, 3069), (218, 2961), (219, 3010), (220, 2923), (221, 2954), (222, 2975), (223, 3041), (224, 3037),
    (225, 2942), (226, 2919), (227, 3061), (228, 3005), (229, 2994), (230, 950)
  ]

theorem fc2kSubCert4_1_valid : checkPrefixSubCert fc2kSubCert4_1 = true := by
  decide +kernel

private noncomputable def fc2kSubProf4_1 : VerifiedSubCertProfile fc2kSubCert4_1 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert4_1 fc2kSubCert4_1_valid)

/-- Sub-certificate 2/3 for FC2K certificate 4 (`15` active super-chunks). -/
def fc2kSubCert4_2 : PrefixSubCert where
  corrLo := 39186893
  numSuperChunks := 44
  activeChunkMask := 0xfffe0000000
  numChunks := 6
  qSub := 28842
  maxHi := 208957903
  chunks := [
    (9, { startWord := 1856, endWord := 2012, endBitCutoff := 5035, subMod := 1 }),
    (8, { startWord := 2012, endWord := 2168, endBitCutoff := 7813, subMod := 1 }),
    (7, { startWord := 2184, endWord := 2340, endBitCutoff := 8168, subMod := 1 }),
    (6, { startWord := 2340, endWord := 2499, endBitCutoff := 3063, subMod := 1 }),
    (5, { startWord := 2496, endWord := 2654, endBitCutoff := 6681, subMod := 1 }),
    (4, { startWord := 2652, endWord := 2812, endBitCutoff := 3886, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (232, 2891), (233, 3062), (234, 2929), (235, 2979), (236, 2920), (237, 2950), (238, 3019), (239, 3038), (240, 3010), (241, 2924),
    (242, 2950), (243, 2873), (244, 2913), (245, 2810), (246, 2950), (247, 3060), (248, 2935), (249, 2949), (250, 2794), (251, 3155),
    (252, 2868), (253, 2995), (254, 2901), (255, 2862), (256, 2886), (257, 3005), (258, 2994), (259, 2888), (260, 2971), (261, 2979),
    (262, 3043), (263, 2933), (264, 2999), (265, 2975), (266, 2909), (267, 2972), (268, 2839), (269, 2990), (270, 2926), (271, 322),
    (273, 2948), (274, 2960), (275, 2987), (276, 3007), (277, 2978), (278, 2927), (279, 2919), (280, 2928), (281, 2901), (282, 2955),
    (283, 2952), (284, 2963), (285, 2943), (286, 2865), (287, 2897), (288, 2919), (289, 2924), (290, 2908), (291, 2986), (292, 3243),
    (293, 2870), (294, 2870), (295, 2870), (296, 2910), (297, 2944), (298, 2942), (299, 2858), (300, 2986), (301, 2884), (302, 2886),
    (303, 2956), (304, 2972), (305, 2828), (306, 2876), (307, 2901), (308, 2954), (309, 2894), (310, 2782), (311, 2885), (312, 3885),
    (313, 2977), (314, 2940), (315, 2980), (316, 2904), (317, 2795), (318, 2851), (319, 2858), (320, 2891), (321, 2910), (322, 2850),
    (323, 3010), (324, 2848), (325, 2917), (326, 2932), (327, 2961), (328, 2969), (329, 2860), (330, 2956), (331, 3762), (332, 2864),
    (333, 2796), (334, 2824), (335, 2976), (336, 2874), (337, 2900), (338, 2770), (339, 2978), (340, 2934), (341, 2904), (342, 2884),
    (343, 2961), (344, 2803), (345, 2934), (346, 2986), (347, 2934), (348, 2942), (349, 2838), (350, 2856), (351, 1544)
  ]

theorem fc2kSubCert4_2_valid : checkPrefixSubCert fc2kSubCert4_2 = true := by
  decide +kernel

private noncomputable def fc2kSubProf4_2 : VerifiedSubCertProfile fc2kSubCert4_2 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert4_2 fc2kSubCert4_2_valid)

/-- Sub-certificate 3/3 for FC2K certificate 4 (`10` active super-chunks). -/
def fc2kSubCert4_3 : PrefixSubCert where
  corrLo := 39186893
  numSuperChunks := 54
  activeChunkMask := 0x3ff00000000000
  numChunks := 4
  qSub := 28842
  maxHi := 208957903
  chunks := [
    (3, { startWord := 2816, endWord := 2975, endBitCutoff := 7148, subMod := 1 }),
    (2, { startWord := 2968, endWord := 3130, endBitCutoff := 6697, subMod := 1 }),
    (1, { startWord := 3136, endWord := 3297, endBitCutoff := 7190, subMod := 1 }),
    (0, { startWord := 3288, endWord := 3453, endBitCutoff := 2589, subMod := 1 })
  ]
  windowCaps := []
  octCounts := [
    (352, 2862), (353, 2842), (354, 2816), (355, 2980), (356, 2810), (357, 2972), (358, 2826), (359, 2870), (360, 2902), (361, 2808),
    (362, 2860), (363, 2774), (364, 2900), (365, 2918), (366, 3009), (367, 2801), (368, 2948), (369, 3005), (370, 2895), (371, 5198),
    (372, 2840), (373, 2914), (374, 2828), (375, 2858), (376, 2896), (377, 2910), (378, 2836), (379, 2874), (380, 2816), (381, 2902),
    (382, 2834), (383, 2938), (384, 2886), (385, 2874), (386, 2766), (387, 2828), (388, 2732), (389, 2946), (390, 2844), (391, 1050),
    (392, 2814), (393, 2866), (394, 2762), (395, 2886), (396, 2922), (397, 2792), (398, 2962), (399, 2936), (400, 2862), (401, 2760),
    (402, 2807), (403, 2841), (404, 2776), (405, 2990), (406, 2814), (407, 2856), (408, 2791), (409, 2793), (410, 2932), (411, 5170),
    (412, 3328), (413, 2784), (414, 2756), (415, 2706), (416, 2882), (417, 2816), (418, 2806), (419, 2848), (420, 2930), (421, 2940),
    (422, 2672), (423, 2822), (424, 2826), (425, 2818), (426, 2842), (427, 2772), (428, 2934), (429, 2790), (430, 2832), (431, 1932)
  ]

theorem fc2kSubCert4_3_valid : checkPrefixSubCert fc2kSubCert4_3 = true := by
  decide +kernel

private noncomputable def fc2kSubProf4_3 : VerifiedSubCertProfile fc2kSubCert4_3 :=
  Classical.choice (checkPrefixSubCert_sound fc2kSubCert4_3 fc2kSubCert4_3_valid)

def fc2kSubCerts4 : List PrefixSubCert := [fc2kSubCert4_0, fc2kSubCert4_1, fc2kSubCert4_2, fc2kSubCert4_3]

def fc2kPlan4 : MultiSubCertPlan where
  P := 26
  M := 1
  qSub := 28842
  qCert := 28842
  corrLo := 39186893
  maxHi := 208957903
  numOcts := 450
  routes := [
    [(3, 3)],
    [(3, 2)],
    [(3, 1)],
    [(3, 0)],
    [(2, 5)],
    [(2, 4)],
    [(2, 3)],
    [(2, 2)],
    [(2, 1)],
    [(2, 0)],
    [(0, 10)],
    [(1, 4)],
    [(1, 3)],
    [(1, 2)],
    [(1, 1)],
    [(1, 0)],
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
    { minWordIdx := 59, spanWords := 12, cap := 51169 },
    { minWordIdx := 59, spanWords := 15, cap := 63956 },
    { minWordIdx := 107, spanWords := 19, cap := 79866 },
    { minWordIdx := 144, spanWords := 12, cap := 51169 },
    { minWordIdx := 173, spanWords := 16, cap := 67677 },
    { minWordIdx := 173, spanWords := 60, cap := 188613 },
    { minWordIdx := 257, spanWords := 21, cap := 63006 },
    { minWordIdx := 257, spanWords := 79, cap := 231636 },
    { minWordIdx := 363, spanWords := 15, cap := 45756 },
    { minWordIdx := 366, spanWords := 12, cap := 37102 },
    { minWordIdx := 475, spanWords := 12, cap := 0 },
    { minWordIdx := 505, spanWords := 19, cap := 0 }
  ]

theorem fc2kPlan4_valid : checkMultiSubCertPlan fc2kSubCerts4 fc2kPlan4 = true := by
  decide +kernel

private noncomputable def fc2kSubProfs4 :
    ∀ g : Fin fc2kSubCerts4.length,
      VerifiedSubCertProfile (fc2kSubCerts4[g.val]'g.isLt)
  | ⟨0, _⟩ => fc2kSubProf4_0
  | ⟨1, _⟩ => fc2kSubProf4_1
  | ⟨2, _⟩ => fc2kSubProf4_2
  | ⟨3, _⟩ => fc2kSubProf4_3
  | ⟨k + 4, h⟩ => False.elim (by change k + 4 < 4 at h; omega)

/-- Assembled `GeneralPrefixProfile` for FC2K certificate 4. -/
noncomputable def fc2kPrefixProfile4 :
    GeneralPrefixProfile 26 28842 39186893 208957903 :=
  assembleGeneralPrefixProfile fc2kSubCerts4 fc2kPlan4 fc2kPlan4_valid fc2kSubProfs4

end Sude
