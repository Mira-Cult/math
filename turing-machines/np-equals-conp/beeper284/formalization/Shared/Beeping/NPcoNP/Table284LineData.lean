import Shared.Beeping.NPcoNP.Table284Data

/-! Generated candidate lines and row pairs. Lean checks the pair
identity below; the input-file-to-lines identity is separate. -/
namespace Shared.Beeping.NPcoNP.Table284LineData
open Shared.Beeping.TableBits
set_option maxRecDepth 8192

def lines00 : List (List Char) := [
  "0 0 1 R 2 0".toList,
  "0 1 1 L 3 0".toList,
  "1 0 1 R 27 0".toList,
  "1 1 0 L 1 0".toList,
  "2 0 0 L 0 0".toList,
  "2 1 0 L 4 0".toList,
  "3 0 1 L 0 0".toList,
  "3 1 1 R 261 0".toList,
  "4 0 1 L 2 0".toList,
  "4 1 1 R 5 0".toList,
  "5 0 0 R 4 0".toList,
  "5 1 0 R 2 0".toList,
  "6 0 1 L 97 0".toList,
  "6 1 1 R 7 0".toList,
  "7 0 0 R 6 0".toList,
  "7 1 1 R 8 0".toList,
  "8 0 0 R 261 0".toList,
  "8 1 1 R 260 0".toList,
  "9 0 0 R 42 0".toList,
  "9 1 1 R 9 0".toList
]
def pairs00 : List RawPair := [
  ((true, (true, (2, false))), (true, (false, (3, false)))),
  ((true, (true, (27, false))), (false, (false, (1, false)))),
  ((false, (false, (0, false))), (false, (false, (4, false)))),
  ((true, (false, (0, false))), (true, (true, (261, false)))),
  ((true, (false, (2, false))), (true, (true, (5, false)))),
  ((false, (true, (4, false))), (false, (true, (2, false)))),
  ((true, (false, (97, false))), (true, (true, (7, false)))),
  ((false, (true, (6, false))), (true, (true, (8, false)))),
  ((false, (true, (261, false))), (true, (true, (260, false)))),
  ((false, (true, (42, false))), (true, (true, (9, false))))
]

def lines01 : List (List Char) := [
  "10 0 1 R 10 0".toList,
  "10 1 1 L 97 0".toList,
  "11 0 0 R 13 0".toList,
  "11 1 1 R 11 0".toList,
  "12 0 0 R 14 0".toList,
  "12 1 1 R 12 0".toList,
  "13 0 1 L 25 0".toList,
  "13 1 0 R 17 0".toList,
  "14 0 1 R 22 0".toList,
  "14 1 1 R 14 0".toList,
  "15 0 0 R 11 0".toList,
  "15 1 1 R 15 0".toList,
  "16 0 0 R 12 0".toList,
  "16 1 1 R 16 0".toList,
  "17 0 0 L 13 0".toList,
  "17 1 1 R 18 0".toList,
  "18 0 0 R 19 0".toList,
  "18 1 1 R 18 0".toList,
  "19 0 0 L 20 0".toList,
  "19 1 1 R 18 0".toList
]
def pairs01 : List RawPair := [
  ((true, (true, (10, false))), (true, (false, (97, false)))),
  ((false, (true, (13, false))), (true, (true, (11, false)))),
  ((false, (true, (14, false))), (true, (true, (12, false)))),
  ((true, (false, (25, false))), (false, (true, (17, false)))),
  ((true, (true, (22, false))), (true, (true, (14, false)))),
  ((false, (true, (11, false))), (true, (true, (15, false)))),
  ((false, (true, (12, false))), (true, (true, (16, false)))),
  ((false, (false, (13, false))), (true, (true, (18, false)))),
  ((false, (true, (19, false))), (true, (true, (18, false)))),
  ((false, (false, (20, false))), (true, (true, (18, false))))
]

def lines02 : List (List Char) := [
  "20 0 1 L 21 0".toList,
  "20 1 1 L 20 0".toList,
  "21 0 0 L 23 0".toList,
  "21 1 0 L 20 0".toList,
  "22 0 0 L 23 0".toList,
  "22 1 0 R 14 0".toList,
  "23 0 0 L 24 0".toList,
  "23 1 1 L 23 0".toList,
  "24 0 0 L 1 0".toList,
  "24 1 1 L 23 0".toList,
  "25 0 0 L 26 0".toList,
  "25 1 1 L 25 0".toList,
  "26 0 0 L 95 0".toList,
  "26 1 1 L 25 0".toList,
  "27 0 0 R 27 0".toList,
  "27 1 0 R 28 0".toList,
  "28 0 0 L 6 0".toList,
  "28 1 0 R 28 0".toList,
  "29 0 1 R 265 0".toList,
  "29 1 1 R 41 0".toList
]
def pairs02 : List RawPair := [
  ((true, (false, (21, false))), (true, (false, (20, false)))),
  ((false, (false, (23, false))), (false, (false, (20, false)))),
  ((false, (false, (23, false))), (false, (true, (14, false)))),
  ((false, (false, (24, false))), (true, (false, (23, false)))),
  ((false, (false, (1, false))), (true, (false, (23, false)))),
  ((false, (false, (26, false))), (true, (false, (25, false)))),
  ((false, (false, (95, false))), (true, (false, (25, false)))),
  ((false, (true, (27, false))), (false, (true, (28, false)))),
  ((false, (false, (6, false))), (false, (true, (28, false)))),
  ((true, (true, (265, false))), (true, (true, (41, false))))
]

def lines03 : List (List Char) := [
  "30 0 1 R 40 0".toList,
  "30 1 1 R 30 0".toList,
  "31 0 0 R 18 0".toList,
  "31 1 1 R 30 0".toList,
  "32 0 0 R 33 0".toList,
  "32 1 1 R 32 0".toList,
  "33 0 0 L 34 0".toList,
  "33 1 1 R 32 0".toList,
  "34 0 1 L 35 0".toList,
  "34 1 1 L 34 0".toList,
  "35 0 0 L 31 0".toList,
  "35 1 0 L 34 0".toList,
  "36 0 0 R 37 0".toList,
  "36 1 1 R 36 0".toList,
  "37 0 0 L 38 0".toList,
  "37 1 1 R 36 0".toList,
  "38 0 1 L 39 0".toList,
  "38 1 1 L 38 0".toList,
  "39 0 0 L 25 0".toList,
  "39 1 0 L 38 0".toList
]
def pairs03 : List RawPair := [
  ((true, (true, (40, false))), (true, (true, (30, false)))),
  ((false, (true, (18, false))), (true, (true, (30, false)))),
  ((false, (true, (33, false))), (true, (true, (32, false)))),
  ((false, (false, (34, false))), (true, (true, (32, false)))),
  ((true, (false, (35, false))), (true, (false, (34, false)))),
  ((false, (false, (31, false))), (false, (false, (34, false)))),
  ((false, (true, (37, false))), (true, (true, (36, false)))),
  ((false, (false, (38, false))), (true, (true, (36, false)))),
  ((true, (false, (39, false))), (true, (false, (38, false)))),
  ((false, (false, (25, false))), (false, (false, (38, false))))
]

def lines04 : List (List Char) := [
  "40 0 0 L 49 0".toList,
  "40 1 0 R 43 0".toList,
  "41 0 0 L 25 0".toList,
  "41 1 1 R 40 0".toList,
  "42 0 0 R 10 0".toList,
  "42 1 0 L 283 0".toList,
  "43 0 0 R 37 0".toList,
  "43 1 0 R 32 0".toList,
  "44 0 0 R 29 0".toList,
  "44 1 1 R 44 0".toList,
  "45 0 0 R 44 0".toList,
  "45 1 1 R 45 0".toList,
  "46 0 0 R 45 0".toList,
  "46 1 1 R 46 0".toList,
  "47 0 0 R 46 0".toList,
  "47 1 1 R 47 0".toList,
  "48 0 0 R 47 0".toList,
  "48 1 1 R 48 0".toList,
  "49 0 0 R 267 0".toList,
  "49 1 0 R 18 0".toList
]
def pairs04 : List RawPair := [
  ((false, (false, (49, false))), (false, (true, (43, false)))),
  ((false, (false, (25, false))), (true, (true, (40, false)))),
  ((false, (true, (10, false))), (false, (false, (283, false)))),
  ((false, (true, (37, false))), (false, (true, (32, false)))),
  ((false, (true, (29, false))), (true, (true, (44, false)))),
  ((false, (true, (44, false))), (true, (true, (45, false)))),
  ((false, (true, (45, false))), (true, (true, (46, false)))),
  ((false, (true, (46, false))), (true, (true, (47, false)))),
  ((false, (true, (47, false))), (true, (true, (48, false)))),
  ((false, (true, (267, false))), (false, (true, (18, false))))
]

def lines05 : List (List Char) := [
  "50 0 1 R 9 0".toList,
  "50 1 1 R 275 0".toList,
  "51 0 1 R 9 0".toList,
  "51 1 0 R 275 0".toList,
  "52 0 1 R 9 0".toList,
  "52 1 1 R 276 0".toList,
  "53 0 1 R 9 0".toList,
  "53 1 0 R 276 0".toList,
  "54 0 1 R 9 0".toList,
  "54 1 1 R 273 0".toList,
  "55 0 1 R 9 0".toList,
  "55 1 0 R 273 0".toList,
  "56 0 1 R 9 0".toList,
  "56 1 1 R 274 0".toList,
  "57 0 1 R 9 0".toList,
  "57 1 0 R 274 0".toList,
  "58 0 1 R 9 0".toList,
  "58 1 1 R 277 0".toList,
  "59 0 1 R 9 0".toList,
  "59 1 0 R 277 0".toList
]
def pairs05 : List RawPair := [
  ((true, (true, (9, false))), (true, (true, (275, false)))),
  ((true, (true, (9, false))), (false, (true, (275, false)))),
  ((true, (true, (9, false))), (true, (true, (276, false)))),
  ((true, (true, (9, false))), (false, (true, (276, false)))),
  ((true, (true, (9, false))), (true, (true, (273, false)))),
  ((true, (true, (9, false))), (false, (true, (273, false)))),
  ((true, (true, (9, false))), (true, (true, (274, false)))),
  ((true, (true, (9, false))), (false, (true, (274, false)))),
  ((true, (true, (9, false))), (true, (true, (277, false)))),
  ((true, (true, (9, false))), (false, (true, (277, false))))
]

def lines06 : List (List Char) := [
  "60 0 1 R 9 0".toList,
  "60 1 1 R 278 0".toList,
  "61 0 1 R 9 0".toList,
  "61 1 0 R 278 0".toList,
  "62 0 1 R 9 0".toList,
  "62 1 1 R 279 0".toList,
  "63 0 1 R 9 0".toList,
  "63 1 0 R 279 0".toList,
  "64 0 1 R 9 0".toList,
  "64 1 1 R 280 0".toList,
  "65 0 1 R 9 0".toList,
  "65 1 0 R 280 0".toList,
  "66 0 1 R 9 0".toList,
  "66 1 1 R 281 0".toList,
  "67 0 1 R 9 0".toList,
  "67 1 0 R 281 0".toList,
  "68 0 1 R 9 0".toList,
  "68 1 1 R 282 0".toList,
  "69 0 1 R 9 0".toList,
  "69 1 0 R 282 0".toList
]
def pairs06 : List RawPair := [
  ((true, (true, (9, false))), (true, (true, (278, false)))),
  ((true, (true, (9, false))), (false, (true, (278, false)))),
  ((true, (true, (9, false))), (true, (true, (279, false)))),
  ((true, (true, (9, false))), (false, (true, (279, false)))),
  ((true, (true, (9, false))), (true, (true, (280, false)))),
  ((true, (true, (9, false))), (false, (true, (280, false)))),
  ((true, (true, (9, false))), (true, (true, (281, false)))),
  ((true, (true, (9, false))), (false, (true, (281, false)))),
  ((true, (true, (9, false))), (true, (true, (282, false)))),
  ((true, (true, (9, false))), (false, (true, (282, false))))
]

def lines07 : List (List Char) := [
  "70 0 1 R 9 0".toList,
  "70 1 1 R 272 0".toList,
  "71 0 1 R 9 0".toList,
  "71 1 0 R 272 0".toList,
  "72 0 1 R 9 0".toList,
  "72 1 1 R 271 0".toList,
  "73 0 1 R 9 0".toList,
  "73 1 0 R 271 0".toList,
  "74 0 1 R 42 0".toList,
  "74 1 0 R 46 0".toList,
  "75 0 1 R 42 0".toList,
  "75 1 0 R 47 0".toList,
  "76 0 1 R 42 0".toList,
  "76 1 0 R 48 0".toList,
  "77 0 1 R 42 0".toList,
  "77 1 0 R 45 0".toList,
  "78 0 0 L 92 0".toList,
  "78 1 1 L 78 0".toList,
  "79 0 0 L 78 0".toList,
  "79 1 1 L 79 0".toList
]
def pairs07 : List RawPair := [
  ((true, (true, (9, false))), (true, (true, (272, false)))),
  ((true, (true, (9, false))), (false, (true, (272, false)))),
  ((true, (true, (9, false))), (true, (true, (271, false)))),
  ((true, (true, (9, false))), (false, (true, (271, false)))),
  ((true, (true, (42, false))), (false, (true, (46, false)))),
  ((true, (true, (42, false))), (false, (true, (47, false)))),
  ((true, (true, (42, false))), (false, (true, (48, false)))),
  ((true, (true, (42, false))), (false, (true, (45, false)))),
  ((false, (false, (92, false))), (true, (false, (78, false)))),
  ((false, (false, (78, false))), (true, (false, (79, false))))
]

def lines08 : List (List Char) := [
  "80 0 0 L 91 0".toList,
  "80 1 1 L 80 0".toList,
  "81 0 0 L 80 0".toList,
  "81 1 1 L 81 0".toList,
  "82 0 0 L 81 0".toList,
  "82 1 1 L 82 0".toList,
  "83 0 0 L 82 0".toList,
  "83 1 1 L 83 0".toList,
  "84 0 0 L 79 0".toList,
  "84 1 1 L 84 0".toList,
  "85 0 0 L 84 0".toList,
  "85 1 1 L 85 0".toList,
  "86 0 0 L 85 0".toList,
  "86 1 1 L 86 0".toList,
  "87 0 0 L 86 0".toList,
  "87 1 1 L 87 0".toList,
  "88 0 0 L 87 0".toList,
  "88 1 1 L 88 0".toList,
  "89 0 0 L 88 0".toList,
  "89 1 1 L 89 0".toList
]
def pairs08 : List RawPair := [
  ((false, (false, (91, false))), (true, (false, (80, false)))),
  ((false, (false, (80, false))), (true, (false, (81, false)))),
  ((false, (false, (81, false))), (true, (false, (82, false)))),
  ((false, (false, (82, false))), (true, (false, (83, false)))),
  ((false, (false, (79, false))), (true, (false, (84, false)))),
  ((false, (false, (84, false))), (true, (false, (85, false)))),
  ((false, (false, (85, false))), (true, (false, (86, false)))),
  ((false, (false, (86, false))), (true, (false, (87, false)))),
  ((false, (false, (87, false))), (true, (false, (88, false)))),
  ((false, (false, (88, false))), (true, (false, (89, false))))
]

def lines09 : List (List Char) := [
  "90 0 0 L 89 0".toList,
  "90 1 1 L 90 0".toList,
  "91 0 0 L 90 0".toList,
  "91 1 1 L 91 0".toList,
  "92 0 0 R 92 0".toList,
  "92 1 1 R 93 0".toList,
  "93 0 0 R 6 0".toList,
  "93 1 1 R 94 0".toList,
  "94 0 0 R 259 0".toList,
  "94 1 0 R 259 0".toList,
  "95 0 0 L 1 0".toList,
  "95 1 0 L 95 0".toList,
  "96 0 0 L 95 0".toList,
  "96 1 0 L 96 0".toList,
  "97 0 0 L 97 0".toList,
  "97 1 1 L 83 0".toList,
  "98 0 0 L 98 0".toList,
  "98 1 0 L 97 0".toList,
  "99 0 1 R 9 0".toList,
  "99 1 0 L 1 1".toList
]
def pairs09 : List RawPair := [
  ((false, (false, (89, false))), (true, (false, (90, false)))),
  ((false, (false, (90, false))), (true, (false, (91, false)))),
  ((false, (true, (92, false))), (true, (true, (93, false)))),
  ((false, (true, (6, false))), (true, (true, (94, false)))),
  ((false, (true, (259, false))), (false, (true, (259, false)))),
  ((false, (false, (1, false))), (false, (false, (95, false)))),
  ((false, (false, (95, false))), (false, (false, (96, false)))),
  ((false, (false, (97, false))), (true, (false, (83, false)))),
  ((false, (false, (98, false))), (false, (false, (97, false)))),
  ((true, (true, (9, false))), (false, (false, (1, true))))
]

def lines10 : List (List Char) := [
  "100 0 0 R 62 0".toList,
  "100 1 0 L 97 0".toList,
  "101 0 0 R 55 0".toList,
  "101 1 1 R 73 0".toList,
  "102 0 0 R 64 0".toList,
  "102 1 0 L 97 0".toList,
  "103 0 0 R 57 0".toList,
  "103 1 1 R 258 0".toList,
  "104 0 0 R 103 0".toList,
  "104 1 0 L 98 0".toList,
  "105 0 0 R 60 0".toList,
  "105 1 1 R 104 0".toList,
  "106 0 0 R 61 0".toList,
  "106 1 0 L 98 0".toList,
  "107 0 0 R 56 0".toList,
  "107 1 1 R 106 0".toList,
  "108 0 0 R 68 0".toList,
  "108 1 1 R 146 0".toList,
  "109 0 0 R 108 0".toList,
  "109 1 1 R 181 0".toList
]
def pairs10 : List RawPair := [
  ((false, (true, (62, false))), (false, (false, (97, false)))),
  ((false, (true, (55, false))), (true, (true, (73, false)))),
  ((false, (true, (64, false))), (false, (false, (97, false)))),
  ((false, (true, (57, false))), (true, (true, (258, false)))),
  ((false, (true, (103, false))), (false, (false, (98, false)))),
  ((false, (true, (60, false))), (true, (true, (104, false)))),
  ((false, (true, (61, false))), (false, (false, (98, false)))),
  ((false, (true, (56, false))), (true, (true, (106, false)))),
  ((false, (true, (68, false))), (true, (true, (146, false)))),
  ((false, (true, (108, false))), (true, (true, (181, false))))
]

def lines11 : List (List Char) := [
  "110 0 0 R 57 0".toList,
  "110 1 1 R 109 0".toList,
  "111 0 0 R 110 0".toList,
  "111 1 0 L 98 0".toList,
  "112 0 0 R 66 0".toList,
  "112 1 1 R 111 0".toList,
  "113 0 0 R 66 0".toList,
  "113 1 0 L 97 0".toList,
  "114 0 0 R 56 0".toList,
  "114 1 1 R 167 0".toList,
  "115 0 0 R 60 0".toList,
  "115 1 1 R 171 0".toList,
  "116 0 0 R 72 0".toList,
  "116 1 1 R 106 0".toList,
  "117 0 0 R 116 0".toList,
  "117 1 1 R 233 0".toList,
  "118 0 0 R 115 0".toList,
  "118 1 1 R 117 0".toList,
  "119 0 0 R 201 0".toList,
  "119 1 1 R 118 0".toList
]
def pairs11 : List RawPair := [
  ((false, (true, (57, false))), (true, (true, (109, false)))),
  ((false, (true, (110, false))), (false, (false, (98, false)))),
  ((false, (true, (66, false))), (true, (true, (111, false)))),
  ((false, (true, (66, false))), (false, (false, (97, false)))),
  ((false, (true, (56, false))), (true, (true, (167, false)))),
  ((false, (true, (60, false))), (true, (true, (171, false)))),
  ((false, (true, (72, false))), (true, (true, (106, false)))),
  ((false, (true, (116, false))), (true, (true, (233, false)))),
  ((false, (true, (115, false))), (true, (true, (117, false)))),
  ((false, (true, (201, false))), (true, (true, (118, false))))
]

def lines12 : List (List Char) := [
  "120 0 0 R 58 0".toList,
  "120 1 1 R 119 0".toList,
  "121 0 0 R 120 0".toList,
  "121 1 0 L 98 0".toList,
  "122 0 0 R 56 0".toList,
  "122 1 1 R 121 0".toList,
  "123 0 0 R 50 0".toList,
  "123 1 0 L 95 0".toList,
  "124 0 0 R 113 0".toList,
  "124 1 1 R 67 0".toList,
  "125 0 0 R 226 0".toList,
  "125 1 1 R 51 0".toList,
  "126 0 0 R 123 0".toList,
  "126 1 1 R 125 0".toList,
  "127 0 0 R 126 0".toList,
  "127 1 0 L 95 0".toList,
  "128 0 0 R 241 0".toList,
  "128 1 1 R 127 0".toList,
  "129 0 0 R 122 0".toList,
  "129 1 1 R 128 0".toList
]
def pairs12 : List RawPair := [
  ((false, (true, (58, false))), (true, (true, (119, false)))),
  ((false, (true, (120, false))), (false, (false, (98, false)))),
  ((false, (true, (56, false))), (true, (true, (121, false)))),
  ((false, (true, (50, false))), (false, (false, (95, false)))),
  ((false, (true, (113, false))), (true, (true, (67, false)))),
  ((false, (true, (226, false))), (true, (true, (51, false)))),
  ((false, (true, (123, false))), (true, (true, (125, false)))),
  ((false, (true, (126, false))), (false, (false, (95, false)))),
  ((false, (true, (241, false))), (true, (true, (127, false)))),
  ((false, (true, (122, false))), (true, (true, (128, false))))
]

def lines13 : List (List Char) := [
  "130 0 0 R 200 0".toList,
  "130 1 1 R 129 0".toList,
  "131 0 0 R 178 0".toList,
  "131 1 1 R 130 0".toList,
  "132 0 0 R 194 0".toList,
  "132 1 1 R 131 0".toList,
  "133 0 0 R 217 0".toList,
  "133 1 1 R 132 0".toList,
  "134 0 0 R 191 0".toList,
  "134 1 1 R 133 0".toList,
  "135 0 0 R 55 0".toList,
  "135 1 1 R 55 0".toList,
  "136 0 0 R 215 0".toList,
  "136 1 1 R 134 0".toList,
  "137 0 0 R 190 0".toList,
  "137 1 1 R 136 0".toList,
  "138 0 0 R 137 0".toList,
  "138 1 0 L 98 0".toList,
  "139 0 0 R 68 0".toList,
  "139 1 1 R 138 0".toList
]
def pairs13 : List RawPair := [
  ((false, (true, (200, false))), (true, (true, (129, false)))),
  ((false, (true, (178, false))), (true, (true, (130, false)))),
  ((false, (true, (194, false))), (true, (true, (131, false)))),
  ((false, (true, (217, false))), (true, (true, (132, false)))),
  ((false, (true, (191, false))), (true, (true, (133, false)))),
  ((false, (true, (55, false))), (true, (true, (55, false)))),
  ((false, (true, (215, false))), (true, (true, (134, false)))),
  ((false, (true, (190, false))), (true, (true, (136, false)))),
  ((false, (true, (137, false))), (false, (false, (98, false)))),
  ((false, (true, (68, false))), (true, (true, (138, false))))
]

def lines14 : List (List Char) := [
  "140 0 0 R 50 0".toList,
  "140 1 1 R 242 0".toList,
  "141 0 0 R 140 0".toList,
  "141 1 0 L 96 0".toList,
  "142 0 0 R 141 0".toList,
  "142 1 1 R 63 0".toList,
  "143 0 0 R 139 0".toList,
  "143 1 1 R 142 0".toList,
  "144 0 0 R 114 0".toList,
  "144 1 1 R 143 0".toList,
  "145 0 0 R 112 0".toList,
  "145 1 1 R 144 0".toList,
  "146 0 0 R 135 0".toList,
  "146 1 0 L 98 0".toList,
  "147 0 0 R 69 0".toList,
  "147 1 1 R 145 0".toList,
  "148 0 0 R 179 0".toList,
  "148 1 1 R 147 0".toList,
  "149 0 0 R 107 0".toList,
  "149 1 1 R 148 0".toList
]
def pairs14 : List RawPair := [
  ((false, (true, (50, false))), (true, (true, (242, false)))),
  ((false, (true, (140, false))), (false, (false, (96, false)))),
  ((false, (true, (141, false))), (true, (true, (63, false)))),
  ((false, (true, (139, false))), (true, (true, (142, false)))),
  ((false, (true, (114, false))), (true, (true, (143, false)))),
  ((false, (true, (112, false))), (true, (true, (144, false)))),
  ((false, (true, (135, false))), (false, (false, (98, false)))),
  ((false, (true, (69, false))), (true, (true, (145, false)))),
  ((false, (true, (179, false))), (true, (true, (147, false)))),
  ((false, (true, (107, false))), (true, (true, (148, false))))
]

def lines15 : List (List Char) := [
  "150 0 0 R 105 0".toList,
  "150 1 1 R 149 0".toList,
  "151 0 0 R 124 0".toList,
  "151 1 1 R 150 0".toList,
  "152 0 0 R 253 0".toList,
  "152 1 1 R 151 0".toList,
  "153 0 0 R 181 0".toList,
  "153 1 1 R 152 0".toList,
  "154 0 0 R 179 0".toList,
  "154 1 1 R 153 0".toList,
  "155 0 0 R 178 0".toList,
  "155 1 1 R 154 0".toList,
  "156 0 0 R 226 0".toList,
  "156 1 1 R 155 0".toList,
  "157 0 0 R 66 0".toList,
  "157 1 1 R 146 0".toList,
  "158 0 0 R 175 0".toList,
  "158 1 1 R 156 0".toList,
  "159 0 0 R 124 0".toList,
  "159 1 1 R 158 0".toList
]
def pairs15 : List RawPair := [
  ((false, (true, (105, false))), (true, (true, (149, false)))),
  ((false, (true, (124, false))), (true, (true, (150, false)))),
  ((false, (true, (253, false))), (true, (true, (151, false)))),
  ((false, (true, (181, false))), (true, (true, (152, false)))),
  ((false, (true, (179, false))), (true, (true, (153, false)))),
  ((false, (true, (178, false))), (true, (true, (154, false)))),
  ((false, (true, (226, false))), (true, (true, (155, false)))),
  ((false, (true, (66, false))), (true, (true, (146, false)))),
  ((false, (true, (175, false))), (true, (true, (156, false)))),
  ((false, (true, (124, false))), (true, (true, (158, false))))
]

def lines16 : List (List Char) := [
  "160 0 0 R 102 0".toList,
  "160 1 1 R 159 0".toList,
  "161 0 0 R 248 0".toList,
  "161 1 1 R 160 0".toList,
  "162 0 0 R 226 0".toList,
  "162 1 1 R 161 0".toList,
  "163 0 0 R 215 0".toList,
  "163 1 1 R 162 0".toList,
  "164 0 0 R 163 0".toList,
  "164 1 0 L 97 0".toList,
  "165 0 0 R 164 0".toList,
  "165 1 1 R 61 0".toList,
  "166 0 0 R 100 0".toList,
  "166 1 1 R 165 0".toList,
  "167 0 0 R 67 0".toList,
  "167 1 0 L 98 0".toList,
  "168 0 0 R 54 0".toList,
  "168 1 1 R 167 0".toList,
  "169 0 0 R 74 0".toList,
  "169 1 1 R 67 0".toList
]
def pairs16 : List RawPair := [
  ((false, (true, (102, false))), (true, (true, (159, false)))),
  ((false, (true, (248, false))), (true, (true, (160, false)))),
  ((false, (true, (226, false))), (true, (true, (161, false)))),
  ((false, (true, (215, false))), (true, (true, (162, false)))),
  ((false, (true, (163, false))), (false, (false, (97, false)))),
  ((false, (true, (164, false))), (true, (true, (61, false)))),
  ((false, (true, (100, false))), (true, (true, (165, false)))),
  ((false, (true, (67, false))), (false, (false, (98, false)))),
  ((false, (true, (54, false))), (true, (true, (167, false)))),
  ((false, (true, (74, false))), (true, (true, (67, false))))
]

def lines17 : List (List Char) := [
  "170 0 0 R 169 0".toList,
  "170 1 1 R 65 0".toList,
  "171 0 0 R 101 0".toList,
  "171 1 0 L 98 0".toList,
  "172 0 0 R 168 0".toList,
  "172 1 1 R 170 0".toList,
  "173 0 0 R 157 0".toList,
  "173 1 1 R 172 0".toList,
  "174 0 0 R 173 0".toList,
  "174 1 0 L 98 0".toList,
  "175 0 0 R 74 0".toList,
  "175 1 1 R 174 0".toList,
  "176 0 0 R 66 0".toList,
  "176 1 1 R 171 0".toList,
  "177 0 0 R 72 0".toList,
  "177 1 1 R 167 0".toList,
  "178 0 0 R 176 0".toList,
  "178 1 1 R 177 0".toList,
  "179 0 0 R 68 0".toList,
  "179 1 0 L 97 0".toList
]
def pairs17 : List RawPair := [
  ((false, (true, (169, false))), (true, (true, (65, false)))),
  ((false, (true, (101, false))), (false, (false, (98, false)))),
  ((false, (true, (168, false))), (true, (true, (170, false)))),
  ((false, (true, (157, false))), (true, (true, (172, false)))),
  ((false, (true, (173, false))), (false, (false, (98, false)))),
  ((false, (true, (74, false))), (true, (true, (174, false)))),
  ((false, (true, (66, false))), (true, (true, (171, false)))),
  ((false, (true, (72, false))), (true, (true, (167, false)))),
  ((false, (true, (176, false))), (true, (true, (177, false)))),
  ((false, (true, (68, false))), (false, (false, (97, false))))
]

def lines18 : List (List Char) := [
  "180 0 0 R 69 0".toList,
  "180 1 0 L 98 0".toList,
  "181 0 0 R 54 0".toList,
  "181 1 1 R 180 0".toList,
  "182 0 0 R 62 0".toList,
  "182 1 1 R 171 0".toList,
  "183 0 0 R 68 0".toList,
  "183 1 1 R 171 0".toList,
  "184 0 0 R 72 0".toList,
  "184 1 1 R 180 0".toList,
  "185 0 0 R 183 0".toList,
  "185 1 1 R 184 0".toList,
  "186 0 0 R 70 0".toList,
  "186 1 0 L 97 0".toList,
  "187 0 0 R 71 0".toList,
  "187 1 0 L 98 0".toList,
  "188 0 0 R 54 0".toList,
  "188 1 1 R 187 0".toList,
  "189 0 0 R 186 0".toList,
  "189 1 1 R 188 0".toList
]
def pairs18 : List RawPair := [
  ((false, (true, (69, false))), (false, (false, (98, false)))),
  ((false, (true, (54, false))), (true, (true, (180, false)))),
  ((false, (true, (62, false))), (true, (true, (171, false)))),
  ((false, (true, (68, false))), (true, (true, (171, false)))),
  ((false, (true, (72, false))), (true, (true, (180, false)))),
  ((false, (true, (183, false))), (true, (true, (184, false)))),
  ((false, (true, (70, false))), (false, (false, (97, false)))),
  ((false, (true, (71, false))), (false, (false, (98, false)))),
  ((false, (true, (54, false))), (true, (true, (187, false)))),
  ((false, (true, (186, false))), (true, (true, (188, false))))
]

def lines19 : List (List Char) := [
  "190 0 0 R 185 0".toList,
  "190 1 1 R 189 0".toList,
  "191 0 0 R 52 0".toList,
  "191 1 0 L 97 0".toList,
  "192 0 0 R 58 0".toList,
  "192 1 0 L 97 0".toList,
  "193 0 0 R 63 0".toList,
  "193 1 0 L 98 0".toList,
  "194 0 0 R 192 0".toList,
  "194 1 1 R 59 0".toList,
  "195 0 0 R 64 0".toList,
  "195 1 1 R 171 0".toList,
  "196 0 0 R 65 0".toList,
  "196 1 0 L 98 0".toList,
  "197 0 0 R 72 0".toList,
  "197 1 1 R 196 0".toList,
  "198 0 0 R 195 0".toList,
  "198 1 1 R 197 0".toList,
  "199 0 0 R 57 0".toList,
  "199 1 0 L 98 0".toList
]
def pairs19 : List RawPair := [
  ((false, (true, (185, false))), (true, (true, (189, false)))),
  ((false, (true, (52, false))), (false, (false, (97, false)))),
  ((false, (true, (58, false))), (false, (false, (97, false)))),
  ((false, (true, (63, false))), (false, (false, (98, false)))),
  ((false, (true, (192, false))), (true, (true, (59, false)))),
  ((false, (true, (64, false))), (true, (true, (171, false)))),
  ((false, (true, (65, false))), (false, (false, (98, false)))),
  ((false, (true, (72, false))), (true, (true, (196, false)))),
  ((false, (true, (195, false))), (true, (true, (197, false)))),
  ((false, (true, (57, false))), (false, (false, (98, false))))
]

def lines20 : List (List Char) := [
  "200 0 0 R 54 0".toList,
  "200 1 1 R 199 0".toList,
  "201 0 0 R 75 0".toList,
  "201 1 1 R 59 0".toList,
  "202 0 0 R 72 0".toList,
  "202 1 0 L 97 0".toList,
  "203 0 0 R 73 0".toList,
  "203 1 0 L 98 0".toList,
  "204 0 0 R 72 0".toList,
  "204 1 1 R 193 0".toList,
  "205 0 0 R 54 0".toList,
  "205 1 1 R 203 0".toList,
  "206 0 0 R 77 0".toList,
  "206 1 0 L 97 0".toList,
  "207 0 0 R 206 0".toList,
  "207 1 0 L 98 0".toList,
  "208 0 0 R 58 0".toList,
  "208 1 1 R 207 0".toList,
  "209 0 0 R 59 0".toList,
  "209 1 0 L 98 0".toList
]
def pairs20 : List RawPair := [
  ((false, (true, (54, false))), (true, (true, (199, false)))),
  ((false, (true, (75, false))), (true, (true, (59, false)))),
  ((false, (true, (72, false))), (false, (false, (97, false)))),
  ((false, (true, (73, false))), (false, (false, (98, false)))),
  ((false, (true, (72, false))), (true, (true, (193, false)))),
  ((false, (true, (54, false))), (true, (true, (203, false)))),
  ((false, (true, (77, false))), (false, (false, (97, false)))),
  ((false, (true, (206, false))), (false, (false, (98, false)))),
  ((false, (true, (58, false))), (true, (true, (207, false)))),
  ((false, (true, (59, false))), (false, (false, (98, false))))
]

def lines21 : List (List Char) := [
  "210 0 0 R 77 0".toList,
  "210 1 1 R 209 0".toList,
  "211 0 0 R 76 0".toList,
  "211 1 1 R 73 0".toList,
  "212 0 0 R 55 0".toList,
  "212 1 0 L 98 0".toList,
  "213 0 0 R 70 0".toList,
  "213 1 1 R 212 0".toList,
  "214 0 0 R 52 0".toList,
  "214 1 1 R 187 0".toList,
  "215 0 0 R 182 0".toList,
  "215 1 1 R 204 0".toList,
  "216 0 0 R 53 0".toList,
  "216 1 0 L 98 0".toList,
  "217 0 0 R 54 0".toList,
  "217 1 1 R 216 0".toList,
  "218 0 0 R 214 0".toList,
  "218 1 1 R 217 0".toList,
  "219 0 0 R 213 0".toList,
  "219 1 1 R 218 0".toList
]
def pairs21 : List RawPair := [
  ((false, (true, (77, false))), (true, (true, (209, false)))),
  ((false, (true, (76, false))), (true, (true, (73, false)))),
  ((false, (true, (55, false))), (false, (false, (98, false)))),
  ((false, (true, (70, false))), (true, (true, (212, false)))),
  ((false, (true, (52, false))), (true, (true, (187, false)))),
  ((false, (true, (182, false))), (true, (true, (204, false)))),
  ((false, (true, (53, false))), (false, (false, (98, false)))),
  ((false, (true, (54, false))), (true, (true, (216, false)))),
  ((false, (true, (214, false))), (true, (true, (217, false)))),
  ((false, (true, (213, false))), (true, (true, (218, false))))
]

def lines22 : List (List Char) := [
  "220 0 0 R 76 0".toList,
  "220 1 1 R 219 0".toList,
  "221 0 0 R 70 0".toList,
  "221 1 1 R 146 0".toList,
  "222 0 0 R 72 0".toList,
  "222 1 1 R 212 0".toList,
  "223 0 0 R 222 0".toList,
  "223 1 1 R 189 0".toList,
  "224 0 0 R 221 0".toList,
  "224 1 1 R 223 0".toList,
  "225 0 0 R 220 0".toList,
  "225 1 1 R 224 0".toList,
  "226 0 0 R 50 0".toList,
  "226 1 0 L 97 0".toList,
  "227 0 0 R 211 0".toList,
  "227 1 1 R 225 0".toList,
  "228 0 0 R 202 0".toList,
  "228 1 1 R 227 0".toList,
  "229 0 0 R 210 0".toList,
  "229 1 1 R 228 0".toList
]
def pairs22 : List RawPair := [
  ((false, (true, (76, false))), (true, (true, (219, false)))),
  ((false, (true, (70, false))), (true, (true, (146, false)))),
  ((false, (true, (72, false))), (true, (true, (212, false)))),
  ((false, (true, (222, false))), (true, (true, (189, false)))),
  ((false, (true, (221, false))), (true, (true, (223, false)))),
  ((false, (true, (220, false))), (true, (true, (224, false)))),
  ((false, (true, (50, false))), (false, (false, (97, false)))),
  ((false, (true, (211, false))), (true, (true, (225, false)))),
  ((false, (true, (202, false))), (true, (true, (227, false)))),
  ((false, (true, (210, false))), (true, (true, (228, false))))
]

def lines23 : List (List Char) := [
  "230 0 0 R 192 0".toList,
  "230 1 1 R 229 0".toList,
  "231 0 0 R 208 0".toList,
  "231 1 1 R 230 0".toList,
  "232 0 0 R 205 0".toList,
  "232 1 1 R 231 0".toList,
  "233 0 0 R 202 0".toList,
  "233 1 1 R 232 0".toList,
  "234 0 0 R 178 0".toList,
  "234 1 1 R 233 0".toList,
  "235 0 0 R 201 0".toList,
  "235 1 1 R 234 0".toList,
  "236 0 0 R 58 0".toList,
  "236 1 1 R 235 0".toList,
  "237 0 0 R 51 0".toList,
  "237 1 0 L 98 0".toList,
  "238 0 0 R 236 0".toList,
  "238 1 0 L 98 0".toList,
  "239 0 0 R 56 0".toList,
  "239 1 1 R 238 0".toList
]
def pairs23 : List RawPair := [
  ((false, (true, (192, false))), (true, (true, (229, false)))),
  ((false, (true, (208, false))), (true, (true, (230, false)))),
  ((false, (true, (205, false))), (true, (true, (231, false)))),
  ((false, (true, (202, false))), (true, (true, (232, false)))),
  ((false, (true, (178, false))), (true, (true, (233, false)))),
  ((false, (true, (201, false))), (true, (true, (234, false)))),
  ((false, (true, (58, false))), (true, (true, (235, false)))),
  ((false, (true, (51, false))), (false, (false, (98, false)))),
  ((false, (true, (236, false))), (false, (false, (98, false)))),
  ((false, (true, (56, false))), (true, (true, (238, false))))
]

def lines24 : List (List Char) := [
  "240 0 0 R 59 0".toList,
  "240 1 0 L 95 0".toList,
  "241 0 0 R 58 0".toList,
  "241 1 1 R 240 0".toList,
  "242 0 0 R 51 0".toList,
  "242 1 0 L 95 0".toList,
  "243 0 0 R 226 0".toList,
  "243 1 1 R 242 0".toList,
  "244 0 0 R 241 0".toList,
  "244 1 1 R 243 0".toList,
  "245 0 0 R 239 0".toList,
  "245 1 1 R 244 0".toList,
  "246 0 0 R 200 0".toList,
  "246 1 1 R 245 0".toList,
  "247 0 0 R 198 0".toList,
  "247 1 1 R 246 0".toList,
  "248 0 0 R 54 0".toList,
  "248 1 1 R 237 0".toList,
  "249 0 0 R 194 0".toList,
  "249 1 1 R 247 0".toList
]
def pairs24 : List RawPair := [
  ((false, (true, (59, false))), (false, (false, (95, false)))),
  ((false, (true, (58, false))), (true, (true, (240, false)))),
  ((false, (true, (51, false))), (false, (false, (95, false)))),
  ((false, (true, (226, false))), (true, (true, (242, false)))),
  ((false, (true, (241, false))), (true, (true, (243, false)))),
  ((false, (true, (239, false))), (true, (true, (244, false)))),
  ((false, (true, (200, false))), (true, (true, (245, false)))),
  ((false, (true, (198, false))), (true, (true, (246, false)))),
  ((false, (true, (54, false))), (true, (true, (237, false)))),
  ((false, (true, (194, false))), (true, (true, (247, false))))
]

def lines25 : List (List Char) := [
  "250 0 0 R 191 0".toList,
  "250 1 1 R 249 0".toList,
  "251 0 0 R 190 0".toList,
  "251 1 1 R 250 0".toList,
  "252 0 0 R 251 0".toList,
  "252 1 0 L 98 0".toList,
  "253 0 0 R 68 0".toList,
  "253 1 1 R 252 0".toList,
  "254 0 0 R 197 0".toList,
  "254 1 1 R 55 0".toList,
  "255 0 0 R 195 0".toList,
  "255 1 1 R 254 0".toList,
  "256 0 0 R 255 0".toList,
  "256 1 0 L 98 0".toList,
  "257 0 0 R 66 0".toList,
  "257 1 1 R 256 0".toList,
  "258 0 0 R 257 0".toList,
  "258 1 1 R 168 0".toList,
  "259 0 0 R 99 0".toList,
  "259 1 1 R 166 0".toList
]
def pairs25 : List RawPair := [
  ((false, (true, (191, false))), (true, (true, (249, false)))),
  ((false, (true, (190, false))), (true, (true, (250, false)))),
  ((false, (true, (251, false))), (false, (false, (98, false)))),
  ((false, (true, (68, false))), (true, (true, (252, false)))),
  ((false, (true, (197, false))), (true, (true, (55, false)))),
  ((false, (true, (195, false))), (true, (true, (254, false)))),
  ((false, (true, (255, false))), (false, (false, (98, false)))),
  ((false, (true, (66, false))), (true, (true, (256, false)))),
  ((false, (true, (257, false))), (true, (true, (168, false)))),
  ((false, (true, (99, false))), (true, (true, (166, false))))
]

def lines26 : List (List Char) := [
  "260 0 1 R 42 0".toList,
  "260 1 0 R 15 0".toList,
  "261 0 1 R 42 0".toList,
  "261 1 0 R 16 0".toList,
  "262 0 0 L 263 0".toList,
  "262 1 1 L 262 0".toList,
  "263 0 0 L 264 0".toList,
  "263 1 1 L 262 0".toList,
  "264 0 0 R 44 0".toList,
  "264 1 0 R 49 0".toList,
  "265 0 0 R 266 0".toList,
  "265 1 1 R 265 0".toList,
  "266 0 1 R 14 0".toList,
  "266 1 1 R 265 0".toList,
  "267 0 1 R 268 0".toList,
  "267 1 1 R 267 0".toList,
  "268 0 0 R 269 0".toList,
  "268 1 1 R 268 0".toList,
  "269 0 0 R 17 0".toList,
  "269 1 1 R 268 0".toList
]
def pairs26 : List RawPair := [
  ((true, (true, (42, false))), (false, (true, (15, false)))),
  ((true, (true, (42, false))), (false, (true, (16, false)))),
  ((false, (false, (263, false))), (true, (false, (262, false)))),
  ((false, (false, (264, false))), (true, (false, (262, false)))),
  ((false, (true, (44, false))), (false, (true, (49, false)))),
  ((false, (true, (266, false))), (true, (true, (265, false)))),
  ((true, (true, (14, false))), (true, (true, (265, false)))),
  ((true, (true, (268, false))), (true, (true, (267, false)))),
  ((false, (true, (269, false))), (true, (true, (268, false)))),
  ((false, (true, (17, false))), (true, (true, (268, false))))
]

def lines27 : List (List Char) := [
  "270 0 0 R 9 0".toList,
  "270 1 1 R 270 0".toList,
  "271 0 0 R 270 0".toList,
  "271 1 1 R 271 0".toList,
  "272 0 0 R 282 0".toList,
  "272 1 1 R 272 0".toList,
  "273 0 0 R 272 0".toList,
  "273 1 1 R 273 0".toList,
  "274 0 0 R 273 0".toList,
  "274 1 1 R 274 0".toList,
  "275 0 0 R 271 0".toList,
  "275 1 1 R 275 0".toList,
  "276 0 0 R 275 0".toList,
  "276 1 1 R 276 0".toList,
  "277 0 0 R 276 0".toList,
  "277 1 1 R 277 0".toList,
  "278 0 0 R 277 0".toList,
  "278 1 1 R 278 0".toList,
  "279 0 0 R 278 0".toList,
  "279 1 1 R 279 0".toList
]
def pairs27 : List RawPair := [
  ((false, (true, (9, false))), (true, (true, (270, false)))),
  ((false, (true, (270, false))), (true, (true, (271, false)))),
  ((false, (true, (282, false))), (true, (true, (272, false)))),
  ((false, (true, (272, false))), (true, (true, (273, false)))),
  ((false, (true, (273, false))), (true, (true, (274, false)))),
  ((false, (true, (271, false))), (true, (true, (275, false)))),
  ((false, (true, (275, false))), (true, (true, (276, false)))),
  ((false, (true, (276, false))), (true, (true, (277, false)))),
  ((false, (true, (277, false))), (true, (true, (278, false)))),
  ((false, (true, (278, false))), (true, (true, (279, false))))
]

def lines28 : List (List Char) := [
  "280 0 0 R 279 0".toList,
  "280 1 1 R 280 0".toList,
  "281 0 0 R 280 0".toList,
  "281 1 1 R 281 0".toList,
  "282 0 0 R 281 0".toList,
  "282 1 1 R 282 0".toList,
  "283 0 0 L 262 0".toList,
  "283 1 1 R 283 0".toList
]
def pairs28 : List RawPair := [
  ((false, (true, (279, false))), (true, (true, (280, false)))),
  ((false, (true, (280, false))), (true, (true, (281, false)))),
  ((false, (true, (281, false))), (true, (true, (282, false)))),
  ((false, (false, (262, false))), (true, (true, (283, false))))
]

def lines : List (List Char) := lines00 ++ lines01 ++ lines02 ++ lines03 ++ lines04 ++ lines05 ++ lines06 ++ lines07 ++ lines08 ++ lines09 ++ lines10 ++ lines11 ++ lines12 ++ lines13 ++ lines14 ++ lines15 ++ lines16 ++ lines17 ++ lines18 ++ lines19 ++ lines20 ++ lines21 ++ lines22 ++ lines23 ++ lines24 ++ lines25 ++ lines26 ++ lines27 ++ lines28
def pairs : List RawPair := pairs00 ++ pairs01 ++ pairs02 ++ pairs03 ++ pairs04 ++ pairs05 ++ pairs06 ++ pairs07 ++ pairs08 ++ pairs09 ++ pairs10 ++ pairs11 ++ pairs12 ++ pairs13 ++ pairs14 ++ pairs15 ++ pairs16 ++ pairs17 ++ pairs18 ++ pairs19 ++ pairs20 ++ pairs21 ++ pairs22 ++ pairs23 ++ pairs24 ++ pairs25 ++ pairs26 ++ pairs27 ++ pairs28

theorem pairs_eq_data : pairs = Table284.data.2 := by rfl

end Shared.Beeping.NPcoNP.Table284LineData
