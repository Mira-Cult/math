import Shared.PNP.Record285.BootstrapTraceData

/-! Kernel-checked bootstrap certificate. The literal text-to-numeric
binding remains an explicit separate premise. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option exponentiation.threshold 4096
namespace Shared.PNP.Record285.BootstrapTraceProof
open Shared.Beeping Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapRows
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.BootstrapChecker
open Shared.PNP.Record285.BootstrapTraceData

theorem block0 : verify b0 c0 = some (216,c1) := by decide
theorem block1 : verify b1 c1 = some (447,c2) := by decide
theorem block2 : verify b2 c2 = some (567,c3) := by decide
theorem block3 : verify b3 c3 = some (759,c4) := by decide
theorem block4 : verify b4 c4 = some (1436,c5) := by decide
theorem block5 : verify b5 c5 = some (2111,c6) := by decide
theorem block6 : verify b6 c6 = some (1327,c7) := by decide
theorem block7 : verify b7 c7 = some (759,c8) := by decide
theorem block8 : verify b8 c8 = some (1436,c9) := by decide
theorem block9 : verify b9 c9 = some (2111,c10) := by decide
theorem block10 : verify b10 c10 = some (2555,c11) := by decide
theorem block11 : verify b11 c11 = some (3411,c12) := by decide
theorem block12 : verify b12 c12 = some (4087,c13) := by decide
theorem block13 : verify b13 c13 = some (4764,c14) := by decide
theorem block14 : verify b14 c14 = some (5439,c15) := by decide
theorem block15 : verify b15 c15 = some (5627,c16) := by decide
theorem block16 : verify b16 c16 = some (6739,c17) := by decide
theorem block17 : verify b17 c17 = some (932,c18) := by decide
theorem block18 : verify b18 c18 = some (1071,c19) := by decide
theorem block19 : verify b19 c19 = some (1595,c20) := by decide
theorem block20 : verify b20 c20 = some (2371,c21) := by decide
theorem block21 : verify b21 c21 = some (3047,c22) := by decide
theorem block22 : verify b22 c22 = some (3724,c23) := by decide
theorem block23 : verify b23 c23 = some (4399,c24) := by decide
theorem block24 : verify b24 c24 = some (4667,c25) := by decide
theorem block25 : verify b25 c25 = some (5699,c26) := by decide
theorem block26 : verify b26 c26 = some (6375,c27) := by decide
theorem block27 : verify b27 c27 = some (7052,c28) := by decide
theorem block28 : verify b28 c28 = some (7727,c29) := by decide
theorem block29 : verify b29 c29 = some (7739,c30) := by decide
theorem block30 : verify b30 c30 = some (9027,c31) := by decide
theorem block31 : verify b31 c31 = some (9703,c32) := by decide
theorem block32 : verify b32 c32 = some (10380,c33) := by decide
theorem block33 : verify b33 c33 = some (11055,c34) := by decide
theorem block34 : verify b34 c34 = some (10811,c35) := by decide
theorem block35 : verify b35 c35 = some (12355,c36) := by decide
theorem block36 : verify b36 c36 = some (13031,c37) := by decide
theorem block37 : verify b37 c37 = some (13708,c38) := by decide
theorem block38 : verify b38 c38 = some (14383,c39) := by decide
theorem block39 : verify b39 c39 = some (13883,c40) := by decide
theorem block40 : verify b40 c40 = some (15683,c41) := by decide
theorem block41 : verify b41 c41 = some (16359,c42) := by decide
theorem block42 : verify b42 c42 = some (17036,c43) := by decide
theorem block43 : verify b43 c43 = some (17711,c44) := by decide
theorem block44 : verify b44 c44 = some (16955,c45) := by decide
theorem block45 : verify b45 c45 = some (3211,c46) := by decide
theorem block46 : verify b46 c46 = some (1020,c47) := by decide
theorem block47 : verify b47 c47 = some (1695,c48) := by decide
theorem block48 : verify b48 c48 = some (2171,c49) := by decide
theorem block49 : verify b49 c49 = some (2995,c50) := by decide
theorem block50 : verify b50 c50 = some (3671,c51) := by decide
theorem block51 : verify b51 c51 = some (4348,c52) := by decide
theorem block52 : verify b52 c52 = some (5023,c53) := by decide
theorem block53 : verify b53 c53 = some (5243,c54) := by decide
theorem block54 : verify b54 c54 = some (6323,c55) := by decide
theorem block55 : verify b55 c55 = some (6999,c56) := by decide
theorem block56 : verify b56 c56 = some (7676,c57) := by decide
theorem block57 : verify b57 c57 = some (8351,c58) := by decide
theorem block58 : verify b58 c58 = some (8315,c59) := by decide
theorem block59 : verify b59 c59 = some (9651,c60) := by decide
theorem block60 : verify b60 c60 = some (10327,c61) := by decide
theorem block61 : verify b61 c61 = some (11004,c62) := by decide
theorem block62 : verify b62 c62 = some (11679,c63) := by decide
theorem block63 : verify b63 c63 = some (11387,c64) := by decide
theorem block64 : verify b64 c64 = some (12979,c65) := by decide
theorem block65 : verify b65 c65 = some (13655,c66) := by decide
theorem block66 : verify b66 c66 = some (14332,c67) := by decide
theorem block67 : verify b67 c67 = some (15007,c68) := by decide
theorem block68 : verify b68 c68 = some (14459,c69) := by decide
theorem block69 : verify b69 c69 = some (16307,c70) := by decide
theorem block70 : verify b70 c70 = some (16983,c71) := by decide
theorem block71 : verify b71 c71 = some (17660,c72) := by decide
theorem block72 : verify b72 c72 = some (18335,c73) := by decide
theorem block73 : verify b73 c73 = some (17531,c74) := by decide
theorem block74 : verify b74 c74 = some (19635,c75) := by decide
theorem block75 : verify b75 c75 = some (20311,c76) := by decide
theorem block76 : verify b76 c76 = some (20988,c77) := by decide
theorem block77 : verify b77 c77 = some (21663,c78) := by decide
theorem block78 : verify b78 c78 = some (20603,c79) := by decide
theorem block79 : verify b79 c79 = some (22963,c80) := by decide
theorem block80 : verify b80 c80 = some (23639,c81) := by decide
theorem block81 : verify b81 c81 = some (24316,c82) := by decide
theorem block82 : verify b82 c82 = some (24991,c83) := by decide
theorem block83 : verify b83 c83 = some (23675,c84) := by decide
theorem block84 : verify b84 c84 = some (26291,c85) := by decide
theorem block85 : verify b85 c85 = some (26967,c86) := by decide
theorem block86 : verify b86 c86 = some (27644,c87) := by decide
theorem block87 : verify b87 c87 = some (28319,c88) := by decide
theorem block88 : verify b88 c88 = some (26747,c89) := by decide
theorem block89 : verify b89 c89 = some (29619,c90) := by decide
theorem block90 : verify b90 c90 = some (30295,c91) := by decide
theorem block91 : verify b91 c91 = some (30972,c92) := by decide
theorem block92 : verify b92 c92 = some (31647,c93) := by decide
theorem block93 : verify b93 c93 = some (29819,c94) := by decide
theorem block94 : verify b94 c94 = some (32947,c95) := by decide
theorem block95 : verify b95 c95 = some (33623,c96) := by decide
theorem block96 : verify b96 c96 = some (34300,c97) := by decide
theorem block97 : verify b97 c97 = some (34975,c98) := by decide
theorem block98 : verify b98 c98 = some (32891,c99) := by decide
theorem block99 : verify b99 c99 = some (36275,c100) := by decide
theorem block100 : verify b100 c100 = some (36951,c101) := by decide
theorem block101 : verify b101 c101 = some (37628,c102) := by decide
theorem block102 : verify b102 c102 = some (38303,c103) := by decide
theorem block103 : verify b103 c103 = some (35963,c104) := by decide
theorem block104 : verify b104 c104 = some (39603,c105) := by decide
theorem block105 : verify b105 c105 = some (40279,c106) := by decide
theorem block106 : verify b106 c106 = some (40956,c107) := by decide
theorem block107 : verify b107 c107 = some (41631,c108) := by decide
theorem block108 : verify b108 c108 = some (39035,c109) := by decide
theorem block109 : verify b109 c109 = some (42931,c110) := by decide
theorem block110 : verify b110 c110 = some (43607,c111) := by decide
theorem block111 : verify b111 c111 = some (44284,c112) := by decide
theorem block112 : verify b112 c112 = some (44959,c113) := by decide
theorem block113 : verify b113 c113 = some (42107,c114) := by decide
theorem block114 : verify b114 c114 = some (46259,c115) := by decide
theorem block115 : verify b115 c115 = some (46935,c116) := by decide
theorem block116 : verify b116 c116 = some (47612,c117) := by decide
theorem block117 : verify b117 c117 = some (48287,c118) := by decide
theorem block118 : verify b118 c118 = some (45179,c119) := by decide
theorem block119 : verify b119 c119 = some (34262,c120) := by decide

theorem final_shape : c120 = ⟨exit,(-2 : Int),rep4 1910,true,30⟩ := by decide

/-- The entire first bootstrap is checked for any machine satisfying the ten rows. -/
theorem bootstrap (M : Machine 285) (rows : Rows M) :
    silent M 2133492 c0 = some c120 := by
  have h0 : silent M 216 c0 = some c1 := verify_sound M rows b0 c0 c1 216 block0
  have h1 : silent M 447 c1 = some c2 := verify_sound M rows b1 c1 c2 447 block1
  have h2 : silent M 567 c2 = some c3 := verify_sound M rows b2 c2 c3 567 block2
  have h3 : silent M 759 c3 = some c4 := verify_sound M rows b3 c3 c4 759 block3
  have h4 : silent M 1436 c4 = some c5 := verify_sound M rows b4 c4 c5 1436 block4
  have h5 : silent M 2111 c5 = some c6 := verify_sound M rows b5 c5 c6 2111 block5
  have h6 : silent M 1327 c6 = some c7 := verify_sound M rows b6 c6 c7 1327 block6
  have h7 : silent M 759 c7 = some c8 := verify_sound M rows b7 c7 c8 759 block7
  have h8 : silent M 1436 c8 = some c9 := verify_sound M rows b8 c8 c9 1436 block8
  have h9 : silent M 2111 c9 = some c10 := verify_sound M rows b9 c9 c10 2111 block9
  have h10 : silent M 2555 c10 = some c11 := verify_sound M rows b10 c10 c11 2555 block10
  have h11 : silent M 3411 c11 = some c12 := verify_sound M rows b11 c11 c12 3411 block11
  have h12 : silent M 4087 c12 = some c13 := verify_sound M rows b12 c12 c13 4087 block12
  have h13 : silent M 4764 c13 = some c14 := verify_sound M rows b13 c13 c14 4764 block13
  have h14 : silent M 5439 c14 = some c15 := verify_sound M rows b14 c14 c15 5439 block14
  have h15 : silent M 5627 c15 = some c16 := verify_sound M rows b15 c15 c16 5627 block15
  have h16 : silent M 6739 c16 = some c17 := verify_sound M rows b16 c16 c17 6739 block16
  have h17 : silent M 932 c17 = some c18 := verify_sound M rows b17 c17 c18 932 block17
  have h18 : silent M 1071 c18 = some c19 := verify_sound M rows b18 c18 c19 1071 block18
  have h19 : silent M 1595 c19 = some c20 := verify_sound M rows b19 c19 c20 1595 block19
  have h20 : silent M 2371 c20 = some c21 := verify_sound M rows b20 c20 c21 2371 block20
  have h21 : silent M 3047 c21 = some c22 := verify_sound M rows b21 c21 c22 3047 block21
  have h22 : silent M 3724 c22 = some c23 := verify_sound M rows b22 c22 c23 3724 block22
  have h23 : silent M 4399 c23 = some c24 := verify_sound M rows b23 c23 c24 4399 block23
  have h24 : silent M 4667 c24 = some c25 := verify_sound M rows b24 c24 c25 4667 block24
  have h25 : silent M 5699 c25 = some c26 := verify_sound M rows b25 c25 c26 5699 block25
  have h26 : silent M 6375 c26 = some c27 := verify_sound M rows b26 c26 c27 6375 block26
  have h27 : silent M 7052 c27 = some c28 := verify_sound M rows b27 c27 c28 7052 block27
  have h28 : silent M 7727 c28 = some c29 := verify_sound M rows b28 c28 c29 7727 block28
  have h29 : silent M 7739 c29 = some c30 := verify_sound M rows b29 c29 c30 7739 block29
  have h30 : silent M 9027 c30 = some c31 := verify_sound M rows b30 c30 c31 9027 block30
  have h31 : silent M 9703 c31 = some c32 := verify_sound M rows b31 c31 c32 9703 block31
  have h32 : silent M 10380 c32 = some c33 := verify_sound M rows b32 c32 c33 10380 block32
  have h33 : silent M 11055 c33 = some c34 := verify_sound M rows b33 c33 c34 11055 block33
  have h34 : silent M 10811 c34 = some c35 := verify_sound M rows b34 c34 c35 10811 block34
  have h35 : silent M 12355 c35 = some c36 := verify_sound M rows b35 c35 c36 12355 block35
  have h36 : silent M 13031 c36 = some c37 := verify_sound M rows b36 c36 c37 13031 block36
  have h37 : silent M 13708 c37 = some c38 := verify_sound M rows b37 c37 c38 13708 block37
  have h38 : silent M 14383 c38 = some c39 := verify_sound M rows b38 c38 c39 14383 block38
  have h39 : silent M 13883 c39 = some c40 := verify_sound M rows b39 c39 c40 13883 block39
  have h40 : silent M 15683 c40 = some c41 := verify_sound M rows b40 c40 c41 15683 block40
  have h41 : silent M 16359 c41 = some c42 := verify_sound M rows b41 c41 c42 16359 block41
  have h42 : silent M 17036 c42 = some c43 := verify_sound M rows b42 c42 c43 17036 block42
  have h43 : silent M 17711 c43 = some c44 := verify_sound M rows b43 c43 c44 17711 block43
  have h44 : silent M 16955 c44 = some c45 := verify_sound M rows b44 c44 c45 16955 block44
  have h45 : silent M 3211 c45 = some c46 := verify_sound M rows b45 c45 c46 3211 block45
  have h46 : silent M 1020 c46 = some c47 := verify_sound M rows b46 c46 c47 1020 block46
  have h47 : silent M 1695 c47 = some c48 := verify_sound M rows b47 c47 c48 1695 block47
  have h48 : silent M 2171 c48 = some c49 := verify_sound M rows b48 c48 c49 2171 block48
  have h49 : silent M 2995 c49 = some c50 := verify_sound M rows b49 c49 c50 2995 block49
  have h50 : silent M 3671 c50 = some c51 := verify_sound M rows b50 c50 c51 3671 block50
  have h51 : silent M 4348 c51 = some c52 := verify_sound M rows b51 c51 c52 4348 block51
  have h52 : silent M 5023 c52 = some c53 := verify_sound M rows b52 c52 c53 5023 block52
  have h53 : silent M 5243 c53 = some c54 := verify_sound M rows b53 c53 c54 5243 block53
  have h54 : silent M 6323 c54 = some c55 := verify_sound M rows b54 c54 c55 6323 block54
  have h55 : silent M 6999 c55 = some c56 := verify_sound M rows b55 c55 c56 6999 block55
  have h56 : silent M 7676 c56 = some c57 := verify_sound M rows b56 c56 c57 7676 block56
  have h57 : silent M 8351 c57 = some c58 := verify_sound M rows b57 c57 c58 8351 block57
  have h58 : silent M 8315 c58 = some c59 := verify_sound M rows b58 c58 c59 8315 block58
  have h59 : silent M 9651 c59 = some c60 := verify_sound M rows b59 c59 c60 9651 block59
  have h60 : silent M 10327 c60 = some c61 := verify_sound M rows b60 c60 c61 10327 block60
  have h61 : silent M 11004 c61 = some c62 := verify_sound M rows b61 c61 c62 11004 block61
  have h62 : silent M 11679 c62 = some c63 := verify_sound M rows b62 c62 c63 11679 block62
  have h63 : silent M 11387 c63 = some c64 := verify_sound M rows b63 c63 c64 11387 block63
  have h64 : silent M 12979 c64 = some c65 := verify_sound M rows b64 c64 c65 12979 block64
  have h65 : silent M 13655 c65 = some c66 := verify_sound M rows b65 c65 c66 13655 block65
  have h66 : silent M 14332 c66 = some c67 := verify_sound M rows b66 c66 c67 14332 block66
  have h67 : silent M 15007 c67 = some c68 := verify_sound M rows b67 c67 c68 15007 block67
  have h68 : silent M 14459 c68 = some c69 := verify_sound M rows b68 c68 c69 14459 block68
  have h69 : silent M 16307 c69 = some c70 := verify_sound M rows b69 c69 c70 16307 block69
  have h70 : silent M 16983 c70 = some c71 := verify_sound M rows b70 c70 c71 16983 block70
  have h71 : silent M 17660 c71 = some c72 := verify_sound M rows b71 c71 c72 17660 block71
  have h72 : silent M 18335 c72 = some c73 := verify_sound M rows b72 c72 c73 18335 block72
  have h73 : silent M 17531 c73 = some c74 := verify_sound M rows b73 c73 c74 17531 block73
  have h74 : silent M 19635 c74 = some c75 := verify_sound M rows b74 c74 c75 19635 block74
  have h75 : silent M 20311 c75 = some c76 := verify_sound M rows b75 c75 c76 20311 block75
  have h76 : silent M 20988 c76 = some c77 := verify_sound M rows b76 c76 c77 20988 block76
  have h77 : silent M 21663 c77 = some c78 := verify_sound M rows b77 c77 c78 21663 block77
  have h78 : silent M 20603 c78 = some c79 := verify_sound M rows b78 c78 c79 20603 block78
  have h79 : silent M 22963 c79 = some c80 := verify_sound M rows b79 c79 c80 22963 block79
  have h80 : silent M 23639 c80 = some c81 := verify_sound M rows b80 c80 c81 23639 block80
  have h81 : silent M 24316 c81 = some c82 := verify_sound M rows b81 c81 c82 24316 block81
  have h82 : silent M 24991 c82 = some c83 := verify_sound M rows b82 c82 c83 24991 block82
  have h83 : silent M 23675 c83 = some c84 := verify_sound M rows b83 c83 c84 23675 block83
  have h84 : silent M 26291 c84 = some c85 := verify_sound M rows b84 c84 c85 26291 block84
  have h85 : silent M 26967 c85 = some c86 := verify_sound M rows b85 c85 c86 26967 block85
  have h86 : silent M 27644 c86 = some c87 := verify_sound M rows b86 c86 c87 27644 block86
  have h87 : silent M 28319 c87 = some c88 := verify_sound M rows b87 c87 c88 28319 block87
  have h88 : silent M 26747 c88 = some c89 := verify_sound M rows b88 c88 c89 26747 block88
  have h89 : silent M 29619 c89 = some c90 := verify_sound M rows b89 c89 c90 29619 block89
  have h90 : silent M 30295 c90 = some c91 := verify_sound M rows b90 c90 c91 30295 block90
  have h91 : silent M 30972 c91 = some c92 := verify_sound M rows b91 c91 c92 30972 block91
  have h92 : silent M 31647 c92 = some c93 := verify_sound M rows b92 c92 c93 31647 block92
  have h93 : silent M 29819 c93 = some c94 := verify_sound M rows b93 c93 c94 29819 block93
  have h94 : silent M 32947 c94 = some c95 := verify_sound M rows b94 c94 c95 32947 block94
  have h95 : silent M 33623 c95 = some c96 := verify_sound M rows b95 c95 c96 33623 block95
  have h96 : silent M 34300 c96 = some c97 := verify_sound M rows b96 c96 c97 34300 block96
  have h97 : silent M 34975 c97 = some c98 := verify_sound M rows b97 c97 c98 34975 block97
  have h98 : silent M 32891 c98 = some c99 := verify_sound M rows b98 c98 c99 32891 block98
  have h99 : silent M 36275 c99 = some c100 := verify_sound M rows b99 c99 c100 36275 block99
  have h100 : silent M 36951 c100 = some c101 := verify_sound M rows b100 c100 c101 36951 block100
  have h101 : silent M 37628 c101 = some c102 := verify_sound M rows b101 c101 c102 37628 block101
  have h102 : silent M 38303 c102 = some c103 := verify_sound M rows b102 c102 c103 38303 block102
  have h103 : silent M 35963 c103 = some c104 := verify_sound M rows b103 c103 c104 35963 block103
  have h104 : silent M 39603 c104 = some c105 := verify_sound M rows b104 c104 c105 39603 block104
  have h105 : silent M 40279 c105 = some c106 := verify_sound M rows b105 c105 c106 40279 block105
  have h106 : silent M 40956 c106 = some c107 := verify_sound M rows b106 c106 c107 40956 block106
  have h107 : silent M 41631 c107 = some c108 := verify_sound M rows b107 c107 c108 41631 block107
  have h108 : silent M 39035 c108 = some c109 := verify_sound M rows b108 c108 c109 39035 block108
  have h109 : silent M 42931 c109 = some c110 := verify_sound M rows b109 c109 c110 42931 block109
  have h110 : silent M 43607 c110 = some c111 := verify_sound M rows b110 c110 c111 43607 block110
  have h111 : silent M 44284 c111 = some c112 := verify_sound M rows b111 c111 c112 44284 block111
  have h112 : silent M 44959 c112 = some c113 := verify_sound M rows b112 c112 c113 44959 block112
  have h113 : silent M 42107 c113 = some c114 := verify_sound M rows b113 c113 c114 42107 block113
  have h114 : silent M 46259 c114 = some c115 := verify_sound M rows b114 c114 c115 46259 block114
  have h115 : silent M 46935 c115 = some c116 := verify_sound M rows b115 c115 c116 46935 block115
  have h116 : silent M 47612 c116 = some c117 := verify_sound M rows b116 c116 c117 47612 block116
  have h117 : silent M 48287 c117 = some c118 := verify_sound M rows b117 c117 c118 48287 block117
  have h118 : silent M 45179 c118 = some c119 := verify_sound M rows b118 c118 c119 45179 block118
  have h119 : silent M 34262 c119 = some c120 := verify_sound M rows b119 c119 c120 34262 block119
  have tail119 : silent M 34262 c119 = some c120 := h119
  have tail118 : silent M 79441 c118 = some c120 := silent_compose M c118 c119 c120 45179 34262 h118 tail119
  have tail117 : silent M 127728 c117 = some c120 := silent_compose M c117 c118 c120 48287 79441 h117 tail118
  have tail116 : silent M 175340 c116 = some c120 := silent_compose M c116 c117 c120 47612 127728 h116 tail117
  have tail115 : silent M 222275 c115 = some c120 := silent_compose M c115 c116 c120 46935 175340 h115 tail116
  have tail114 : silent M 268534 c114 = some c120 := silent_compose M c114 c115 c120 46259 222275 h114 tail115
  have tail113 : silent M 310641 c113 = some c120 := silent_compose M c113 c114 c120 42107 268534 h113 tail114
  have tail112 : silent M 355600 c112 = some c120 := silent_compose M c112 c113 c120 44959 310641 h112 tail113
  have tail111 : silent M 399884 c111 = some c120 := silent_compose M c111 c112 c120 44284 355600 h111 tail112
  have tail110 : silent M 443491 c110 = some c120 := silent_compose M c110 c111 c120 43607 399884 h110 tail111
  have tail109 : silent M 486422 c109 = some c120 := silent_compose M c109 c110 c120 42931 443491 h109 tail110
  have tail108 : silent M 525457 c108 = some c120 := silent_compose M c108 c109 c120 39035 486422 h108 tail109
  have tail107 : silent M 567088 c107 = some c120 := silent_compose M c107 c108 c120 41631 525457 h107 tail108
  have tail106 : silent M 608044 c106 = some c120 := silent_compose M c106 c107 c120 40956 567088 h106 tail107
  have tail105 : silent M 648323 c105 = some c120 := silent_compose M c105 c106 c120 40279 608044 h105 tail106
  have tail104 : silent M 687926 c104 = some c120 := silent_compose M c104 c105 c120 39603 648323 h104 tail105
  have tail103 : silent M 723889 c103 = some c120 := silent_compose M c103 c104 c120 35963 687926 h103 tail104
  have tail102 : silent M 762192 c102 = some c120 := silent_compose M c102 c103 c120 38303 723889 h102 tail103
  have tail101 : silent M 799820 c101 = some c120 := silent_compose M c101 c102 c120 37628 762192 h101 tail102
  have tail100 : silent M 836771 c100 = some c120 := silent_compose M c100 c101 c120 36951 799820 h100 tail101
  have tail99 : silent M 873046 c99 = some c120 := silent_compose M c99 c100 c120 36275 836771 h99 tail100
  have tail98 : silent M 905937 c98 = some c120 := silent_compose M c98 c99 c120 32891 873046 h98 tail99
  have tail97 : silent M 940912 c97 = some c120 := silent_compose M c97 c98 c120 34975 905937 h97 tail98
  have tail96 : silent M 975212 c96 = some c120 := silent_compose M c96 c97 c120 34300 940912 h96 tail97
  have tail95 : silent M 1008835 c95 = some c120 := silent_compose M c95 c96 c120 33623 975212 h95 tail96
  have tail94 : silent M 1041782 c94 = some c120 := silent_compose M c94 c95 c120 32947 1008835 h94 tail95
  have tail93 : silent M 1071601 c93 = some c120 := silent_compose M c93 c94 c120 29819 1041782 h93 tail94
  have tail92 : silent M 1103248 c92 = some c120 := silent_compose M c92 c93 c120 31647 1071601 h92 tail93
  have tail91 : silent M 1134220 c91 = some c120 := silent_compose M c91 c92 c120 30972 1103248 h91 tail92
  have tail90 : silent M 1164515 c90 = some c120 := silent_compose M c90 c91 c120 30295 1134220 h90 tail91
  have tail89 : silent M 1194134 c89 = some c120 := silent_compose M c89 c90 c120 29619 1164515 h89 tail90
  have tail88 : silent M 1220881 c88 = some c120 := silent_compose M c88 c89 c120 26747 1194134 h88 tail89
  have tail87 : silent M 1249200 c87 = some c120 := silent_compose M c87 c88 c120 28319 1220881 h87 tail88
  have tail86 : silent M 1276844 c86 = some c120 := silent_compose M c86 c87 c120 27644 1249200 h86 tail87
  have tail85 : silent M 1303811 c85 = some c120 := silent_compose M c85 c86 c120 26967 1276844 h85 tail86
  have tail84 : silent M 1330102 c84 = some c120 := silent_compose M c84 c85 c120 26291 1303811 h84 tail85
  have tail83 : silent M 1353777 c83 = some c120 := silent_compose M c83 c84 c120 23675 1330102 h83 tail84
  have tail82 : silent M 1378768 c82 = some c120 := silent_compose M c82 c83 c120 24991 1353777 h82 tail83
  have tail81 : silent M 1403084 c81 = some c120 := silent_compose M c81 c82 c120 24316 1378768 h81 tail82
  have tail80 : silent M 1426723 c80 = some c120 := silent_compose M c80 c81 c120 23639 1403084 h80 tail81
  have tail79 : silent M 1449686 c79 = some c120 := silent_compose M c79 c80 c120 22963 1426723 h79 tail80
  have tail78 : silent M 1470289 c78 = some c120 := silent_compose M c78 c79 c120 20603 1449686 h78 tail79
  have tail77 : silent M 1491952 c77 = some c120 := silent_compose M c77 c78 c120 21663 1470289 h77 tail78
  have tail76 : silent M 1512940 c76 = some c120 := silent_compose M c76 c77 c120 20988 1491952 h76 tail77
  have tail75 : silent M 1533251 c75 = some c120 := silent_compose M c75 c76 c120 20311 1512940 h75 tail76
  have tail74 : silent M 1552886 c74 = some c120 := silent_compose M c74 c75 c120 19635 1533251 h74 tail75
  have tail73 : silent M 1570417 c73 = some c120 := silent_compose M c73 c74 c120 17531 1552886 h73 tail74
  have tail72 : silent M 1588752 c72 = some c120 := silent_compose M c72 c73 c120 18335 1570417 h72 tail73
  have tail71 : silent M 1606412 c71 = some c120 := silent_compose M c71 c72 c120 17660 1588752 h71 tail72
  have tail70 : silent M 1623395 c70 = some c120 := silent_compose M c70 c71 c120 16983 1606412 h70 tail71
  have tail69 : silent M 1639702 c69 = some c120 := silent_compose M c69 c70 c120 16307 1623395 h69 tail70
  have tail68 : silent M 1654161 c68 = some c120 := silent_compose M c68 c69 c120 14459 1639702 h68 tail69
  have tail67 : silent M 1669168 c67 = some c120 := silent_compose M c67 c68 c120 15007 1654161 h67 tail68
  have tail66 : silent M 1683500 c66 = some c120 := silent_compose M c66 c67 c120 14332 1669168 h66 tail67
  have tail65 : silent M 1697155 c65 = some c120 := silent_compose M c65 c66 c120 13655 1683500 h65 tail66
  have tail64 : silent M 1710134 c64 = some c120 := silent_compose M c64 c65 c120 12979 1697155 h64 tail65
  have tail63 : silent M 1721521 c63 = some c120 := silent_compose M c63 c64 c120 11387 1710134 h63 tail64
  have tail62 : silent M 1733200 c62 = some c120 := silent_compose M c62 c63 c120 11679 1721521 h62 tail63
  have tail61 : silent M 1744204 c61 = some c120 := silent_compose M c61 c62 c120 11004 1733200 h61 tail62
  have tail60 : silent M 1754531 c60 = some c120 := silent_compose M c60 c61 c120 10327 1744204 h60 tail61
  have tail59 : silent M 1764182 c59 = some c120 := silent_compose M c59 c60 c120 9651 1754531 h59 tail60
  have tail58 : silent M 1772497 c58 = some c120 := silent_compose M c58 c59 c120 8315 1764182 h58 tail59
  have tail57 : silent M 1780848 c57 = some c120 := silent_compose M c57 c58 c120 8351 1772497 h57 tail58
  have tail56 : silent M 1788524 c56 = some c120 := silent_compose M c56 c57 c120 7676 1780848 h56 tail57
  have tail55 : silent M 1795523 c55 = some c120 := silent_compose M c55 c56 c120 6999 1788524 h55 tail56
  have tail54 : silent M 1801846 c54 = some c120 := silent_compose M c54 c55 c120 6323 1795523 h54 tail55
  have tail53 : silent M 1807089 c53 = some c120 := silent_compose M c53 c54 c120 5243 1801846 h53 tail54
  have tail52 : silent M 1812112 c52 = some c120 := silent_compose M c52 c53 c120 5023 1807089 h52 tail53
  have tail51 : silent M 1816460 c51 = some c120 := silent_compose M c51 c52 c120 4348 1812112 h51 tail52
  have tail50 : silent M 1820131 c50 = some c120 := silent_compose M c50 c51 c120 3671 1816460 h50 tail51
  have tail49 : silent M 1823126 c49 = some c120 := silent_compose M c49 c50 c120 2995 1820131 h49 tail50
  have tail48 : silent M 1825297 c48 = some c120 := silent_compose M c48 c49 c120 2171 1823126 h48 tail49
  have tail47 : silent M 1826992 c47 = some c120 := silent_compose M c47 c48 c120 1695 1825297 h47 tail48
  have tail46 : silent M 1828012 c46 = some c120 := silent_compose M c46 c47 c120 1020 1826992 h46 tail47
  have tail45 : silent M 1831223 c45 = some c120 := silent_compose M c45 c46 c120 3211 1828012 h45 tail46
  have tail44 : silent M 1848178 c44 = some c120 := silent_compose M c44 c45 c120 16955 1831223 h44 tail45
  have tail43 : silent M 1865889 c43 = some c120 := silent_compose M c43 c44 c120 17711 1848178 h43 tail44
  have tail42 : silent M 1882925 c42 = some c120 := silent_compose M c42 c43 c120 17036 1865889 h42 tail43
  have tail41 : silent M 1899284 c41 = some c120 := silent_compose M c41 c42 c120 16359 1882925 h41 tail42
  have tail40 : silent M 1914967 c40 = some c120 := silent_compose M c40 c41 c120 15683 1899284 h40 tail41
  have tail39 : silent M 1928850 c39 = some c120 := silent_compose M c39 c40 c120 13883 1914967 h39 tail40
  have tail38 : silent M 1943233 c38 = some c120 := silent_compose M c38 c39 c120 14383 1928850 h38 tail39
  have tail37 : silent M 1956941 c37 = some c120 := silent_compose M c37 c38 c120 13708 1943233 h37 tail38
  have tail36 : silent M 1969972 c36 = some c120 := silent_compose M c36 c37 c120 13031 1956941 h36 tail37
  have tail35 : silent M 1982327 c35 = some c120 := silent_compose M c35 c36 c120 12355 1969972 h35 tail36
  have tail34 : silent M 1993138 c34 = some c120 := silent_compose M c34 c35 c120 10811 1982327 h34 tail35
  have tail33 : silent M 2004193 c33 = some c120 := silent_compose M c33 c34 c120 11055 1993138 h33 tail34
  have tail32 : silent M 2014573 c32 = some c120 := silent_compose M c32 c33 c120 10380 2004193 h32 tail33
  have tail31 : silent M 2024276 c31 = some c120 := silent_compose M c31 c32 c120 9703 2014573 h31 tail32
  have tail30 : silent M 2033303 c30 = some c120 := silent_compose M c30 c31 c120 9027 2024276 h30 tail31
  have tail29 : silent M 2041042 c29 = some c120 := silent_compose M c29 c30 c120 7739 2033303 h29 tail30
  have tail28 : silent M 2048769 c28 = some c120 := silent_compose M c28 c29 c120 7727 2041042 h28 tail29
  have tail27 : silent M 2055821 c27 = some c120 := silent_compose M c27 c28 c120 7052 2048769 h27 tail28
  have tail26 : silent M 2062196 c26 = some c120 := silent_compose M c26 c27 c120 6375 2055821 h26 tail27
  have tail25 : silent M 2067895 c25 = some c120 := silent_compose M c25 c26 c120 5699 2062196 h25 tail26
  have tail24 : silent M 2072562 c24 = some c120 := silent_compose M c24 c25 c120 4667 2067895 h24 tail25
  have tail23 : silent M 2076961 c23 = some c120 := silent_compose M c23 c24 c120 4399 2072562 h23 tail24
  have tail22 : silent M 2080685 c22 = some c120 := silent_compose M c22 c23 c120 3724 2076961 h22 tail23
  have tail21 : silent M 2083732 c21 = some c120 := silent_compose M c21 c22 c120 3047 2080685 h21 tail22
  have tail20 : silent M 2086103 c20 = some c120 := silent_compose M c20 c21 c120 2371 2083732 h20 tail21
  have tail19 : silent M 2087698 c19 = some c120 := silent_compose M c19 c20 c120 1595 2086103 h19 tail20
  have tail18 : silent M 2088769 c18 = some c120 := silent_compose M c18 c19 c120 1071 2087698 h18 tail19
  have tail17 : silent M 2089701 c17 = some c120 := silent_compose M c17 c18 c120 932 2088769 h17 tail18
  have tail16 : silent M 2096440 c16 = some c120 := silent_compose M c16 c17 c120 6739 2089701 h16 tail17
  have tail15 : silent M 2102067 c15 = some c120 := silent_compose M c15 c16 c120 5627 2096440 h15 tail16
  have tail14 : silent M 2107506 c14 = some c120 := silent_compose M c14 c15 c120 5439 2102067 h14 tail15
  have tail13 : silent M 2112270 c13 = some c120 := silent_compose M c13 c14 c120 4764 2107506 h13 tail14
  have tail12 : silent M 2116357 c12 = some c120 := silent_compose M c12 c13 c120 4087 2112270 h12 tail13
  have tail11 : silent M 2119768 c11 = some c120 := silent_compose M c11 c12 c120 3411 2116357 h11 tail12
  have tail10 : silent M 2122323 c10 = some c120 := silent_compose M c10 c11 c120 2555 2119768 h10 tail11
  have tail9 : silent M 2124434 c9 = some c120 := silent_compose M c9 c10 c120 2111 2122323 h9 tail10
  have tail8 : silent M 2125870 c8 = some c120 := silent_compose M c8 c9 c120 1436 2124434 h8 tail9
  have tail7 : silent M 2126629 c7 = some c120 := silent_compose M c7 c8 c120 759 2125870 h7 tail8
  have tail6 : silent M 2127956 c6 = some c120 := silent_compose M c6 c7 c120 1327 2126629 h6 tail7
  have tail5 : silent M 2130067 c5 = some c120 := silent_compose M c5 c6 c120 2111 2127956 h5 tail6
  have tail4 : silent M 2131503 c4 = some c120 := silent_compose M c4 c5 c120 1436 2130067 h4 tail5
  have tail3 : silent M 2132262 c3 = some c120 := silent_compose M c3 c4 c120 759 2131503 h3 tail4
  have tail2 : silent M 2132829 c2 = some c120 := silent_compose M c2 c3 c120 567 2132262 h2 tail3
  have tail1 : silent M 2133276 c1 = some c120 := silent_compose M c1 c2 c120 447 2132829 h1 tail2
  have tail0 : silent M 2133492 c0 = some c120 := silent_compose M c0 c1 c120 216 2133276 h0 tail1
  exact tail0

/-- Exact numeric endpoint of the first blank-start bootstrap. -/
theorem bootstrap_shape (M : Machine 285) (rows : Rows M) :
    silent M 2133492 ⟨A,0,0,false,0⟩ = some ⟨exit,(-2 : Int),rep4 1910,true,30⟩ := by
  have h := bootstrap M rows
  rw [final_shape] at h
  exact h

end Shared.PNP.Record285.BootstrapTraceProof
