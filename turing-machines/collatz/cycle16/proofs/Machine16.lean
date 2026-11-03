import CollatzTM.Core

namespace CollatzTM.M16

inductive State where
  | A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P
  deriving DecidableEq, Repr

def tableString : String := "1RP1LA_0LC0LC_0RD1LC_1RP1RE_1LB0RF_1LG1RF_0RI0LH_1RE1LH_0LA0LJ_1LK1LJ_0RN0RL_1RM1RL_0LA1RI_0RO1RN_0RZ1LB_0LC1RP"

def delta : State → Bool → Instr State
  | .A, false => ⟨true, .R, some .P⟩
  | .A, true => ⟨true, .L, some .A⟩
  | .B, false => ⟨false, .L, some .C⟩
  | .B, true => ⟨false, .L, some .C⟩
  | .C, false => ⟨false, .R, some .D⟩
  | .C, true => ⟨true, .L, some .C⟩
  | .D, false => ⟨true, .R, some .P⟩
  | .D, true => ⟨true, .R, some .E⟩
  | .E, false => ⟨true, .L, some .B⟩
  | .E, true => ⟨false, .R, some .F⟩
  | .F, false => ⟨true, .L, some .G⟩
  | .F, true => ⟨true, .R, some .F⟩
  | .G, false => ⟨false, .R, some .I⟩
  | .G, true => ⟨false, .L, some .H⟩
  | .H, false => ⟨true, .R, some .E⟩
  | .H, true => ⟨true, .L, some .H⟩
  | .I, false => ⟨false, .L, some .A⟩
  | .I, true => ⟨false, .L, some .J⟩
  | .J, false => ⟨true, .L, some .K⟩
  | .J, true => ⟨true, .L, some .J⟩
  | .K, false => ⟨false, .R, some .N⟩
  | .K, true => ⟨false, .R, some .L⟩
  | .L, false => ⟨true, .R, some .M⟩
  | .L, true => ⟨true, .R, some .L⟩
  | .M, false => ⟨false, .L, some .A⟩
  | .M, true => ⟨true, .R, some .I⟩
  | .N, false => ⟨false, .R, some .O⟩
  | .N, true => ⟨true, .R, some .N⟩
  | .O, false => ⟨false, .R, none⟩
  | .O, true => ⟨true, .L, some .B⟩
  | .P, false => ⟨false, .L, some .C⟩
  | .P, true => ⟨true, .R, some .P⟩

def blank : Config State := ⟨some .A, 0, fun _ => false⟩

end CollatzTM.M16
