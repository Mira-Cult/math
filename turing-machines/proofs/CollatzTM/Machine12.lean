import CollatzTM.Core

namespace CollatzTM.M12

inductive State where
  | A | B | C | D | E | F | G | H | I | J | K | L
  deriving DecidableEq, Repr

def tableString : String := "1RH0RK_0RA1RC_0RB1RD_1RH1RE_1RB0RF_1RB1RG_0RD1RF_1LI1LI_0RK1LJ_0LI1LI_0RA0RL_0LZ1RG"

def delta : State → Bool → Instr State
  | .A, false => ⟨true, .R, some .H⟩
  | .A, true => ⟨false, .R, some .K⟩
  | .B, false => ⟨false, .R, some .A⟩
  | .B, true => ⟨true, .R, some .C⟩
  | .C, false => ⟨false, .R, some .B⟩
  | .C, true => ⟨true, .R, some .D⟩
  | .D, false => ⟨true, .R, some .H⟩
  | .D, true => ⟨true, .R, some .E⟩
  | .E, false => ⟨true, .R, some .B⟩
  | .E, true => ⟨false, .R, some .F⟩
  | .F, false => ⟨true, .R, some .B⟩
  | .F, true => ⟨true, .R, some .G⟩
  | .G, false => ⟨false, .R, some .D⟩
  | .G, true => ⟨true, .R, some .F⟩
  | .H, false => ⟨true, .L, some .I⟩
  | .H, true => ⟨true, .L, some .I⟩
  | .I, false => ⟨false, .R, some .K⟩
  | .I, true => ⟨true, .L, some .J⟩
  | .J, false => ⟨false, .L, some .I⟩
  | .J, true => ⟨true, .L, some .I⟩
  | .K, false => ⟨false, .R, some .A⟩
  | .K, true => ⟨false, .R, some .L⟩
  | .L, false => ⟨false, .L, none⟩
  | .L, true => ⟨true, .R, some .G⟩

def blank : Config State := ⟨some .A, 0, fun _ => false⟩

end CollatzTM.M12
