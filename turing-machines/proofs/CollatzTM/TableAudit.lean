import CollatzTM.Machine12
import CollatzTM.Machine16

namespace CollatzTM.TableAudit

def instrCode (name : S → String) (i : Instr S) : String :=
  (if i.write then "1" else "0") ++ (match i.dir with | .L => "L" | .R => "R") ++
    (match i.next with | none => "Z" | some q => name q)

def state12Name : M12.State → String
  | .A => "A" | .B => "B" | .C => "C" | .D => "D" | .E => "E" | .F => "F"
  | .G => "G" | .H => "H" | .I => "I" | .J => "J" | .K => "K" | .L => "L"

def state16Name : M16.State → String
  | .A => "A" | .B => "B" | .C => "C" | .D => "D" | .E => "E" | .F => "F"
  | .G => "G" | .H => "H" | .I => "I" | .J => "J" | .K => "K" | .L => "L"
  | .M => "M" | .N => "N" | .O => "O" | .P => "P"

def states12 : List M12.State := [.A,.B,.C,.D,.E,.F,.G,.H,.I,.J,.K,.L]
def states16 : List M16.State := [.A,.B,.C,.D,.E,.F,.G,.H,.I,.J,.K,.L,.M,.N,.O,.P]

def tableCode (name : S → String) (states : List S) (δ : S → Bool → Instr S) : String :=
  String.intercalate "_" (states.map (fun q => instrCode name (δ q false) ++ instrCode name (δ q true)))

/-- The actual compiled transitions, re-encoded, are the exact supplied 12-state string. -/
theorem twelve_table_exact : tableCode state12Name states12 M12.delta =
    "1RH0RK_0RA1RC_0RB1RD_1RH1RE_1RB0RF_1RB1RG_0RD1RF_1LI1LI_0RK1LJ_0LI1LI_0RA0RL_0LZ1RG" := by decide

/-- The actual compiled transitions, re-encoded, are the exact supplied 16-state string. -/
theorem sixteen_table_exact : tableCode state16Name states16 M16.delta =
    "1RP1LA_0LC0LC_0RD1LC_1RP1RE_1LB0RF_1LG1RF_0RI0LH_1RE1LH_0LA0LJ_1LK1LJ_0RN0RL_1RM1RL_0LA1RI_0RO1RN_0RZ1LB_0LC1RP" := by decide

theorem twelve_states_complete (q : M12.State) : q ∈ states12 := by cases q <;> decide
theorem sixteen_states_complete (q : M16.State) : q ∈ states16 := by cases q <;> decide

theorem twelve_halt_transition (q : M12.State) (b : Bool) :
    (M12.delta q b).next = none ↔ q = .L ∧ b = false := by cases q <;> cases b <;> decide

theorem sixteen_halt_transition (q : M16.State) (b : Bool) :
    (M16.delta q b).next = none ↔ q = .O ∧ b = false := by cases q <;> cases b <;> decide

#print axioms twelve_table_exact
#print axioms sixteen_table_exact
#print axioms twelve_halt_transition
#print axioms sixteen_halt_transition

end CollatzTM.TableAudit
