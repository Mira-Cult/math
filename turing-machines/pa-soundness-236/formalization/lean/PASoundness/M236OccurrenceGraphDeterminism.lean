import PASoundness.M236OccurrenceGraphEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def incRegister (op : String) : Option (Fin 9) :=
  if op = "3.scratch.copy.inc" then some 0 else
  if op = "3.k.stage.inc" then some 1 else
  if op = "3.k.rest.inc" then some 2 else
  if op = "3.k.count.inc" then some 3 else
  if op = "3.k.top.inc" then some 4 else
  if op = "3.k.env.inc" then some 5 else
  if op = "3.k.a.inc" then some 6 else
  if op = "3.k.b.inc" then some 7 else
  if op = "3.k.c.inc" then some 8 else
  none

def decRegister (op : String) : Option (Fin 9) :=
  if op = "3.scratch.copy.decnz" then some 0 else
  if op = "3.k.stage.decnz" then some 1 else
  if op = "3.k.rest.decnz" then some 2 else
  if op = "3.k.count.decnz" then some 3 else
  if op = "3.k.top.decnz" then some 4 else
  if op = "3.k.env.decnz" then some 5 else
  if op = "3.k.a.decnz" then some 6 else
  if op = "3.k.b.decnz" then some 7 else
  if op = "3.k.c.decnz" then some 8 else
  none

def nextIndex (op : String) (dest : Nat) (extra : Option Nat)
    (bank : RegisterMachine.Bank 9) : Nat :=
  match decRegister op, extra with
  | some r, some zeroDest => if bank r = 0 then zeroDest else dest
  | _, _ => dest

theorem branch_index (edge : Grammar.Edge) (op : String) (bank : RegisterMachine.Bank 9)
    (dest : Nat) (extra : Option Nat) (target : Nat)
    (hlabel : GraphLabel edge op) (hbranch : GraphBranch edge bank dest extra target) :
    target = nextIndex op dest extra bank := by
  cases hbranch with
  | inc r write bank dest extra =>
      fin_cases r <;> simp_all [GraphLabel, nextIndex, decRegister, Selector.registerNames]
  | positive r write bank dest extra v h =>
      cases extra <;> fin_cases r <;> simp_all [GraphLabel, nextIndex, decRegister, Selector.registerNames]
  | zero r write bank dest target h =>
      fin_cases r <;> simp_all [GraphLabel, nextIndex, decRegister, Selector.registerNames]
  | continue1 => simp_all [GraphLabel, nextIndex, decRegister]
  | continue2 => simp_all [GraphLabel, nextIndex, decRegister]
  | continue3 => simp_all [GraphLabel, nextIndex, decRegister]
  | break1 => simp_all [GraphLabel, nextIndex, decRegister]
  | break3 => simp_all [GraphLabel, nextIndex, decRegister]
  | emitContinue b => cases b <;> simp_all [GraphLabel, nextIndex, decRegister, Emit.emitName]
  | emitCleanup b => cases b <;> simp_all [GraphLabel, nextIndex, decRegister, Emit.emitName]
def nextBank (op : String) (bank : RegisterMachine.Bank 9) : RegisterMachine.Bank 9 :=
  match incRegister op, decRegister op with
  | some r, _ => (RegisterMachine.execute (.inc r) bank).bank
  | none, some r => (RegisterMachine.execute (.decNZ r) bank).bank
  | none, none => bank

def nextReserve (op : String) (bank : RegisterMachine.Bank 9) (reserve : List Nat) : List Nat :=
  match decRegister op with
  | some r => if bank r = 0 then reserve else reserve ++ [0]
  | none => reserve

theorem effect_registers (edge : Grammar.Edge) (op : String)
    (bank bank' : RegisterMachine.Bank 9) (reserve reserve' : List Nat) (events : List Bool)
    (hlabel : GraphLabel edge op) (heffect : BranchEffect edge bank reserve bank' reserve' events) :
    bank' = nextBank op bank ∧ reserve' = nextReserve op bank reserve := by
  cases heffect with
  | inc r write bank reserve =>
      fin_cases r <;> simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister, Selector.registerNames]
  | positive r write bank reserve v h =>
      fin_cases r <;> simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister, Selector.registerNames]
  | zero r write bank reserve h =>
      fin_cases r <;> simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister, Selector.registerNames, RegisterMachine.execute]
  | continue1 => simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister]
  | continue2 => simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister]
  | continue3 => simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister]
  | break1 => simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister]
  | break3 => simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister]
  | emitContinue b => cases b <;> simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister, Emit.emitName]
  | emitCleanup b => cases b <;> simp_all [GraphLabel, nextBank, nextReserve, incRegister, decRegister, Emit.emitName]

/-- The retained row data, interpreted as an executable register step. -/
def graphNext (a : GraphState) : Option (List Bool × GraphState) :=
  (sourceRows[a.index]?).map fun row =>
    let (op, dest, extra) := row
    (outputForOp op, ⟨nextIndex op dest extra a.registers,
      nextBank op a.registers, nextReserve op a.registers a.reserve⟩)

/-- Every relational graph step equals the explicit deterministic interpreter. -/
theorem witness_step_functional (a b : GraphState) (events : List Bool)
    (h : WitnessStep a b events) : graphNext a = some (events, b) := by
  obtain ⟨edge, op, dest, extra, _, hrow, hlabel, hbranch, heffect⟩ := h
  have hi := branch_index edge op a.registers dest extra b.index hlabel hbranch
  obtain ⟨hb, hr⟩ := effect_registers edge op a.registers b.registers a.reserve b.reserve events hlabel heffect
  have he := effect_output edge op a.registers b.registers a.reserve b.reserve events hlabel heffect
  unfold graphNext
  rw [hrow]
  simp only [Option.map_some]
  apply congrArg some
  apply Prod.ext he.symm
  cases b with
  | mk index registers reserve =>
    simp only at hi hb hr
    simp [← hi, ← hb, ← hr]

/-- The graph relation has at most one next state and output. -/
theorem witness_step_deterministic (a b c : GraphState) (events events' : List Bool)
    (h : WitnessStep a b events) (h' : WitnessStep a c events') :
    events = events' ∧ b = c := by
  have h1 := witness_step_functional a b events h
  have h2 := witness_step_functional a c events' h'
  have he := Option.some.inj (h1.symm.trans h2)
  exact Prod.mk.inj he

end PASoundness.M236.OccurrenceGraph
