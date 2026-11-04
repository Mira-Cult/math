import Shared.PNP.Record285.PythonControlRelocation

/-! Generic one-instruction relocation for the shared typed decoder. Explicit
row, edge, and settled-stack premises are supplied by the finite certificate;
this theorem is not itself an unbounded execution correspondence. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationStep
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation

def Matched : Status → Status → Prop
  | .fault,.fault => True
  | .live r,.live c => r.store=c.store ∧ c.pc=r.pc+47 ∧
      ∃ inner, r.loops=inner++referenceBase ∧ c.loops=inner.map shiftLoop++candidateBase
  | _,_ => False

def Allowed : Line → Prop
  | .while_ _ _ | .if_ _ _ | .else_ _ | .assign _ _ _ |
    .assignMany _ _ _ | .aug _ _ _ _ => True
  | _ => False

def Edges (pc : Nat) : Line → Prop
  | .while_ level _ => seek code (pc+1) level+47=seek code (pc+47+1) (level-4)
  | .if_ level _ => jumpFalse code pc level+47=jumpFalse code (pc+47) (level-4)
  | .else_ level => seek code (pc+1) level+47=seek code (pc+47+1) (level-4)
  | _ => True

/-- Equal settled stores, matching rows and matching control edges produce
identical labels and related one-line successors, including paired faults. -/
theorem matched_step (pc : Nat) (s : Store) (inner : List Loop) (line : Line)
    (hrefSettle : settle pc (inner++referenceBase)=(pc,inner++referenceBase))
    (hcandSettle : settle (pc+47) (inner.map shiftLoop++candidateBase)=
      (pc+47,inner.map shiftLoop++candidateBase))
    (href : code[pc]?=some line) (hcand : code[pc+47]?=some (unindent line))
    (hallowed : Allowed line) (hedges : Edges pc line) :
    let r := step code (.live ⟨pc,s,inner++referenceBase⟩)
    let c := step code (.live ⟨pc+47,s,inner.map shiftLoop++candidateBase⟩)
    r.2=c.2 ∧ Matched r.1 c.1 := by
  cases line with
  | function n a => exact False.elim hallowed
  | blank => exact False.elim hallowed
  | call i n => exact False.elim hallowed
  | return_ i e => exact False.elim hallowed
  | break_ i => exact False.elim hallowed
  | while_ level e =>
    change seek code (pc+1) level+47=seek code (pc+47+1) (level-4) at hedges
    cases he : eval s e with
    | none => simp [step,hrefSettle,hcandSettle,href,hcand,unindent,he,Matched]
    | some v =>
      by_cases hz : v=0
      · simp [step,hrefSettle,hcandSettle,href,hcand,unindent,he,hz,Matched,advance,←hedges, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [step,hrefSettle,hcandSettle,href,hcand,unindent,he,hz,Matched,advance,←hedges, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        refine ⟨⟨pc,seek code (pc+1) level⟩::inner,rfl,?_⟩
        simp [shiftLoop, Nat.add_comm]
  | if_ level e =>
    change jumpFalse code pc level+47=jumpFalse code (pc+47) (level-4) at hedges
    cases he : eval s e with
    | none => simp [step,hrefSettle,hcandSettle,href,hcand,unindent,he,Matched]
    | some v =>
      by_cases hz : v=0
      · simp [step,hrefSettle,hcandSettle,href,hcand,unindent,he,hz,Matched,advance,←hedges, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [step,hrefSettle,hcandSettle,href,hcand,unindent,he,hz,Matched,advance,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  | else_ level =>
    change seek code (pc+1) level+47=seek code (pc+47+1) (level-4) at hedges
    simp [step,hrefSettle,hcandSettle,href,hcand,unindent,Matched,advance,←hedges]
  | assign level name e =>
    have hc : simple (.assign (level-4) name e) s = simple (.assign level name e) s := rfl
    cases he : simple (.assign level name e) s with
    | none => simp only [step,hrefSettle,hcandSettle,href,hcand,unindent,Prod.fst,Prod.snd,hc,he,Matched, true_and]
    | some v =>
      simp only [step,hrefSettle,hcandSettle,href,hcand,unindent,Prod.fst,Prod.snd,hc,he,Matched,advance]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | assignMany level names es =>
    have hc : simple (.assignMany (level-4) names es) s = simple (.assignMany level names es) s := rfl
    cases he : simple (.assignMany level names es) s with
    | none => simp only [step,hrefSettle,hcandSettle,href,hcand,unindent,Prod.fst,Prod.snd,hc,he,Matched, true_and]
    | some v =>
      simp only [step,hrefSettle,hcandSettle,href,hcand,unindent,Prod.fst,Prod.snd,hc,he,Matched,advance]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | aug level name op e =>
    have hc : simple (.aug (level-4) name op e) s = simple (.aug level name op e) s := rfl
    cases he : simple (.aug level name op e) s with
    | none => simp only [step,hrefSettle,hcandSettle,href,hcand,unindent,Prod.fst,Prod.snd,hc,he,Matched, true_and]
    | some v =>
      simp only [step,hrefSettle,hcandSettle,href,hcand,unindent,Prod.fst,Prod.snd,hc,he,Matched,advance]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Shared.PNP.Record285.PythonControlRelocationStep
