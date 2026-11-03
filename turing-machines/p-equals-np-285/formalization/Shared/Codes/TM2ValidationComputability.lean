import Shared.Codes.TM2Micro
import Shared.ComplexityBridge.CNFComputability

/-! Uniform primitive-recursive validation of complete numeric TM2 programs.
The traversal checks every node and both branches, and agrees with the existing
`valid` and `programValid` definitions. It uses a finite token-length bound;
no polynomial bit-operation bound is asserted. -/
set_option maxHeartbeats 200000

namespace Shared.Codes.TM2ValidationComputability
open Shared.Codes.TM2Statements Shared.Codes.TM2StatementValidation Shared.Codes.TM2Scanner
open Shared.Codes.TM2Decompose Shared.Codes.TM2Micro Shared.Codes.FiniteTables Shared.Codes.TM2Primcodable
open Shared.Codes.TM2Program

abbrev Params := Nat × Nat × Nat × Nat

theorem unaryValid_primrec : Primrec (fun p : (List Nat × Nat) × Nat => unaryValid p.1.1 p.1.2 p.2) := by
  let P := (List Nat × Nat) × Nat
  have hlookup : Primrec (fun p : P × Nat => lookup p.1.1.1 p.2) :=
    lookup_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have hyes : Primrec₂ (fun (p : P × Nat) (x : Nat) => decide (x < p.1.2)) :=
    (Primrec.nat_lt.decide.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).to₂
  have ht : Primrec₂ (fun (p : P) (i : Nat) => match lookup p.1.1 i with
      | none => false | some x => decide (x < p.2)) := by
    have h := Primrec.option_casesOn hlookup (Primrec.const false) hyes
    apply h.to₂.of_eq
    intro p i
    cases lookup p.1.1 i <;> rfl
  have h := Shared.ComplexityBridge.CNF.list_all_primrec
    (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)) ht
  apply h.of_eq
  intro p
  unfold unaryValid
  congr 1
  funext i
  cases lookup p.1.1 i <;> rfl

theorem binaryValid_primrec : Primrec (fun p : ((List (List Nat) × Nat) × Nat) × Nat =>
    binaryValid p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  let P := ((List (List Nat) × Nat) × Nat) × Nat
  have hp : Primrec (fun x : (P × Nat) × Nat => x.1.1) := Primrec.fst.comp Primrec.fst
  have htable : Primrec (fun x : (P × Nat) × Nat => x.1.1.1.1.1) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).comp hp
  have hrow : Primrec (fun x : (P × Nat) × Nat => x.1.2) := Primrec.snd.comp Primrec.fst
  have hpair : Primrec (fun x : (P × Nat) × Nat => ((x.1.1.1.1.1,x.1.2),x.2)) :=
    Primrec.pair (Primrec.pair htable hrow) Primrec.snd
  have hlookup : Primrec (fun x : (P × Nat) × Nat => lookup₂ x.1.1.1.1.1 x.1.2 x.2) := by
    have h := lookup₂_primrec.comp hpair
    apply h.of_eq
    intro x
    rfl
  have hyes : Primrec₂ (fun (x : (P × Nat) × Nat) (v : Nat) => decide (v < x.1.1.2)) :=
    (Primrec.nat_lt.decide.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))).to₂
  have hcell : Primrec₂ (fun (x : P × Nat) (j : Nat) => match lookup₂ x.1.1.1.1 x.2 j with
      | none => false | some v => decide (v < x.1.2)) := by
    have h := Primrec.option_casesOn hlookup (Primrec.const false) hyes
    apply h.to₂.of_eq
    intro x j
    cases lookup₂ x.1.1.1.1 x.2 j <;> rfl
  have hrow : Primrec₂ (fun (p : P) (i : Nat) => (List.range p.1.2).all fun j =>
      match lookup₂ p.1.1.1 i j with | none => false | some v => decide (v < p.2)) := by
    apply (Shared.ComplexityBridge.CNF.list_all_primrec
      (Primrec.list_range.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) hcell).to₂
  have h := Shared.ComplexityBridge.CNF.list_all_primrec
    (Primrec.list_range.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) hrow
  apply h.of_eq
  intro p
  unfold binaryValid
  congr 1
  funext i
  congr 1
  funext j
  cases lookup₂ p.1.1.1 i j <;> rfl

/-- Check just the root node; recursive children are checked separately. -/
def rootCheck (p : Params) (q : Code) : Bool :=
  if rootTag q = 0 then true
  else if rootTag q = 1 then unaryValid (table1 (slot₁ q)) p.2.1 p.2.2.2
  else if rootTag q = 2 then (slot₁ q < p.1) && unaryValid (table1 (slot₂ q)) p.2.1 p.2.2.1
  else if rootTag q = 3 then (slot₁ q < p.1) && binaryValid (table2 (slot₂ q)) p.2.1 (p.2.2.1+1) p.2.1
  else if rootTag q = 4 then (slot₁ q < p.1) && binaryValid (table2 (slot₂ q)) p.2.1 (p.2.2.1+1) p.2.1
  else if rootTag q = 5 then unaryValid (table1 (slot₁ q)) p.2.1 p.2.1
  else if rootTag q = 6 then unaryValid (table1 (slot₁ q)) p.2.1 2
  else false

theorem rootCheck_primrec : Primrec₂ rootCheck := by
  let A := Params × Code
  have hks : Primrec (fun a : A => a.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun a : A => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hy : Primrec (fun a : A => a.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hl : Primrec (fun a : A => a.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have h1 : Primrec (fun a : A => table1 (slot₁ a.2)) := table1_primrec.comp (slot₁_primrec.comp Primrec.snd)
  have h2 : Primrec (fun a : A => table1 (slot₂ a.2)) := table1_primrec.comp (slot₂_primrec.comp Primrec.snd)
  have h3 : Primrec (fun a : A => table2 (slot₂ a.2)) := table2_primrec.comp (slot₂_primrec.comp Primrec.snd)
  have hgoto : Primrec (fun a : A => unaryValid (table1 (slot₁ a.2)) a.1.2.1 a.1.2.2.2) := by
    have h := unaryValid_primrec.comp (Primrec.pair (Primrec.pair h1 hs) hl)
    exact h.of_eq (by intro a; rfl)
  have hpush : Primrec (fun a : A => unaryValid (table1 (slot₂ a.2)) a.1.2.1 a.1.2.2.1) := by
    have h := unaryValid_primrec.comp (Primrec.pair (Primrec.pair h2 hs) hy)
    exact h.of_eq (by intro a; rfl)
  have hbin : Primrec (fun a : A => binaryValid (table2 (slot₂ a.2)) a.1.2.1 (a.1.2.2.1+1) a.1.2.1) := by
    have h := binaryValid_primrec.comp (Primrec.pair (Primrec.pair (Primrec.pair h3 hs) (Primrec.succ.comp hy)) hs)
    exact h.of_eq (by intro a; rfl)
  have hload : Primrec (fun a : A => unaryValid (table1 (slot₁ a.2)) a.1.2.1 a.1.2.1) := by
    have h := unaryValid_primrec.comp (Primrec.pair (Primrec.pair h1 hs) hs)
    exact h.of_eq (by intro a; rfl)
  have hbranch : Primrec (fun a : A => unaryValid (table1 (slot₁ a.2)) a.1.2.1 2) := by
    have h := unaryValid_primrec.comp (Primrec.pair (Primrec.pair h1 hs) (Primrec.const 2))
    exact h.of_eq (by intro a; rfl)
  have hstack : Primrec (fun a : A => decide (slot₁ a.2 < a.1.1)) :=
    Primrec.nat_lt.decide.comp (slot₁_primrec.comp Primrec.snd) hks
  have htag (n : Nat) : PrimrecPred (fun a : A => rootTag a.2 = n) :=
    Primrec.eq.comp (rootTag_primrec.comp Primrec.snd) (Primrec.const n)
  have h := (Primrec.ite (htag 0) (Primrec.const true)
    (Primrec.ite (htag 1) hgoto
    (Primrec.ite (htag 2) (Primrec.and.comp hstack hpush)
    (Primrec.ite (htag 3) (Primrec.and.comp hstack hbin)
    (Primrec.ite (htag 4) (Primrec.and.comp hstack hbin)
    (Primrec.ite (htag 5) hload
    (Primrec.ite (htag 6) hbranch (Primrec.const false))))))))
  apply h.to₂.of_eq
  intro p q
  rfl

def children (q : Code) : List Code := (child₁ q).toList ++ (child₂ q).toList

theorem optionToList_primrec : Primrec (Option.toList : Option Code → List Code) := by
  have h := Primrec.option_casesOn (Primrec.id : Primrec (fun q : Option Code => q)) (Primrec.const [])
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])).to₂
  exact h.of_eq (by intro q; cases q <;> rfl)

theorem children_primrec : Primrec children :=
  Primrec.list_append.comp (optionToList_primrec.comp child₁_primrec) (optionToList_primrec.comp child₂_primrec)

/-- Process one pending node. The traversal includes both branch children. -/
def workStep (p : Params) (s : Bool × List Code) : Bool × List Code :=
  match s.2 with
  | [] => s
  | q :: rest => (s.1 && rootCheck p q, children q ++ rest)

theorem workStep_primrec : Primrec₂ workStep := by
  let A := Params × (Bool × List Code)
  have hl : Primrec (fun a : A => a.2.2) := Primrec.snd.comp Primrec.snd
  have hb : Primrec (fun a : A => a.2) := Primrec.snd
  have hv : Primrec (fun x : A × (Code × List Code) => x.1.2.1 && rootCheck x.1.1 x.2.1) :=
    Primrec.and.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (rootCheck_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  have hwork : Primrec (fun x : A × (Code × List Code) => children x.2.1 ++ x.2.2) :=
    Primrec.list_append.comp (children_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hc : Primrec₂ (fun (a : A) (x : Code × List Code) =>
      (a.2.1 && rootCheck a.1 x.1, children x.1 ++ x.2)) := (Primrec.pair hv hwork).to₂
  have h := Primrec.list_casesOn hl hb hc
  apply h.to₂.of_eq
  rintro p ⟨b,ls⟩
  cases ls <;> rfl

example (p : Params) (b : Bool) (k : Nat) (t : List Nat) (q : Code) (rest : List Code) :
    workStep p (b,.push k t q::rest) =
      (b && ((k < p.1) && unaryValid t p.2.1 p.2.2.1),q::rest) := by
  simp [workStep, rootCheck, table1, children, child₁, child₂]
  rfl

theorem consume (p : Params) (q : Code) (b : Bool) (rest : List Code) :
    (workStep p)^[nodeCount q] (b,q::rest) =
      (b && valid p.1 p.2.1 p.2.2.1 p.2.2.2 q,rest) := by
  induction q generalizing b rest with
  | halt => simp [nodeCount, workStep, rootCheck, children, child₁, child₂, valid]
  | goto t => simp [nodeCount, workStep, rootCheck, table1, children, child₁, child₂, valid]
  | push k t q ih =>
    simp [nodeCount, Function.iterate_succ_apply, workStep, rootCheck, table1, children, child₁, child₂,
      valid, ih, Bool.and_assoc]
    rfl
  | peek k t q ih =>
    simp [nodeCount, Function.iterate_succ_apply, workStep, rootCheck, table2, children, child₁, child₂,
      valid, ih, Bool.and_assoc]
    rfl
  | pop k t q ih =>
    simp [nodeCount, Function.iterate_succ_apply, workStep, rootCheck, table2, children, child₁, child₂,
      valid, ih, Bool.and_assoc]
    rfl
  | load t q ih =>
    simp [nodeCount, Function.iterate_succ_apply, workStep, rootCheck, table1, children, child₁, child₂,
      valid, ih, Bool.and_assoc]
  | branch t left right iha ihb =>
    simp only [nodeCount, Function.iterate_succ_apply]
    simp only [workStep, rootCheck, rootTag_branch, Nat.reduceEqDiff, ↓reduceIte,
      slot₁_branch, table1, Denumerable.ofNat_encode, children, child₁, child₂,
      Option.toList_some, List.cons_append]
    rw [Nat.add_comm (nodeCount left) (nodeCount right), Function.iterate_add_apply]
    rw [iha]
    simp only [List.nil_append, List.cons_append]
    rw [ihb]
    simp [valid, Bool.and_assoc]

/-- Traverse every node with an explicit finite token-length bound. -/
def validate (p : Params) (q : Code) : Bool :=
  ((workStep p)^[(tokens q).length] (true,[q])).1

theorem validate_primrec : Primrec₂ validate := by
  let A := Params × Code
  have hf : Primrec (fun a : A => (tokens a.2).length) :=
    Primrec.list_length.comp (tokens_primrec.comp Primrec.snd)
  have hi : Primrec (fun a : A => (true,[a.2])) :=
    Primrec.pair (Primrec.const true) (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  have hs : Primrec₂ (fun (a : A) (s : Bool × List Code) => workStep a.1 s) :=
    (workStep_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.fst.comp (Primrec.nat_iterate hf hi hs)).to₂

theorem validate_eq (p : Params) (q : Code) :
    validate p q = valid p.1 p.2.1 p.2.2.1 p.2.2.2 q := by
  unfold validate
  have hle := nodeCount_le_length q
  have hf : (tokens q).length = ((tokens q).length-nodeCount q) + nodeCount q := by omega
  rw [hf, Function.iterate_add_apply, consume]
  have hfix : ∀ b : Bool, workStep p (b,[]) = (b,[]) := by intro b; rfl
  rw [Function.iterate_fixed (hfix _) _]
  simp

theorem valid_uniform_primrec : Primrec (fun x : Params × Code =>
    valid x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2) := by
  have h : Primrec (fun x : Params × Code => validate x.1 x.2) := validate_primrec
  apply h.of_eq
  rintro ⟨p,q⟩
  exact validate_eq p q

theorem programValid_primrec : Primrec (fun x : Program × (Nat × Nat × Nat) =>
    programValid x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let A := Program × (Nat × Nat × Nat)
  have hl : Primrec (fun a : A => a.1.length) := Primrec.list_length.comp Primrec.fst
  have hk : Primrec (fun a : A => a.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun a : A => a.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hy : Primrec (fun a : A => a.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp : Primrec (fun a : A => ((a.2.1,a.2.2.1,a.2.2.2,a.1.length) : Params)) :=
    Primrec.pair hk (Primrec.pair hs (Primrec.pair hy hl))
  have hv : Primrec₂ (fun (a : A) (q : Code) => valid a.2.1 a.2.2.1 a.2.2.2 a.1.length q) :=
    (valid_uniform_primrec.comp (Primrec.pair (hp.comp Primrec.fst) Primrec.snd)).to₂
  exact Shared.ComplexityBridge.CNF.list_all_primrec Primrec.fst hv

example : validate (1,1,1,1) (.branch [0] .halt (.goto [])) = false := by
  simp [validate_eq, valid, unaryValid, Shared.Codes.FiniteTables.lookup]
example : validate (1,1,1,1) (.branch [0] .halt (.goto [0])) = true := by
  simp [validate_eq, valid, unaryValid, Shared.Codes.FiniteTables.lookup]

end Shared.Codes.TM2ValidationComputability
