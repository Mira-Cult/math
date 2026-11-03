import Shared.Codes.TM2FixedComputability

/-! Uniform, primitive-recursive prefix scanning for numeric TM2 statements.

This checks tags, header lengths, and table decodes while counting pending
subtrees. It uses the existing statement tokens, not a new machine model.
Coverage and suffix rejection are proved below. `TM2ScannerSound` proves the
converse identification with the existing parser; the scanner does not itself
reconstruct a `Code` or execute statements. -/
namespace Shared.Codes.TM2Scanner
open Shared.Codes.TM2Statements Shared.Codes.FiniteTables

def tableAt₁ (xs : List Nat) (i : Nat) : Bool :=
  ((xs[i]?).bind decode₁).isSome

def tableAt₂ (xs : List Nat) (i : Nat) : Bool :=
  ((xs[i]?).bind decode₂).isSome

/-- Read a single prefix node, returning its number of children and the
unread suffix. A missing or malformed table fails. -/
def node (xs : List Nat) : Option (Nat × List Nat) :=
  let tag := (xs[0]?).getD 7
  if tag = 0 then some (0,xs.drop 1)
  else if tag = 1 ∧ tableAt₁ xs 1 then some (0,xs.drop 2)
  else if tag = 2 ∧ (xs[1]?).isSome ∧ tableAt₁ xs 2 then some (1,xs.drop 3)
  else if tag = 3 ∧ (xs[1]?).isSome ∧ tableAt₂ xs 2 then some (1,xs.drop 3)
  else if tag = 4 ∧ (xs[1]?).isSome ∧ tableAt₂ xs 2 then some (1,xs.drop 3)
  else if tag = 5 ∧ tableAt₁ xs 1 then some (1,xs.drop 2)
  else if tag = 6 ∧ tableAt₁ xs 1 then some (2,xs.drop 2)
  else none

abbrev State := Option (Nat × List Nat)

/-- The pending-node count is zero exactly after a complete tree has been
read. Success then freezes the suffix; malformed input remains failed. -/
def step : State → State
  | none => none
  | some (0,xs) => some (0,xs)
  | some (n+1,xs) => (node xs).map fun (children,rest) => (n+children,rest)

def scan (fuel : Nat) (xs : List Nat) : State := step^[fuel] (some (1,xs))

theorem tableAt₁_primrec : Primrec₂ tableAt₁ := by
  have h := Primrec.option_bind (Primrec.list_getElem? : Primrec₂ (fun (xs : List Nat) (i : Nat) => xs[i]?))
    (Primrec.decode.comp Primrec.snd : Primrec (fun p : (List Nat × Nat) × Nat => decode₁ p.2)).to₂
  exact (Primrec.option_isSome.comp h).to₂

theorem tableAt₂_primrec : Primrec₂ tableAt₂ := by
  have h := Primrec.option_bind (Primrec.list_getElem? : Primrec₂ (fun (xs : List Nat) (i : Nat) => xs[i]?))
    (Primrec.decode.comp Primrec.snd : Primrec (fun p : (List Nat × Nat) × Nat => decode₂ p.2)).to₂
  exact (Primrec.option_isSome.comp h).to₂

theorem node_primrec : Primrec node := by
  have htag : Primrec (fun xs : List Nat => (xs[0]?).getD 7) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0)) (Primrec.const 7)
  have htab1 (i : Nat) : PrimrecPred (fun xs : List Nat => tableAt₁ xs i = true) :=
    Primrec.eq.comp (tableAt₁_primrec.comp Primrec.id (Primrec.const i)) (Primrec.const true)
  have htab2 (i : Nat) : PrimrecPred (fun xs : List Nat => tableAt₂ xs i = true) :=
    Primrec.eq.comp (tableAt₂_primrec.comp Primrec.id (Primrec.const i)) (Primrec.const true)
  have hstk : PrimrecPred (fun xs : List Nat => (xs[1]?).isSome = true) :=
    Primrec.eq.comp (Primrec.option_isSome.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 1))) (Primrec.const true)
  have hres (n i : Nat) : Primrec (fun xs : List Nat => (some (n,xs.drop i) : Option (Nat × List Nat))) :=
    Primrec.option_some.comp (Primrec.pair (Primrec.const n) (Primrec.list_drop.comp (Primrec.const i) Primrec.id))
  have htagEq (i : Nat) : PrimrecPred (fun xs : List Nat => (xs[0]?).getD 7 = i) := Primrec.eq.comp htag (Primrec.const i)
  have h := Primrec.ite (htagEq 0) (hres 0 1)
    (Primrec.ite (PrimrecPred.and (htagEq 1) (htab1 1)) (hres 0 2)
    (Primrec.ite (PrimrecPred.and (htagEq 2) (PrimrecPred.and hstk (htab1 2))) (hres 1 3)
    (Primrec.ite (PrimrecPred.and (htagEq 3) (PrimrecPred.and hstk (htab2 2))) (hres 1 3)
    (Primrec.ite (PrimrecPred.and (htagEq 4) (PrimrecPred.and hstk (htab2 2))) (hres 1 3)
    (Primrec.ite (PrimrecPred.and (htagEq 5) (htab1 1)) (hres 1 2)
    (Primrec.ite (PrimrecPred.and (htagEq 6) (htab1 1)) (hres 2 2) (Primrec.const none)))))))
  exact h

theorem step_primrec : Primrec step := by
  have hm : Primrec (fun p : Nat × List Nat => (node p.2).map
      (fun z : Nat × List Nat => (p.1 - 1 + z.1,z.2))) := by
    have hf : Primrec₂ (fun (p : Nat × List Nat) (z : Nat × List Nat) => (p.1 - 1 + z.1,z.2)) :=
      (Primrec.pair (Primrec.nat_add.comp (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂
    exact Primrec.option_map (node_primrec.comp Primrec.snd) hf
  have hp : Primrec (fun p : Nat × List Nat => if p.1 = 0 then some p else
      (node p.2).map (fun z : Nat × List Nat => (p.1 - 1 + z.1,z.2))) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst : Primrec (fun p : Nat × List Nat => p.1)) (Primrec.const 0))
      (Primrec.option_some.comp Primrec.id) hm
  have h := Primrec.option_casesOn (Primrec.id : Primrec (fun s : State => s)) (Primrec.const none)
    (hp.comp Primrec.snd).to₂
  apply h.of_eq
  intro s
  cases s with
  | none => rfl
  | some p =>
    rcases p with ⟨n,xs⟩
    cases n <;> simp [step]

theorem scan_primrec : Primrec (fun p : Nat × List Nat => scan p.1 p.2) := by
  have hi : Primrec (fun p : Nat × List Nat => (some (1,p.2) : State)) :=
    Primrec.option_some.comp (Primrec.pair (Primrec.const 1) Primrec.snd)
  exact Primrec.nat_iterate Primrec.fst hi (step_primrec.comp Primrec.snd).to₂

def nodeCount : Code → Nat
  | .halt | .goto _ => 1
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => nodeCount q + 1
  | .branch _ a b => nodeCount a + nodeCount b + 1

theorem tableAt₁_encoded (t : List Nat) (suffix : List Nat) :
    tableAt₁ (Encodable.encode t :: suffix) 0 = true := by
  simp [tableAt₁, decode₁]
theorem tableAt₂_encoded (t : List (List Nat)) (suffix : List Nat) :
    tableAt₂ (Encodable.encode t :: suffix) 0 = true := by
  simp [tableAt₂, decode₂]

theorem step_halt (n : Nat) (xs : List Nat) : step (some (n+1,0::xs)) = some (n,xs) := by
  simp [step, node]

theorem step_goto (n : Nat) (t : List Nat) (xs : List Nat) :
    step (some (n+1,1::Encodable.encode t::xs)) = some (n,xs) := by
  simp [step, node, tableAt₁, decode₁]

theorem consume (q : Code) (n : Nat) (xs : List Nat) :
    step^[nodeCount q] (some (n+1,tokens q ++ xs)) = some (n,xs) := by
  induction q generalizing n xs with
  | halt => simpa [nodeCount, tokens] using step_halt n xs
  | goto t => simpa [nodeCount, tokens] using step_goto n t xs
  | push k t q ih =>
    simp only [nodeCount, tokens, List.cons_append, Function.iterate_succ_apply]
    simp only [step, node, tableAt₁, decode₁, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Encodable.encodek, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n xs
  | peek k t q ih =>
    simp only [nodeCount, tokens, List.cons_append, Function.iterate_succ_apply]
    simp only [step, node, tableAt₂, decode₂, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Encodable.encodek, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n xs
  | pop k t q ih =>
    simp only [nodeCount, tokens, List.cons_append, Function.iterate_succ_apply]
    simp only [step, node, tableAt₂, decode₂, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Encodable.encodek, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n xs
  | load t q ih =>
    simp only [nodeCount, tokens, List.cons_append, Function.iterate_succ_apply]
    simp only [step, node, tableAt₁, decode₁, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Encodable.encodek, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n xs
  | branch t a b iha ihb =>
    simp only [nodeCount, tokens, List.cons_append, Function.iterate_succ_apply]
    simp only [step, node, tableAt₁, decode₁, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Encodable.encodek, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    rw [Nat.add_comm (nodeCount a) (nodeCount b), Function.iterate_add_apply]
    rw [List.append_assoc]
    simpa [Nat.add_assoc] using (congrArg (step^[nodeCount b]) (iha (n+1) (tokens b ++ xs))).trans (ihb n xs)

theorem nodeCount_le_length (q : Code) : nodeCount q ≤ (tokens q).length := by
  induction q with
  | halt => simp [nodeCount, tokens]
  | goto t => simp [nodeCount, tokens]
  | push k t q ih => simp [nodeCount, tokens] at *; omega
  | peek k t q ih => simp [nodeCount, tokens] at *; omega
  | pop k t q ih => simp [nodeCount, tokens] at *; omega
  | load t q ih => simp [nodeCount, tokens] at *; omega
  | branch t a b iha ihb => simp [nodeCount, tokens] at *; omega

theorem scan_tokens (q : Code) (suffix : List Nat) (fuel : Nat)
    (h : nodeCount q ≤ fuel) : scan fuel (tokens q ++ suffix) = some (0,suffix) := by
  unfold scan
  have hf : fuel = (fuel - nodeCount q) + nodeCount q := by omega
  rw [hf, Function.iterate_add_apply]
  rw [show (some (1, tokens q ++ suffix) : State) = some (0+1,tokens q ++ suffix) by rfl, consume]
  exact Function.iterate_fixed (show step (some (0,suffix)) = some (0,suffix) from rfl) _

/-- Exhausting at most the total token count suffices on serialized input. -/
theorem scan_tokens_length (q : Code) : scan (tokens q).length (tokens q) = some (0,[]) := by
  simpa using scan_tokens q [] (tokens q).length (nodeCount_le_length q)

/-- A complete statement must consume every token; a suffix is not accepted. -/
def complete (xs : List Nat) : Bool := decide (scan xs.length xs = some (0,[]))

theorem complete_primrec : Primrec complete := by
  have h : Primrec (fun xs : List Nat => scan xs.length xs) :=
    scan_primrec.comp (Primrec.pair Primrec.list_length Primrec.id)
  unfold complete
  exact (Primrec.eq.comp h (Primrec.const (some (0,[]) : State))).decide

theorem complete_tokens (q : Code) : complete (tokens q) = true := by
  simp [complete, scan_tokens_length]

theorem complete_tokens_suffix (q : Code) (suffix : List Nat) (h : suffix ≠ []) :
    complete (tokens q ++ suffix) = false := by
  have hf : nodeCount q ≤ (tokens q ++ suffix).length := by
    simpa using Nat.le_trans (nodeCount_le_length q) (Nat.le_add_right (tokens q).length suffix.length)
  unfold complete
  rw [scan_tokens q suffix _ hf]
  simp [h]

/-- Decode a numeric list code and check that it is a complete prefix tree. -/
def check (n : Nat) : Bool := (Encodable.decode n : Option (List Nat)).any complete

theorem check_primrec : Primrec check := by
  have h := Primrec.option_casesOn (Primrec.decode : Primrec (Encodable.decode : Nat → Option (List Nat)))
    (Primrec.const false) (complete_primrec.comp Primrec.snd).to₂
  apply h.of_eq
  intro n
  unfold check
  cases (Encodable.decode n : Option (List Nat)) <;> rfl

theorem check_covers (q : Code) : check (Encodable.encode (tokens q)) = true := by
  simp [check, complete_tokens]

example : scan 1 [0] = some (0,[]) := by decide
example : scan 1 [2] = none := by decide
example : scan 1 [7] = none := by decide
example : scan 1 [0,0] = some (0,[0]) := by decide
example : scan 1 [6,Encodable.encode ([] : List Nat)] = some (2,[]) := by
  simp [scan, step, node, tableAt₁, decode₁]
example : scan 3 [6,Encodable.encode ([] : List Nat),0,0] = some (0,[]) := by
  simpa [tokens, nodeCount] using scan_tokens (.branch [] .halt .halt) [] 3 (by simp [nodeCount])

end Shared.Codes.TM2Scanner
