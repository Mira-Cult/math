import Shared.Codes.TM2Primcodable

/-! Primitive-recursive decomposition of the existing numeric statement
syntax. A scanner splits the left branch from its following suffix, so both
children can be recovered uniformly from a runtime statement. The resulting
view does not itself execute the statement or charge bit-operation costs. -/
namespace Shared.Codes.TM2Decompose
open Shared.Codes.TM2Statements Shared.Codes.TM2Scanner Shared.Codes.TM2Primcodable

/-- Decode one leading statement and retain its unconsumed suffix. -/
def split (xs : List Nat) : Option (Code × List Nat) :=
  match scan xs.length xs with
  | some (0,rest) => (decodeTokens (xs.take (xs.length - rest.length))).map fun q => (q,rest)
  | _ => none

theorem split_primrec : Primrec split := by
  have hs : Primrec (fun xs : List Nat => scan xs.length xs) :=
    scan_primrec.comp (Primrec.pair Primrec.list_length Primrec.id)
  have hl : Primrec (fun p : List Nat × (Nat × List Nat) => p.1.length - p.2.2.length) :=
    Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst)
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec (fun p : List Nat × (Nat × List Nat) => p.1.take (p.1.length-p.2.2.length)) :=
    Primrec.list_take.comp hl Primrec.fst
  have hd := decodeTokens_primrec.comp ht
  have hp : Primrec₂ (fun (p : List Nat × (Nat × List Nat)) (q : Code) => (q,p.2.2)) :=
    (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).to₂
  have hm := Primrec.option_map hd hp
  have hf := Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)) hm
    (Primrec.const (none : Option (Code × List Nat)))
  have h := Primrec.option_casesOn hs (Primrec.const none) hf.to₂
  apply h.of_eq
  intro xs
  unfold split
  cases hn : scan xs.length xs with
  | none => rfl
  | some p => rcases p with ⟨n,rest⟩; cases n <;> rfl

theorem split_tokens (q : Code) (suffix : List Nat) : split (tokens q ++ suffix) = some (q,suffix) := by
  unfold split
  have hb : nodeCount q ≤ (tokens q ++ suffix).length := by
    have := nodeCount_le_length q
    simp only [List.length_append]
    omega
  rw [scan_tokens q suffix _ hb]
  simp [decodeTokens_tokens]

def tag (xs : List Nat) : Nat := (xs[0]?).getD 7

def first (xs : List Nat) : Option Code :=
  if tag xs = 2 ∨ tag xs = 3 ∨ tag xs = 4 then decodeTokens (xs.drop 3)
  else if tag xs = 5 then decodeTokens (xs.drop 2)
  else if tag xs = 6 then (split (xs.drop 2)).map Prod.fst
  else none

def second (xs : List Nat) : Option Code :=
  if tag xs = 6 then (split (xs.drop 2)).bind fun p => decodeTokens p.2 else none

theorem tag_primrec : Primrec tag :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0)) (Primrec.const 7)

theorem first_primrec : Primrec first := by
  have he (n : Nat) : PrimrecPred (fun xs : List Nat => tag xs = n) := Primrec.eq.comp tag_primrec (Primrec.const n)
  have hd (n : Nat) : Primrec (fun xs : List Nat => decodeTokens (xs.drop n)) :=
    decodeTokens_primrec.comp (Primrec.list_drop.comp (Primrec.const n) Primrec.id)
  have hs : Primrec (fun xs : List Nat => split (xs.drop 2)) :=
    split_primrec.comp (Primrec.list_drop.comp (Primrec.const 2) Primrec.id)
  have hm : Primrec (fun xs : List Nat => (split (xs.drop 2)).map Prod.fst) :=
    Primrec.option_map hs (Primrec.fst.comp Primrec.snd).to₂
  exact Primrec.ite (PrimrecPred.or (he 2) (PrimrecPred.or (he 3) (he 4))) (hd 3)
    (Primrec.ite (he 5) (hd 2) (Primrec.ite (he 6) hm (Primrec.const none)))

theorem second_primrec : Primrec second := by
  have he : PrimrecPred (fun xs : List Nat => tag xs = 6) := Primrec.eq.comp tag_primrec (Primrec.const 6)
  have hs : Primrec (fun xs : List Nat => split (xs.drop 2)) :=
    split_primrec.comp (Primrec.list_drop.comp (Primrec.const 2) Primrec.id)
  have hb : Primrec₂ (fun (_ : List Nat) (p : Code × List Nat) => decodeTokens p.2) :=
    (decodeTokens_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.ite he (Primrec.option_bind hs hb) (Primrec.const none)

def child₁ : Code → Option Code
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => some q
  | .branch _ a _ => some a
  | _ => none

def child₂ : Code → Option Code
  | .branch _ _ b => some b
  | _ => none

theorem first_tokens (q : Code) : first (tokens q) = child₁ q := by
  cases q <;> simp [first, tag, tokens, child₁, decodeTokens_tokens, split_tokens]

theorem second_tokens (q : Code) : second (tokens q) = child₂ q := by
  cases q <;> simp [second, tag, tokens, child₂, decodeTokens_tokens, split_tokens]

theorem child₁_primrec : Primrec child₁ :=
  (first_primrec.comp tokens_primrec).of_eq first_tokens

theorem child₂_primrec : Primrec child₂ :=
  (second_primrec.comp tokens_primrec).of_eq second_tokens

/-- The root tag and two header slots. Unused slots are ignored by each
constructor; for short headers they can contain tokens of the first child. -/
def rootTag (q : Code) : Nat := tag (tokens q)
def slot₁ (q : Code) : Nat := ((tokens q)[1]?).getD 0
def slot₂ (q : Code) : Nat := ((tokens q)[2]?).getD 0

theorem rootTag_primrec : Primrec rootTag := tag_primrec.comp tokens_primrec

theorem slot₁_primrec : Primrec slot₁ := by
  exact (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 1))
    (Primrec.const 0)).comp tokens_primrec

theorem slot₂_primrec : Primrec slot₂ := by
  exact (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.id (Primrec.const 2))
    (Primrec.const 0)).comp tokens_primrec

@[simp] theorem rootTag_halt : rootTag .halt = 0 := rfl
@[simp] theorem rootTag_goto (t) : rootTag (.goto t) = 1 := rfl
@[simp] theorem rootTag_push (k t q) : rootTag (.push k t q) = 2 := rfl
@[simp] theorem rootTag_peek (k t q) : rootTag (.peek k t q) = 3 := rfl
@[simp] theorem rootTag_pop (k t q) : rootTag (.pop k t q) = 4 := rfl
@[simp] theorem rootTag_load (t q) : rootTag (.load t q) = 5 := rfl
@[simp] theorem rootTag_branch (t a b) : rootTag (.branch t a b) = 6 := rfl

@[simp] theorem slot₁_goto (t) : slot₁ (.goto t) = Encodable.encode t := rfl
@[simp] theorem slot₁_push (k t q) : slot₁ (.push k t q) = k := rfl
@[simp] theorem slot₁_peek (k t q) : slot₁ (.peek k t q) = k := rfl
@[simp] theorem slot₁_pop (k t q) : slot₁ (.pop k t q) = k := rfl
@[simp] theorem slot₁_load (t q) : slot₁ (.load t q) = Encodable.encode t := rfl
@[simp] theorem slot₁_branch (t a b) : slot₁ (.branch t a b) = Encodable.encode t := rfl
@[simp] theorem slot₂_push (k t q) : slot₂ (.push k t q) = Encodable.encode t := rfl
@[simp] theorem slot₂_peek (k t q) : slot₂ (.peek k t q) = Encodable.encode t := rfl
@[simp] theorem slot₂_pop (k t q) : slot₂ (.pop k t q) = Encodable.encode t := rfl

/-- A uniform primitive-recursive view of the constructor, numeric headers,
and its immediate children, for use by a small-step interpreter. -/
abbrev View := Nat × Nat × Nat × Option Code × Option Code

def view (q : Code) : View := (rootTag q, slot₁ q, slot₂ q, child₁ q, child₂ q)

theorem view_primrec : Primrec view :=
  Primrec.pair rootTag_primrec (Primrec.pair slot₁_primrec
    (Primrec.pair slot₂_primrec (Primrec.pair child₁_primrec child₂_primrec)))

example : child₁ (.branch [] .halt (.goto [2])) = some .halt := rfl
example : child₂ (.branch [] .halt (.goto [2])) = some (.goto [2]) := rfl
example : split [0,0] = some (.halt,[0]) := by
  simpa [tokens] using split_tokens .halt [0]

end Shared.Codes.TM2Decompose
