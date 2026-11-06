import Shared.Codes.TM2Scanner

/-! The primitive-recursive scanner recognizes precisely the domain of the
existing numeric statement decoder. The proof reconstructs a prefix forest
from a successful scan and accounts for arbitrary decodable table codes.
`TM2Primcodable` uses this result to prove computability of decoded values;
no bit-cost bound follows here. -/
namespace Shared.Codes.TM2ScannerSound
open Shared.Codes.TM2Scanner Shared.Codes.TM2Statements Shared.Codes.FiniteTables

/-- A verified single-node prefix. Table encodings need not be canonical. -/
inductive Frame : List Nat → Nat → List Nat → Prop
  | halt (xs) : Frame (0::xs) 0 xs
  | goto (t xs v) (h : decode₁ t = some v) : Frame (1::t::xs) 0 xs
  | push (k t xs v) (h : decode₁ t = some v) : Frame (2::k::t::xs) 1 xs
  | peek (k t xs v) (h : decode₂ t = some v) : Frame (3::k::t::xs) 1 xs
  | pop (k t xs v) (h : decode₂ t = some v) : Frame (4::k::t::xs) 1 xs
  | load (t xs v) (h : decode₁ t = some v) : Frame (5::t::xs) 1 xs
  | branch (t xs v) (h : decode₁ t = some v) : Frame (6::t::xs) 2 xs

theorem node_sound {xs : List Nat} {k : Nat} {rest : List Nat}
    (h : node xs = some (k,rest)) : Frame xs k rest := by
  cases xs with
  | nil => simp [node] at h
  | cons tag xs =>
    have hlt : tag < 7 := by
      by_contra hh
      have h0 : tag ≠ 0 := by omega
      have h1 : tag ≠ 1 := by omega
      have h2 : tag ≠ 2 := by omega
      have h3 : tag ≠ 3 := by omega
      have h4 : tag ≠ 4 := by omega
      have h5 : tag ≠ 5 := by omega
      have h6 : tag ≠ 6 := by omega
      simp [node, h0, h1, h2, h3, h4, h5, h6] at h
    have hc : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [node] at h
      obtain ⟨rfl,rfl⟩ := h
      exact .halt _
    · cases xs with
      | nil => simp [node, tableAt₁] at h
      | cons t xs =>
        cases ht : decode₁ t with
        | none => simp [node, tableAt₁, ht] at h
        | some v =>
          simp [node, tableAt₁, ht] at h
          obtain ⟨rfl,rfl⟩ := h
          exact .goto t xs v ht
    · cases xs with
      | nil => simp [node] at h
      | cons z xs =>
        cases xs with
        | nil => simp [node, tableAt₁] at h
        | cons t xs =>
          cases ht : decode₁ t with
          | none => simp [node, tableAt₁, ht] at h
          | some v =>
            simp [node, tableAt₁, ht] at h
            obtain ⟨rfl,rfl⟩ := h
            exact .push z t xs v ht
    · cases xs with
      | nil => simp [node] at h
      | cons z xs =>
        cases xs with
        | nil => simp [node, tableAt₂] at h
        | cons t xs =>
          cases ht : decode₂ t with
          | none => simp [node, tableAt₂, ht] at h
          | some v =>
            simp [node, tableAt₂, ht] at h
            obtain ⟨rfl,rfl⟩ := h
            exact .peek z t xs v ht
    · cases xs with
      | nil => simp [node] at h
      | cons z xs =>
        cases xs with
        | nil => simp [node, tableAt₂] at h
        | cons t xs =>
          cases ht : decode₂ t with
          | none => simp [node, tableAt₂, ht] at h
          | some v =>
            simp [node, tableAt₂, ht] at h
            obtain ⟨rfl,rfl⟩ := h
            exact .pop z t xs v ht
    · cases xs with
      | nil => simp [node, tableAt₁] at h
      | cons t xs =>
        cases ht : decode₁ t with
        | none => simp [node, tableAt₁, ht] at h
        | some v =>
          simp [node, tableAt₁, ht] at h
          obtain ⟨rfl,rfl⟩ := h
          exact .load t xs v ht
    · cases xs with
      | nil => simp [node, tableAt₁] at h
      | cons t xs =>
        cases ht : decode₁ t with
        | none => simp [node, tableAt₁, ht] at h
        | some v =>
          simp [node, tableAt₁, ht] at h
          obtain ⟨rfl,rfl⟩ := h
          exact .branch t xs v ht

/-- Prefix grammar retaining the input table codes. -/
inductive Tree : List Nat → Code → List Nat → Prop
  | halt (xs) : Tree (0::xs) .halt xs
  | goto (t xs v) (h : decode₁ t = some v) : Tree (1::t::xs) (.goto v) xs
  | push (k t xs v q rest) (h : decode₁ t = some v) (child : Tree xs q rest) :
      Tree (2::k::t::xs) (.push k v q) rest
  | peek (k t xs v q rest) (h : decode₂ t = some v) (child : Tree xs q rest) :
      Tree (3::k::t::xs) (.peek k v q) rest
  | pop (k t xs v q rest) (h : decode₂ t = some v) (child : Tree xs q rest) :
      Tree (4::k::t::xs) (.pop k v q) rest
  | load (t xs v q rest) (h : decode₁ t = some v) (child : Tree xs q rest) :
      Tree (5::t::xs) (.load v q) rest
  | branch (t xs v a b mid rest) (h : decode₁ t = some v)
      (left : Tree xs a mid) (right : Tree mid b rest) :
      Tree (6::t::xs) (.branch v a b) rest

inductive Forest : Nat → List Nat → List Nat → Prop
  | nil (xs) : Forest 0 xs xs
  | cons {n xs mid rest q} (tree : Tree xs q mid) (forest : Forest n mid rest) :
      Forest (n+1) xs rest

theorem frame_forest {xs rest suffix k n} (frame : Frame xs k rest)
    (forest : Forest (n+k) rest suffix) : Forest (n+1) xs suffix := by
  cases frame with
  | halt xs => exact .cons (.halt _) (by simpa using forest)
  | goto t xs v h => exact .cons (.goto t _ v h) (by simpa using forest)
  | push z t xs v h =>
    cases forest with
    | cons tree tail => exact .cons (.push z t _ v _ _ h tree) tail
  | peek z t xs v h =>
    cases forest with
    | cons tree tail => exact .cons (.peek z t _ v _ _ h tree) tail
  | pop z t xs v h =>
    cases forest with
    | cons tree tail => exact .cons (.pop z t _ v _ _ h tree) tail
  | load t xs v h =>
    cases forest with
    | cons tree tail => exact .cons (.load t _ v _ _ h tree) tail
  | branch t xs v h =>
    cases forest with
    | cons treeA tail =>
      cases tail with
      | cons treeB tail => exact .cons (.branch t _ v _ _ _ _ h treeA treeB) tail

theorem iterate_forest (fuel n : Nat) (xs suffix : List Nat)
    (h : step^[fuel] (some (n,xs)) = some (0,suffix)) : Forest n xs suffix := by
  induction fuel generalizing n xs with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    exact .nil _
  | succ fuel ih =>
    rw [Function.iterate_succ_apply] at h
    cases n with
    | zero =>
      simp only [step] at h
      have hh := ih 0 xs h
      cases hh with | nil _ => exact .nil _
    | succ n =>
      cases hn : node xs with
      | none =>
        simp only [step, hn, Option.map_none] at h
        have : step^[fuel] none = none := Function.iterate_fixed rfl fuel
        rw [this] at h
        contradiction
      | some p =>
        rcases p with ⟨k,rest⟩
        have hframe := node_sound hn
        simp only [step, hn, Option.map_some] at h
        exact frame_forest hframe (ih (n+k) rest h)

theorem tree_length {xs q rest} (h : Tree xs q rest) : rest.length < xs.length := by
  induction h <;> simp_all <;> omega

theorem tree_parse {xs q rest} (h : Tree xs q rest) :
    ∀ fuel, xs.length ≤ fuel → parse fuel xs = some (q,rest) := by
  induction h with
  | halt xs =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f => rfl
  | goto t xs v ht =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f => simp [parse, ht]
  | push k t xs v q rest ht child ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hh : xs.length ≤ f := by simp at hf; omega
      simp [parse, ht, ih f hh]
  | peek k t xs v q rest ht child ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hh : xs.length ≤ f := by simp at hf; omega
      simp [parse, ht, ih f hh]
  | pop k t xs v q rest ht child ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hh : xs.length ≤ f := by simp at hf; omega
      simp [parse, ht, ih f hh]
  | load t xs v q rest ht child ih =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hh : xs.length ≤ f := by simp at hf; omega
      simp [parse, ht, ih f hh]
  | branch t xs v a b mid rest ht left right ihl ihr =>
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hh : xs.length ≤ f := by simp at hf; omega
      have hmid : mid.length ≤ f := by have := tree_length left; omega
      simp [parse, ht, ihl f hh, ihr f hmid]

theorem scan_parse {fuel : Nat} {xs suffix : List Nat}
    (h : scan fuel xs = some (0,suffix)) : ∃ q, parse xs.length xs = some (q,suffix) := by
  have hf : Forest 1 xs suffix := iterate_forest fuel 1 xs suffix h
  cases hf with
  | cons tree forest =>
    cases forest with
    | nil _ => exact ⟨_, tree_parse tree _ (Nat.le_refl _)⟩

theorem complete_parse {xs : List Nat} (h : complete xs = true) :
    ∃ q, decodeTokens xs = some q := by
  have hs : scan xs.length xs = some (0,[]) := by simpa [complete] using h
  obtain ⟨q,hq⟩ := scan_parse hs
  exact ⟨q, by simp [decodeTokens, hq]⟩

theorem parse_tree (fuel : Nat) {xs q rest} (h : parse fuel xs = some (q,rest)) : Tree xs q rest := by
  induction fuel generalizing xs q rest with
  | zero => simp [parse] at h
  | succ f ih =>
    cases xs with
    | nil => simp [parse] at h
    | cons tag xs =>
      have hlt : tag < 7 := by
        by_contra hh
        have h0 : tag ≠ 0 := by omega
        have h1 : tag ≠ 1 := by omega
        have h2 : tag ≠ 2 := by omega
        have h3 : tag ≠ 3 := by omega
        have h4 : tag ≠ 4 := by omega
        have h5 : tag ≠ 5 := by omega
        have h6 : tag ≠ 6 := by omega
        simp [parse, h0, h1, h2, h3, h4, h5, h6] at h
      have hc : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [parse] at h
        obtain ⟨rfl,rfl⟩ := h
        exact .halt _
      · cases xs with
        | nil => simp [parse] at h
        | cons t xs =>
          cases ht : decode₁ t with
          | none => simp [parse, ht] at h
          | some v =>
            simp [parse, ht] at h
            obtain ⟨rfl,rfl⟩ := h
            exact .goto t xs v ht
      · cases xs with
        | nil => simp [parse] at h
        | cons k xs =>
          cases xs with
          | nil => simp [parse] at h
          | cons t xs =>
            cases ht : decode₁ t with
            | none => simp [parse, ht] at h
            | some v =>
              cases hp : parse f xs with
              | none => simp [parse, ht, hp] at h
              | some p =>
                rcases p with ⟨q',r⟩
                simp [parse, ht, hp] at h
                obtain ⟨rfl,rfl⟩ := h
                exact .push k t xs v q' r ht (ih hp)
      · cases xs with
        | nil => simp [parse] at h
        | cons k xs =>
          cases xs with
          | nil => simp [parse] at h
          | cons t xs =>
            cases ht : decode₂ t with
            | none => simp [parse, ht] at h
            | some v =>
              cases hp : parse f xs with
              | none => simp [parse, ht, hp] at h
              | some p =>
                rcases p with ⟨q',r⟩
                simp [parse, ht, hp] at h
                obtain ⟨rfl,rfl⟩ := h
                exact .peek k t xs v q' r ht (ih hp)
      · cases xs with
        | nil => simp [parse] at h
        | cons k xs =>
          cases xs with
          | nil => simp [parse] at h
          | cons t xs =>
            cases ht : decode₂ t with
            | none => simp [parse, ht] at h
            | some v =>
              cases hp : parse f xs with
              | none => simp [parse, ht, hp] at h
              | some p =>
                rcases p with ⟨q',r⟩
                simp [parse, ht, hp] at h
                obtain ⟨rfl,rfl⟩ := h
                exact .pop k t xs v q' r ht (ih hp)
      · cases xs with
        | nil => simp [parse] at h
        | cons t xs =>
          cases ht : decode₁ t with
          | none => simp [parse, ht] at h
          | some v =>
            cases hp : parse f xs with
            | none => simp [parse, ht, hp] at h
            | some p =>
              rcases p with ⟨q',r⟩
              simp [parse, ht, hp] at h
              obtain ⟨rfl,rfl⟩ := h
              exact .load t xs v q' r ht (ih hp)
      · cases xs with
        | nil => simp [parse] at h
        | cons t xs =>
          cases ht : decode₁ t with
          | none => simp [parse, ht] at h
          | some v =>
            cases hp : parse f xs with
            | none => simp [parse, ht, hp] at h
            | some p =>
              rcases p with ⟨a,mid⟩
              cases hr : parse f mid with
              | none => simp [parse, ht, hp, hr] at h
              | some p =>
                rcases p with ⟨b,r⟩
                simp [parse, ht, hp, hr] at h
                obtain ⟨rfl,rfl⟩ := h
                exact .branch t xs v a b mid r ht (ih hp) (ih hr)

theorem tree_consume {xs q rest} (tree : Tree xs q rest) (n : Nat) :
    step^[nodeCount q] (some (n+1,xs)) = some (n,rest) := by
  induction tree generalizing n with
  | halt xs => simpa [nodeCount] using step_halt n xs
  | goto t xs v ht =>
    simp [nodeCount, step, node, tableAt₁, ht]
  | push k t xs v q rest ht child ih =>
    simp only [nodeCount, Function.iterate_succ_apply]
    simp only [step, node, tableAt₁, List.getElem?_cons_zero, List.getElem?_cons_succ,
      ht, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n
  | peek k t xs v q rest ht child ih =>
    simp only [nodeCount, Function.iterate_succ_apply]
    simp only [step, node, tableAt₂, List.getElem?_cons_zero, List.getElem?_cons_succ,
      ht, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n
  | pop k t xs v q rest ht child ih =>
    simp only [nodeCount, Function.iterate_succ_apply]
    simp only [step, node, tableAt₂, List.getElem?_cons_zero, List.getElem?_cons_succ,
      ht, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n
  | load t xs v q rest ht child ih =>
    simp only [nodeCount, Function.iterate_succ_apply]
    simp only [step, node, tableAt₁, List.getElem?_cons_zero, List.getElem?_cons_succ,
      ht, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    exact ih n
  | branch t xs v a b mid rest ht left right iha ihb =>
    simp only [nodeCount, Function.iterate_succ_apply]
    simp only [step, node, tableAt₁, List.getElem?_cons_zero, List.getElem?_cons_succ,
      ht, Option.bind_some, Option.isSome_some, Option.getD_some, List.drop_succ_cons,
      List.drop_zero, Nat.reduceEqDiff, false_and, true_and, ↓reduceIte, Option.map_some]
    rw [Nat.add_comm (nodeCount a) (nodeCount b), Function.iterate_add_apply]
    simpa [Nat.add_assoc] using (congrArg (step^[nodeCount b]) (iha (n+1))).trans (ihb n)

theorem tree_nodeCount_le {xs q rest} (tree : Tree xs q rest) : nodeCount q + rest.length ≤ xs.length := by
  induction tree with
  | halt xs => simp [nodeCount]; omega
  | goto t xs v ht => simp [nodeCount]; omega
  | push k t xs v q rest ht child ih => simp [nodeCount] at *; omega
  | peek k t xs v q rest ht child ih => simp [nodeCount] at *; omega
  | pop k t xs v q rest ht child ih => simp [nodeCount] at *; omega
  | load t xs v q rest ht child ih => simp [nodeCount] at *; omega
  | branch t xs v a b mid rest ht left right iha ihb => simp [nodeCount] at *; omega

theorem tree_scan {xs q rest} (tree : Tree xs q rest) (fuel : Nat)
    (h : nodeCount q ≤ fuel) : scan fuel xs = some (0,rest) := by
  unfold scan
  have hf : fuel = (fuel - nodeCount q) + nodeCount q := by omega
  rw [hf, Function.iterate_add_apply]
  rw [show (some (1,xs) : State) = some (0+1,xs) by rfl, tree_consume tree 0]
  exact Function.iterate_fixed (show step (some (0,rest)) = some (0,rest) from rfl) _

theorem parse_scan {fuel : Nat} {xs q rest} (h : parse fuel xs = some (q,rest)) :
    scan xs.length xs = some (0,rest) := by
  have ht := parse_tree fuel h
  apply tree_scan ht
  have := tree_nodeCount_le ht
  omega

theorem complete_iff_decode (xs : List Nat) : complete xs = true ↔ ∃ q, decodeTokens xs = some q := by
  constructor
  · exact complete_parse
  · rintro ⟨q,hq⟩
    unfold decodeTokens at hq
    cases hp : parse xs.length xs with
    | none => simp [hp] at hq
    | some p =>
      rcases p with ⟨r,suffix⟩
      cases suffix with
      | cons x suffix => simp [hp] at hq
      | nil =>
        have hs := parse_scan hp
        simpa [complete] using hs

theorem check_iff_decode (n : Nat) : check n = true ↔ ∃ q, Shared.Codes.TM2Statements.decode n = some q := by
  unfold check Shared.Codes.TM2Statements.decode
  change (Encodable.decode n : Option (List Nat)).any complete = true ↔
    ∃ q, ((Encodable.decode n : Option (List Nat)).bind decodeTokens) = some q
  cases h : (Encodable.decode n : Option (List Nat)) with
  | none => simp
  | some xs => simpa using complete_iff_decode xs

/-- The domain of the existing code decoder is primitive recursive. This is
not yet a computability theorem for its decoded value. -/
theorem decode_isSome_primrec : Primrec (fun n => (Shared.Codes.TM2Statements.decode n).isSome) := by
  apply check_primrec.of_eq
  intro n
  have h := check_iff_decode n
  cases hc : check n <;> cases hd : Shared.Codes.TM2Statements.decode n <;> simp_all

end Shared.Codes.TM2ScannerSound
