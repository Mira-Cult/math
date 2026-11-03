import Shared.PNP.Record285.ControlNextDispatch

/-! Prefix semantics for the byte-bound producer control grammar. Unlike
`walk`, a prefix may end at an internal node. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarPrefix
open Shared.PNP.Record285.Grammar

/-- Consume exactly a path, preserving an internal node when the input ends.
Reading past a leaf or a missing node fails. -/
def follow : Edge → List Bool → Option Edge
  | e, [] => some e
  | .node n, b::bs => (nodeEdge n b).bind (fun next => follow next bs)
  | _, _::_ => none

def valid (code : List Bool) : Prop := ∃ e, follow (.node rootIndex) code = some e

def bounded : Edge → Prop
  | .node n => n < 163
  | _ => True

theorem follow_append (e : Edge) (xs ys : List Bool) :
    follow e (xs++ys) = (follow e xs).bind (fun mid => follow mid ys) := by
  induction xs generalizing e with
  | nil => rfl
  | cons b bs ih =>
    cases e with
    | node n =>
      cases h : nodeEdge n b with
      | none => simp [follow,h]
      | some next => simpa only [List.cons_append,follow,h,Option.bind_some] using ih next
    | inc i => rfl
    | dec i => rfl
    | half i => rfl
    | beep => rfl
    | brk i => rfl
    | cont i => rfl

/-- Every successful complete grammar walk is the corresponding prefix walk. -/
theorem walk_follow (code : List Bool) (n : Nat) (e : Edge)
    (h : walk n code = some e) : follow (.node n) code = some e := by
  induction code generalizing n with
  | nil => simp [walk] at h
  | cons b bs ih =>
    cases hn : nodeEdge n b with
    | none => simp [walk,hn] at h
    | some found =>
      cases found with
      | node j =>
        have hh : walk j bs = some e := by simpa only [walk,hn] using h
        simpa only [follow,hn,Option.bind_some] using ih j hh
      | inc j =>
        cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | dec j =>
        cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | half j =>
        cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | beep =>
        cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | brk j =>
        cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | cont j =>
        cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption

/-- Successful prefix traversal never leaves the checked finite grammar. -/
theorem follow_bounded (code : List Bool) (e out : Edge) (he : bounded e)
    (h : follow e code = some out) : bounded out := by
  induction code generalizing e with
  | nil =>
    simp only [follow,Option.some.injEq] at h
    subst out
    exact he
  | cons b bs ih =>
    cases e with
    | node n =>
      cases hn : nodeEdge n b with
      | none => simp [follow,hn] at h
      | some next =>
        have hnext : bounded next := by
          cases next with
          | node j =>
            have hj := node_edge_decreases n b j he hn
            dsimp [bounded] at he ⊢
            omega
          | inc j => trivial
          | dec j => trivial
          | half j => trivial
          | beep => trivial
          | brk j => trivial
          | cont j => trivial
        have hh : follow next bs = some out := by simpa only [follow,hn,Option.bind_some] using h
        exact ih next hnext hh
    | inc i => simp [follow] at h
    | dec i => simp [follow] at h
    | half i => simp [follow] at h
    | beep => simp [follow] at h
    | brk i => simp [follow] at h
    | cont i => simp [follow] at h

/-- The backward numbering of the frozen grammar bounds every successful
path, including paths which stop at an internal node. -/
theorem follow_length_bound (code : List Bool) (n : Nat) (out : Edge) (hn : n < 163)
    (h : follow (.node n) code = some out) : code.length ≤ n+1 := by
  induction code generalizing n with
  | nil => simp
  | cons b bs ih =>
    cases he : nodeEdge n b with
    | none => simp [follow,he] at h
    | some next =>
      cases next with
      | node j =>
        have hj : j < n := node_edge_decreases n b j hn he
        have hs : follow (.node j) bs = some out := by simpa only [follow,he,Option.bind_some] using h
        have hl := ih j (by omega) hs
        simp only [List.length_cons]
        omega
      | inc j => cases bs <;> simp [follow,he] at h ⊢
      | dec j => cases bs <;> simp [follow,he] at h ⊢
      | half j => cases bs <;> simp [follow,he] at h ⊢
      | beep => cases bs <;> simp [follow,he] at h ⊢
      | brk j => cases bs <;> simp [follow,he] at h ⊢
      | cont j => cases bs <;> simp [follow,he] at h ⊢

theorem valid_length_bound (code : List Bool) (h : valid code) : code.length ≤ 163 := by
  obtain ⟨e,he⟩ := h
  simpa only [rootIndex] using follow_length_bound code 162 e (by decide) he

/-- A proper prefix of a successful traversal necessarily ends at a node. -/
theorem proper_prefix_node (e : Edge) (pre : List Bool) (b : Bool) (tail : List Bool)
    (out : Edge) (h : follow e (pre++b::tail) = some out) :
    ∃ n, follow e pre = some (.node n) := by
  rw [follow_append] at h
  cases hp : follow e pre with
  | none => simp [hp] at h
  | some mid =>
    cases mid with
    | node n => exact ⟨n,rfl⟩
    | inc i => simp [hp,follow] at h
    | dec i => simp [hp,follow] at h
    | half i => simp [hp,follow] at h
    | beep => simp [hp,follow] at h
    | brk i => simp [hp,follow] at h
    | cont i => simp [hp,follow] at h

/-- Any prefix of a completed grammar path is itself a valid control prefix. -/
theorem prefix_valid (pre tail : List Bool) (e : Edge)
    (hwalk : walk rootIndex (pre++tail) = some e) : valid pre := by
  have h := walk_follow (pre++tail) rootIndex e hwalk
  rw [follow_append] at h
  cases hp : follow (.node rootIndex) pre with
  | none => simp [hp] at h
  | some mid => exact ⟨mid,hp⟩

/-- At any zero branch on a completed path, switching to the sibling one
branch yields another valid (possibly internal) grammar prefix. -/
theorem sibling_valid (pre tail : List Bool) (e : Edge)
    (hwalk : walk rootIndex (pre++false::tail) = some e) : valid (pre++[true]) := by
  have h := walk_follow (pre++false::tail) rootIndex e hwalk
  obtain ⟨n,hn⟩ := proper_prefix_node (.node rootIndex) pre false tail e h
  have hb : n < 163 := follow_bounded pre (.node rootIndex) (.node n) (by simp [bounded,rootIndex]) hn
  obtain ⟨next,hnext⟩ := node_edge_exists n true hb
  refine ⟨next,?_⟩
  rw [follow_append,hn]
  simp [follow,hnext]

/-- Select a marked bit while scanning a reversed path. The result keeps the
prefix through that bit, replacing it by one. -/
def selectBack (bit : Bool) (skip : Nat) : List Bool → Option (List Bool)
  | [] => none
  | b::bs =>
    if b = bit then
      match skip with
      | 0 => some (bs.reverse++[true])
      | k+1 => selectBack bit k bs
    else selectBack bit skip bs

theorem selectBack_shape (bit : Bool) (xs : List Bool) (skip : Nat) (result : List Bool)
    (h : selectBack bit skip xs = some result) :
    ∃ dropped rest, xs = dropped++bit::rest ∧ result = rest.reverse++[true] := by
  induction xs generalizing skip with
  | nil => simp [selectBack] at h
  | cons b bs ih =>
    by_cases hb : b = bit
    · subst b
      cases skip with
      | zero =>
        simp only [selectBack,if_true,Option.some.injEq] at h
        exact ⟨[],bs,rfl,h.symm⟩
      | succ k =>
        have ht : selectBack bit k bs = some result := by simpa [selectBack] using h
        obtain ⟨dropped,rest,heq,hresult⟩ := ih k ht
        exact ⟨bit::dropped,rest,by simp [heq],hresult⟩
    · have ht : selectBack bit skip bs = some result := by simpa [selectBack,hb] using h
      obtain ⟨dropped,rest,heq,hresult⟩ := ih skip ht
      exact ⟨b::dropped,rest,by simp [heq],hresult⟩

theorem select_zero_zero (xs : List Bool) : selectBack false 0 xs = returnAfterZero xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [selectBack,returnAfterZero,ih]

theorem select_zero_one (xs : List Bool) : selectBack false 1 xs = returnAfterOneSkip xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [selectBack,returnAfterOneSkip,select_zero_zero,ih]

theorem select_zero_two (xs : List Bool) : selectBack false 2 xs = ControlBreak.returnAfterTwoSkip xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [selectBack,ControlBreak.returnAfterTwoSkip,select_zero_one,ih]

theorem select_one_zero (xs : List Bool) : selectBack true 0 xs = ControlContinue.continueAfterOne xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [selectBack,ControlContinue.continueAfterOne,ih]

theorem select_one_one (xs : List Bool) : selectBack true 1 xs = ControlContinue.continueAfterTwo xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [selectBack,ControlContinue.continueAfterTwo,select_one_zero,ih]

/-- Any skip-count zero return from a completed leaf path produces a valid
sibling prefix, independently of the register values or physical timing. -/
theorem selected_return_valid (code result : List Bool) (skip : Nat) (e : Edge)
    (hwalk : walk rootIndex code = some e)
    (hreturn : selectBack false skip code.reverse = some result) : valid result := by
  obtain ⟨dropped,rest,hcode,hresult⟩ := selectBack_shape false code.reverse skip result hreturn
  have hrev := congrArg List.reverse hcode
  simp only [List.reverse_reverse,List.reverse_append,List.reverse_cons] at hrev
  subst result
  rw [hrev] at hwalk
  have hw : walk rootIndex (rest.reverse++false::dropped.reverse) = some e := by
    simpa only [List.singleton_append,List.append_assoc] using hwalk
  exact sibling_valid rest.reverse dropped.reverse e hw

theorem return_path_valid (code result : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) (hreturn : returnPath code = some result) : valid result := by
  apply selected_return_valid code result 0 e hwalk
  simpa only [select_zero_zero,returnPath] using hreturn

theorem return_skip_one_valid (code result : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) (hreturn : returnPathSkipOne code = some result) : valid result := by
  apply selected_return_valid code result 1 e hwalk
  simpa only [select_zero_one,returnPathSkipOne] using hreturn

theorem return_skip_two_valid (code result : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) (hreturn : ControlBreak.returnPathSkipTwo code = some result) : valid result := by
  apply selected_return_valid code result 2 e hwalk
  simpa only [select_zero_two,ControlBreak.returnPathSkipTwo] using hreturn

/-- A continuation truncates a completed path at an earlier one, so the
result is a valid prefix of that same path. -/
theorem selected_continue_valid (code result : List Bool) (skip : Nat) (e : Edge)
    (hwalk : walk rootIndex code = some e)
    (hreturn : selectBack true skip code.reverse.tail = some result) : valid result := by
  cases hreverse : code.reverse with
  | nil =>
    have hnil : code = [] := List.reverse_eq_nil_iff.mp hreverse
    subst code
    simp [walk] at hwalk
  | cons last xs =>
    simp only [hreverse,List.tail_cons] at hreturn
    obtain ⟨dropped,rest,hcode,hresult⟩ := selectBack_shape true xs skip result hreturn
    have hrev := congrArg List.reverse hcode
    simp only [List.reverse_append,List.reverse_cons] at hrev
    have hwhole := congrArg List.reverse hreverse
    simp only [List.reverse_reverse,List.reverse_cons] at hwhole
    rw [hrev] at hwhole
    subst result
    rw [hwhole] at hwalk
    have hw : walk rootIndex ((rest.reverse++[true])++(dropped.reverse++[last])) = some e := by
      simpa only [List.append_assoc] using hwalk
    exact prefix_valid (rest.reverse++[true]) (dropped.reverse++[last]) e hw

theorem continue_one_valid (code result : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e)
    (hreturn : ControlContinue.continuePathOne code = some result) : valid result := by
  apply selected_continue_valid code result 0 e hwalk
  simpa only [select_one_zero,ControlContinue.continuePathOne] using hreturn

theorem continue_two_valid (code result : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e)
    (hreturn : ControlContinue.continuePathTwo code = some result) : valid result := by
  apply selected_continue_valid code result 1 e hwalk
  simpa only [select_one_one,ControlContinue.continuePathTwo] using hreturn

/-- Prefix traversal and the original complete-walk interpreter agree when
the result is a leaf. -/
theorem follow_leaf_walk (code : List Bool) (n : Nat) (e : Edge)
    (h : follow (.node n) code = some e) (hleaf : isLeaf e = true) :
    walk n code = some e := by
  induction code generalizing n with
  | nil =>
    simp only [follow,Option.some.injEq] at h
    subst e
    contradiction
  | cons b bs ih =>
    cases hn : nodeEdge n b with
    | none => simp [follow,hn] at h
    | some found =>
      cases found with
      | node j =>
        have hh : follow (.node j) bs = some e := by simpa only [follow,hn,Option.bind_some] using h
        simpa only [walk,hn] using ih j hh
      | inc j => cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | dec j => cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | half j => cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | beep => cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | brk j => cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption
      | cont j => cases bs <;> simp [walk,follow,hn] at h ⊢ <;> assumption

theorem zero_window (pos n : Nat) :
    window (fun _ => false) pos n = List.replicate n false := by
  induction n generalizing pos with
  | zero => rfl
  | succ n ih => simp only [window,List.replicate_succ,ih]

/-- Every valid control prefix reaches a leaf by reading at most 163 further
zero bits. This is a grammar bound; the available physical gap is not assumed
or established by this theorem. -/
theorem valid_zero_completion (pre : List Bool) (hvalid : valid pre) :
    ∃ zeros e, zeros ≤ 163 ∧ isLeaf e = true ∧
      walk rootIndex (pre++List.replicate zeros false) = some e := by
  obtain ⟨current,hpre⟩ := hvalid
  have hb := follow_bounded pre (.node rootIndex) current (by simp [bounded,rootIndex]) hpre
  cases current with
  | node n =>
    dsimp only [bounded] at hb
    obtain ⟨e,stop,hd⟩ := descend_terminates 163 n (fun _ => false) 0 hb (by omega)
    obtain ⟨len,_,hlen,_,hwalk⟩ := descend_trace 163 n (fun _ => false) 0 e stop hd
    have hleaf := (descend_bound 163 n (fun _ => false) 0 e stop hd).2.2
    rw [zero_window] at hwalk
    have hfollow := walk_follow _ n e hwalk
    have hall : follow (.node rootIndex) (pre++List.replicate len false) = some e := by
      rw [follow_append,hpre]
      simpa only [Option.bind_some] using hfollow
    exact ⟨len,e,hlen,hleaf,follow_leaf_walk _ rootIndex e hall hleaf⟩
  | inc n =>
    refine ⟨0,.inc n,by omega,rfl,?_⟩
    exact follow_leaf_walk _ rootIndex _ (by simpa using hpre) rfl
  | dec n =>
    refine ⟨0,.dec n,by omega,rfl,?_⟩
    exact follow_leaf_walk _ rootIndex _ (by simpa using hpre) rfl
  | half n =>
    refine ⟨0,.half n,by omega,rfl,?_⟩
    exact follow_leaf_walk _ rootIndex _ (by simpa using hpre) rfl
  | beep =>
    refine ⟨0,.beep,by omega,rfl,?_⟩
    exact follow_leaf_walk _ rootIndex _ (by simpa using hpre) rfl
  | brk n =>
    refine ⟨0,.brk n,by omega,rfl,?_⟩
    exact follow_leaf_walk _ rootIndex _ (by simpa using hpre) rfl
  | cont n =>
    refine ⟨0,.cont n,by omega,rfl,?_⟩
    exact follow_leaf_walk _ rootIndex _ (by simpa using hpre) rfl

end Shared.PNP.Record285.GrammarPrefix
