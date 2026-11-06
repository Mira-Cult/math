import Shared.Codes.FiniteProgramFrameProbe

/-! Loop the successful frame-removal branch back to the fixed-width crossing
entry. The distinct empty-buffer continuation remains unexecuted. -/
namespace Shared.Codes.FiniteProgramFrameLoop
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramLink (link shiftConfig shiftStatus step_shift)
open Shared.Codes.FiniteProgramSplice (stem stem_length)
open Shared.Codes.FiniteProgramCrossTag (phase cursor)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev base (n : Nat) := Shared.Codes.FiniteProgramFrameProbe.program n
def stop (n : Nat) : Nat := 8*n+52
def empty (n : Nat) : Nat := 8*n+53

theorem base_length (n : Nat) : (base n).length = 8*n+54 :=
  Shared.Codes.FiniteProgramFrameProbe.program_length n

theorem base_valid (n : Nat) : valid (base n) = true :=
  Shared.Codes.FiniteProgramFrameProbe.program_valid n

theorem stop_bound (n : Nat) : stop n < (base n).length := by simp [stop,base_length]

theorem zero_stop (t : Tape) : step (base 0) (stop 0,t) = some (.inl false) := by
  cases h : t.2.1 <;>
    simp [base,stop,Shared.Codes.FiniteProgramFrameProbe.program,
      Shared.Codes.FiniteProgramFrameProbe.base,Shared.Codes.FiniteProgramFrameProbe.pre,
      Shared.Codes.FiniteProgramFrameProbe.dummy,Shared.Codes.FiniteProgramDropTag.program,
      Shared.Codes.FiniteProgramDropTag.setup,Shared.Codes.FiniteProgramDropTag.phases,
      Shared.Codes.FiniteProgramDropTag.phase,Shared.Codes.FiniteProgramDropTag.dummy,
      Shared.Codes.FiniteProgramTaggedAdvance.program,Shared.Codes.FiniteProgramSplice.program,
      Shared.Codes.FiniteProgramSplice.stem,link,Shared.Codes.FiniteProgramLink.shiftPair,
      Shared.Codes.FiniteProgramLink.shiftRow,step,h]

theorem base_stop (n : Nat) (t : Tape) : step (base n) (stop n,t) = some (.inl false) := by
  induction n with
  | zero => exact zero_stop t
  | succ n ih =>
    have h := step_shift (stem phase) (base n) [] (stop n,t) (stop_bound n)
    rw [ih] at h
    simpa [base,Shared.Codes.FiniteProgramFrameProbe.program,
      Shared.Codes.FiniteProgramSplice.program,stem_length,phase,stop,
      shiftConfig,shiftStatus,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def program (n : Nat) : Program := (base n).set (stop n) (branch (base n).length) ++ [bridge 0]

theorem length (n : Nat) : (program n).length = 8*n+55 := by simp [program,base_length]

theorem base_other (n : Nat) (d : Config) (hd : d.1 < (base n).length)
    (hne : d.1 ≠ stop n) : step (base n) d = step (program n) d := by
  have he : (program n)[d.1]? = (base n)[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,he]

theorem stop_row (n : Nat) : (program n)[stop n]? = some (branch (base n).length) := by
  simp [program,List.getElem?_append_left,stop_bound]

theorem bridge_row (n : Nat) : (program n)[(base n).length]? = some (bridge 0) := by
  simp [program]

theorem restart (n : Nat) (b : Bool) (L R : List Bool) :
    run (program n) (stop n,tapeAt L (b::false::R)) 2 =
      some (.inr (0,tapeAt L (b::false::R))) := by
  have hs := stop_row n
  have hb := bridge_row n
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape]

theorem program_valid (n : Nat) : valid (program n) = true := by
  let p := base n
  let m := p.length+1
  have hm : (program n).length = m := by simp [program,m,p]
  have hold : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    intro r hr
    have hv := base_valid n
    change valid p = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hbound : p.length ≤ m := by simp [m]
  have hp : ∀ r ∈ p.set (stop n) (branch p.length),
      validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    rcases List.mem_or_eq_of_mem_set hr with ho | he
    · obtain ⟨h₁,h₂⟩ := hold r ho
      exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₁,
        Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hbound h₂⟩
    · subst r
      have hb : p.length < m := by simp [m]
      simp [branch,validRow,hb]
  have hb : validRow m (bridge 0).1 = true ∧ validRow m (bridge 0).2 = true := by
    have hmpos : 0 < m := by simp [m]
    simp [bridge,validRow,hmpos]
  have hall : (program n).all
      (fun r => validRow (program n).length r.1 && validRow (program n).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ p.set (stop n) (branch p.length) ∨ r = bridge 0 := by
      simpa [program,p,List.mem_append] using hr
    rw [hm]
    rcases hr' with hp' | hb'
    · simpa only [Bool.and_eq_true] using hp r hp'
    · subst r; simpa only [Bool.and_eq_true] using hb
  have hn : (program n).isEmpty = false := by simp [program]
  change (!(program n).isEmpty && (program n).all
    (fun r => validRow (program n).length r.1 && validRow (program n).length r.2)) = true
  rw [hn,hall]
  rfl

/-- One full pass crosses the fixed-size word, removes the next metadata,
then returns to the entry in two charged transitions. -/
theorem cycle (kept xs L R : List Bool) (b m : Bool) :
    run (program kept.length) (0,tapeAt L (b::false::tagged (kept ++ m::xs) ++ false::R))
      (7*kept.length+30*xs.length+26) =
      some (.inr (0,tapeAt (cursor b L kept).2
        ((cursor b L kept).1::false::tagged xs ++ false::false::false::false::R))) := by
  have h := Shared.Codes.FiniteProgramFrameProbe.cross_present kept xs L R b m
  change run (base kept.length) _ _ = some (.inr (stop kept.length,_)) at h
  have hp := Shared.Codes.FiniteProgramFirstEntry.first_entry (base kept.length) (program kept.length)
    _ _ _ (stop kept.length) false (base_valid kept.length) (by simp [base_length])
    (base_stop kept.length) (base_other kept.length) h
  rw [show 7*kept.length+30*xs.length+26 = (7*kept.length+30*xs.length+24)+2 by omega]
  rw [run_continue _ _ _ _ _ hp]
  simp only [List.cons_append]
  exact restart kept.length (cursor b L kept).1 (cursor b L kept).2
    (tagged xs ++ false::false::false::false::R)

/-- The empty branch is unaffected by the patched success row and reaches
its distinct live continuation. -/
theorem finish (kept L R : List Bool) (b : Bool) :
    run (program kept.length) (0,tapeAt L (b::false::tagged kept ++ false::R))
      (7*kept.length+4) =
      some (.inr (empty kept.length,
        tapeAt (cursor b L kept).2 ((cursor b L kept).1::false::false::R))) := by
  have h := Shared.Codes.FiniteProgramFrameProbe.cross_empty kept L R b
  change run (base kept.length) _ _ = some (.inr (empty kept.length,_)) at h
  exact Shared.Codes.FiniteProgramFirstEntry.first_entry (base kept.length) (program kept.length)
    _ _ _ (stop kept.length) false (base_valid kept.length) (by simp [base_length])
    (base_stop kept.length) (base_other kept.length) h

theorem cursor_append (b : Bool) (L xs ys : List Bool) :
    cursor b L (xs++ys) = cursor (cursor b L xs).1 (cursor b L xs).2 ys := by
  induction xs generalizing b L with
  | nil => rfl
  | cons x xs ih => simpa [cursor] using ih true (x::true::b::L)

/-- A finite list of metadata/word pairs in their physical buffer order. -/
def framed : List (Bool × List Bool) → List Bool
  | [] => []
  | (m,word)::rest => m::(word ++ framed rest)

def words (items : List (Bool × List Bool)) : List Bool := items.flatMap Prod.snd

def totalCost (width : Nat) : List (Bool × List Bool) → Nat
  | [] => 7*width+4
  | (_,word)::rest => 7*width+30*(word ++ framed rest).length+26+totalCost width rest

def padding : Nat → List Bool → List Bool
  | 0,R => R
  | n+1,R => padding n (false::false::false::R)

/-- This one fixed table removes all metadata from any finite sequence of
equal-width words. It crosses the last word and exits on the empty branch.
The remaining words are tagged and lie in the left tape through `cursor`. -/
theorem run_frames (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width)
    (kept L R : List Bool) (b : Bool) (hk : kept.length = width) :
    run (program width) (0,tapeAt L (b::false::tagged (kept ++ framed items) ++ false::R))
      (totalCost width items) =
      some (.inr (empty width,
        tapeAt (cursor b L (kept ++ words items)).2
          ((cursor b L (kept ++ words items)).1::false::false::padding items.length R))) := by
  induction items generalizing kept L R b with
  | nil =>
    have h := finish kept L R b
    simpa [framed,words,totalCost,padding,hk] using h
  | cons item items ih =>
    rcases item with ⟨m,word⟩
    have hw : word.length = width := hwidth (m,word) (by simp)
    have ht : ∀ item ∈ items, item.2.length = width := by
      intro item hi
      exact hwidth item (by simp [hi])
    have hcycle := cycle kept (word ++ framed items) L R b m
    have hnext := ih ht word (cursor b L kept).2 (false::false::false::R)
      (cursor b L kept).1 hw
    have htime : totalCost width ((m,word)::items) =
      (7*kept.length+30*(word ++ framed items).length+26)+totalCost width items := by
        simp [totalCost,hk]
    rw [htime]
    simp only [framed,List.cons_append] at hcycle ⊢
    rw [run_continue _ _ _ _ _ (by simpa [hk] using hcycle)]
    simpa [hk,words,framed,padding,cursor_append,List.append_assoc] using hnext

theorem framed_length (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width) :
    (framed items).length = items.length*(width+1) := by
  induction items with
  | nil => simp [framed]
  | cons item items ih =>
    rcases item with ⟨m,word⟩
    have hw : word.length = width := hwidth (m,word) (by simp)
    have ht : ∀ item ∈ items, item.2.length = width := by
      intro item hi
      exact hwidth item (by simp [hi])
    simp only [framed,List.length_cons,List.length_append,hw,ih ht,Nat.succ_mul]
    omega

/-- A quadratic transition bound in the number of frames, with the codec
width explicit. This bounds the physical table run, not a host-language list
operation. -/
theorem totalCost_bound (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width) :
    totalCost width items ≤ (items.length+1) *
      (7*width+30*((items.length+1)*(width+1))+26) := by
  induction items with
  | nil => simp [totalCost]; omega
  | cons item items ih =>
    rcases item with ⟨m,word⟩
    have hw : word.length = width := hwidth (m,word) (by simp)
    have ht : ∀ item ∈ items, item.2.length = width := by
      intro item hi
      exact hwidth item (by simp [hi])
    let n := items.length
    let bound := 7*width+30*((n+2)*(width+1))+26
    have hsize : (word ++ framed items).length ≤ (n+2)*(width+1) := by
      simp only [List.length_append,hw,framed_length width items ht]
      dsimp [n]
      simp only [Nat.add_mul]
      omega
    have hlocal : 7*width+30*(word ++ framed items).length+26 ≤ bound := by
      dsimp [bound]
      omega
    have hsmall : 7*width+30*((n+1)*(width+1))+26 ≤ bound := by
      dsimp [bound]
      simp only [Nat.add_mul]
      omega
    have hrec : totalCost width items ≤ (n+1)*bound :=
      le_trans (ih ht) (Nat.mul_le_mul_left (n+1) hsmall)
    change (7*width+30*(word ++ framed items).length+26)+totalCost width items ≤ (n+2)*bound
    calc
      _ ≤ bound+(n+1)*bound := Nat.add_le_add hlocal hrec
      _ = (n+2)*bound := by simp [Nat.add_mul]; omega

open Shared.ComplexityBridge.FirstBlocksContent (frames frames_cons selected selected_length)

def selectedItems (zero one bits : List Bool) : List (Bool × List Bool) :=
  bits.map (fun b => (b,selected zero one b))

theorem framed_selectedItems (zero one bits : List Bool) :
    framed (selectedItems zero one bits) = frames zero one bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change b::(selected zero one b ++ framed (selectedItems zero one bits)) = frames zero one (b::bits)
    rw [frames_cons,ih]
    rfl

theorem words_selectedItems (zero one bits : List Bool) :
    words (selectedItems zero one bits) = bits.flatMap (selected zero one) := by
  simp [words,selectedItems,List.flatMap_map]

/-- The loop applies to the actual framed selected words produced by the
earlier scan. The caller supplies the first word after its metadata was
already removed, and a buffer with an explicit false end marker. -/
theorem run_selected_frames (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width)
    (previous b : Bool) (bits L R : List Bool) :
    let kept := selected zero one previous
    let allWords := kept ++ bits.flatMap (selected zero one)
    run (program width) (0,tapeAt L (b::false::tagged (kept ++ frames zero one bits) ++ false::R))
      (totalCost width (selectedItems zero one bits)) =
      some (.inr (empty width, tapeAt (cursor b L allWords).2
        ((cursor b L allWords).1::false::false::padding bits.length R))) := by
  have hw : ∀ item ∈ selectedItems zero one bits, item.2.length = width := by
    intro item hi
    obtain ⟨bit,_,rfl⟩ := List.mem_map.mp hi
    exact selected_length zero one width hzero hone bit
  have h := run_frames width (selectedItems zero one bits) hw (selected zero one previous) L R b
    (selected_length zero one width hzero hone previous)
  rw [framed_selectedItems,words_selectedItems] at h
  simpa [selectedItems] using h

namespace Fixtures
example : totalCost 1 [(true,[false]),(false,[true])] = 197 := by decide
example : totalCost 0 [(true,[])] = 30 := by decide
example : (program 1).length = 63 := by simpa using length 1
end Fixtures

end Shared.Codes.FiniteProgramFrameLoop
