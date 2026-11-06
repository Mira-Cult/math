import Shared.Beeping.BinaryBlockScan

/-! A finite binary table for writing a stored 13-bit word backwards.
The source block is supplied in finite control; future compiler work must
produce that control state and combine this table with row dispatch. -/
namespace Shared.Beeping.BinaryBlockWrite
open Shared.Beeping.Machines
open Shared.Beeping.BinaryBlockScan
open Shared.Beeping.ComparisonAlphabetBits
open Shared.Beeping.ComparisonSingleTape

abbrev Word := Fin 8192
abbrev Phase := Fin 16

def state (word : Word) (phase : Phase) : Fin 131072 :=
  ⟨16*word.val+phase.val, by have := word.isLt; have := phase.isLt; omega⟩

theorem state_phase (word : Word) (phase : Phase) : (state word phase).val % 16 = phase.val := by
  simp only [state]
  have := phase.isLt
  omega

theorem state_word (word : Word) (phase : Phase) : (state word phase).val / 16 = word.val := by
  simp only [state]
  have := phase.isLt
  omega

def bit (word : Nat) (offset : Nat) : Bool := ((unpath 13 (8192+word))[offset]?).getD false

def next (q : Fin 131072) : Fin 131072 :=
  if h : q.val % 16 < 15 then ⟨q.val+1, by have := q.isLt; omega⟩ else q

def row (q : Fin 131072) (read : Bool) : Row 131072 :=
  let phase := q.val % 16
  let w := q.val / 16
  ⟨if 1 ≤ phase ∧ phase ≤ 13 then bit w (13-phase) else read,
    if phase ≤ 13 then .left else .right, next q, false⟩

def writer : Machine 131072 where
  table := ⟨Vector.ofFn fun q => (row q false,row q true)⟩
  start := state ⟨0,by decide⟩ ⟨0,by decide⟩
  blank := false
  startHead := 0

def begin (word : Word) (tape : Int → Bool) (head : Int) : Config 131072 :=
  ⟨state word ⟨0,by decide⟩,head,tape⟩

def written (word : Word) (tape : Int → Bool) (head : Int) : Nat → Int → Bool
  | 0 => tape
  | k+1 => Function.update (written word tape head k) (head - (k+1 : Nat)) (bit word.val (12-k))

theorem next_phase (word : Word) (phase : Phase) (h : phase.val < 15) :
    next (state word phase) = state word ⟨phase.val+1,by omega⟩ := by
  unfold next
  have hh : (state word phase).val % 16 < 15 := by simpa [state_phase] using h
  rw [dif_pos hh]
  apply Fin.ext
  simp [state]
  omega

theorem step (c : Config 131072) :
    writer.step c =
      let r := row c.state (c.tape c.head)
      (⟨r.next,r.move.apply c.head,c.write r.write⟩,false) := by
  cases hb : c.tape c.head <;> simp [Machine.step,writer,Table.row,hb,row]

/-- Start to the left of the cell immediately after the block. -/
theorem first (word : Word) (tape : Int → Bool) (head : Int) :
    (writer.system.advance (begin word tape head) 1) =
      ⟨state word ⟨1,by decide⟩,head-1,tape⟩ := by
  change (writer.step (begin word tape head)).1 = _
  rw [step]
  have hw : (begin word tape head).write ((begin word tape head).tape (begin word tape head).head) = tape := by
    funext i
    by_cases h : i = head <;> simp [begin,Config.write,h]
  have hw' : (⟨state word ⟨0,by decide⟩,head,tape⟩ : Config 131072).write (tape head) = tape := hw
  simp only [begin] at hw
  simp [row,begin,state_phase,state_word,next_phase,Move.apply,hw]
  funext i
  by_cases hi : i = head <;> simp [Config.write,hi]

/-- For each written bit, the next row writes the word's corresponding bit,
then moves one cell left. -/
theorem write_step (word : Word) (k : Nat) (hk : k < 13)
    (tape : Int → Bool) (head : Int) :
    (writer.step ⟨state word ⟨k+1,by omega⟩,head-(k+1),tape⟩).1 =
      ⟨state word ⟨k+2,by omega⟩,head-(k+2),
        Function.update tape (head-(k+1)) (bit word.val (12-k))⟩ := by
  rw [step]
  simp only [Prod.fst]
  have hs := state_phase word (⟨k+1,by omega⟩ : Phase)
  have hw := state_word word (⟨k+1,by omega⟩ : Phase)
  have hn := next_phase word (⟨k+1,by omega⟩ : Phase) (by simp; omega)
  have hk' : k ≤ 12 := by omega
  have hsub : 13-(k+1) = 12-k := by omega
  simp [row,hs,hw,hn,hk',hsub,Move.apply]
  constructor
  · omega
  · funext i
    by_cases hi : i = head - (k+1 : Nat) <;> simp [Config.write,Function.update,hi]

/-- After the initial left move, each of the next `k` transitions writes one
bit, with an exact functional tape description. -/
theorem write_run (word : Word) (tape : Int → Bool) (head : Int) (k : Nat) (hk : k ≤ 13) :
    writer.system.advance (begin word tape head) (1+k) =
      ⟨state word ⟨k+1,by omega⟩,head-(k+1),written word tape head k⟩ := by
  induction k with
  | zero => simpa [written] using first word tape head
  | succ k ih =>
    have hp : k ≤ 13 := by omega
    rw [show 1+(k+1) = (1+k)+1 by omega, EventSystem.advance, ih hp]
    simpa [written,Machine.system,Nat.cast_add,Nat.cast_one,add_assoc] using write_step word k (by omega) (written word tape head k) head

theorem written_inside (word : Word) (tape : Int → Bool) (head : Int)
    (k j : Nat) (hj : j < k) :
    written word tape head k (head-(j+1)) = bit word.val (12-j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : j = k
    · subst j
      simp [written]
    · have hj' : j < k := by omega
      have hn : head-(j+1 : Nat) ≠ head-(k+1 : Nat) := by omega
      simp only [written,Nat.cast_add,Nat.cast_one] at hn ⊢
      rw [Function.update_of_ne hn]
      exact ih hj'

theorem written_outside (word : Word) (tape : Int → Bool) (head : Int)
    (k : Nat) (i : Int) (h : i < head-k ∨ head ≤ i) :
    written word tape head k i = tape i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hn : i ≠ head-(k+1 : Nat) := by omega
    simp only [written,Function.update_of_ne hn]
    exact ih (by omega)

theorem finish (word : Word) (tape : Int → Bool) (head : Int) :
    (writer.step ⟨state word ⟨14,by decide⟩,head-14,tape⟩).1 =
      ⟨state word ⟨15,by decide⟩,head-13,tape⟩ := by
  rw [step]
  have hn := next_phase word (⟨14,by decide⟩ : Phase) (by decide)
  have hn' : next (state word 14) = state word 15 := by simpa using hn
  simp [row,state_phase,state_word,hn',Move.apply]
  constructor
  · omega
  · funext i
    by_cases hi : i = head-14 <;> simp [Config.write,hi]

/-- A complete write takes 15 transitions: one positioning move, 13 writes,
and one move back to the block's left boundary. -/
theorem write_complete (word : Word) (tape : Int → Bool) (head : Int) :
    writer.system.advance (begin word tape head) 15 =
      ⟨state word ⟨15,by decide⟩,head-13,written word tape head 13⟩ := by
  change (writer.system.step (writer.system.advance (begin word tape head) (1+13))).1 = _
  rw [write_run word tape head 13 (by decide)]
  exact finish word (written word tape head 13) head

/-- Every binary word's tree code lies in the leaf interval for its length. -/
theorem path_bounds (bits : List Bool) :
    2^bits.length ≤ path bits ∧ path bits < 2^(bits.length+1) := by
  induction bits using List.reverseRecOn with
  | nil => simp [path]
  | append_singleton bits b ih =>
    have he : path (bits ++ [b]) = 2*path bits + if b then 1 else 0 := by
      simp [path,List.foldl_append]
    simp only [List.length_append,List.length_singleton,Nat.pow_succ] at *
    rw [he]
    cases b <;> simp_all <;> omega

/-- Finite control containing exactly the encoding of a source alphabet symbol. -/
def wordOf (a : Alphabet) : Word :=
  ⟨path (encode a)-8192, by
    have h := path_bounds (encode a)
    rw [encode_length] at h
    norm_num at h
    omega⟩

theorem wordOf_decode (a : Alphabet) : unpath 13 (8192+(wordOf a).val) = encode a := by
  have h := path_bounds (encode a)
  rw [encode_length] at h
  norm_num at h
  have he : 8192+(wordOf a).val = path (encode a) := by
    change 8192 + (path (encode a) - 8192) = path (encode a)
    exact Nat.add_sub_of_le h.1
  have hu := unpath_path (encode a)
  rw [encode_length] at hu
  simpa [he] using hu

/-- On an encoded source tape, writing `wordOf a` changes exactly the
selected source cell's block, including for negative positions. -/
theorem written_binary_update (tape : Int → Alphabet) (position : Int) (a : Alphabet) :
    written (wordOf a) (binaryTape tape) (13*position+13) 13 =
      binaryTape (Function.update tape position a) := by
  funext i
  by_cases hp : i / 13 = position
  · let r : Nat := (i % 13).toNat
    have hr0 : 0 ≤ i % 13 := by omega
    have hr : (r : Int) = i % 13 := Int.toNat_of_nonneg hr0
    have hlt : r < 13 := by omega
    have hi : i = 13*position+(r : Int) := by omega
    let j : Nat := 12-r
    have hj : j < 13 := by omega
    have hpos : 13*position+13-(j+1 : Nat) = i := by omega
    have hjval : 12-j = r := by omega
    have hw := written_inside (wordOf a) (binaryTape tape) (13*position+13) 13 j hj
    simp only [Nat.cast_add,Nat.cast_one] at hpos hw
    rw [hpos,hjval] at hw
    rw [hw]
    simp [bit,wordOf_decode,binaryTape,hp,Function.update_self,r]
  · have ho : i < 13*position ∨ 13*position+13 ≤ i := by omega
    rw [written_outside (wordOf a) (binaryTape tape) (13*position+13) 13 i (by omega)]
    simp [binaryTape,Function.update_of_ne hp]

/-- The concrete writer implements the encoded single-cell update, returns to
the aligned source-cell address, and takes exactly 15 transitions. -/
theorem write_binary_cell (tape : Int → Alphabet) (position : Int) (a : Alphabet) :
    writer.system.advance (begin (wordOf a) (binaryTape tape) (13*position+13)) 15 =
      ⟨state (wordOf a) ⟨15,by decide⟩,13*position,
        binaryTape (Function.update tape position a)⟩ := by
  rw [write_complete,written_binary_update]
  congr 1 <;> omega

/-- Applied to the actual post-Turing tape, the same 15 transitions implement
its `write` instruction at the current head. -/
theorem write_postTape (tape : Turing.Tape Alphabet) (a : Alphabet) :
    writer.system.advance (begin (wordOf a) (binaryTape tape.nth) 13) 15 =
      ⟨state (wordOf a) ⟨15,by decide⟩,0,binaryTape (tape.write a).nth⟩ := by
  have he : Function.update tape.nth 0 a = (tape.write a).nth := by
    funext i
    simp [Function.update,Turing.Tape.write_nth]
  have h := write_binary_cell tape.nth 0 a
  simpa [he] using h

theorem no_beeps (word : Word) (tape : Int → Bool) (head : Int) (k : Nat) :
    ¬ writer.system.BeepFrom (begin word tape head) k := by
  simp [EventSystem.BeepFrom,Machine.system,step]

end Shared.Beeping.BinaryBlockWrite
