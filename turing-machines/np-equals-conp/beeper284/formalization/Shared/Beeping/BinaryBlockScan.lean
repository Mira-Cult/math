import Shared.Beeping.ComparisonAlphabetBits
import Shared.Beeping.Machines
import Shared.Beeping.Refinement

/-! A concrete finite binary transition table scans 13 cells, retaining their
bits as a binary-tree node in its finite state. It never changes tape bits or
beeps. Later code must dispatch the leaf and implement writes and movements. -/
namespace Shared.Beeping.BinaryBlockScan
open Shared.Beeping.Machines
open Shared.Beeping.ComparisonAlphabetBits Shared.Beeping.ComparisonSingleTape

/-- Every live node below 8192 has two children below 16384. Leaves and the
unused state zero continue moving right silently. -/
def next (q : Fin 16384) (bit : Bool) : Fin 16384 :=
  if h : q.val < 8192 then
    ⟨2*q.val + if bit then 1 else 0, by cases bit <;> simp <;> omega⟩
  else q

theorem next_val (q : Fin 16384) (bit : Bool) (h : q.val < 8192) :
    (next q bit).val = 2*q.val + if bit then 1 else 0 := by simp [next,h]

def scanner : Machine 16384 where
  table := ⟨Vector.ofFn fun q =>
    (⟨false,.right,next q false,false⟩, ⟨true,.right,next q true,false⟩)⟩
  start := ⟨1, by decide⟩
  blank := false
  startHead := 0

def begin (tape : Int → Bool) (head : Int) : Config 16384 := ⟨⟨1,by decide⟩,head,tape⟩

def index (tape : Int → Bool) (head : Int) : Nat → Nat
  | 0 => 1
  | k+1 => 2 * index tape head k + if tape (head + k) then 1 else 0

theorem index_bounds (tape : Int → Bool) (head : Int) (k : Nat) :
    2^k ≤ index tape head k ∧ index tape head k < 2^(k+1) := by
  induction k with
  | zero => simp [index]
  | succ k ih =>
    simp only [index,Nat.pow_succ] at *
    cases tape (head + k) <;> simp_all <;> omega

theorem index_live (tape : Int → Bool) (head : Int) (k : Nat) (hk : k < 13) :
    index tape head k < 8192 := by
  have h := (index_bounds tape head k).2
  have hp : 2^(k+1) ≤ 2^13 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp
  omega

theorem step (c : Config 16384) :
    scanner.step c = (⟨next c.state (c.tape c.head),c.head+1,c.tape⟩,false) := by
  have hw : c.write (c.tape c.head) = c.tape := by
    funext i
    by_cases h : i = c.head <;> simp [Config.write,h]
  cases hb : c.tape c.head with
  | false =>
    have hw' : c.write false = c.tape := by simpa [hb] using hw
    simp [Machine.step,scanner,Table.row,Move.apply,hb,hw']
  | true =>
    have hw' : c.write true = c.tape := by simpa [hb] using hw
    simp [Machine.step,scanner,Table.row,Move.apply,hb,hw']

/-- At every point through the thirteenth transition, the control state is the
binary-tree index of the bits read so far, the head advanced by that many
cells, and the tape is unchanged. -/
theorem scan (tape : Int → Bool) (head : Int) (k : Nat) (hk : k ≤ 13) :
    let c := scanner.system.advance (begin tape head) k
    c.state.val = index tape head k ∧ c.head = head + k ∧ c.tape = tape := by
  induction k with
  | zero => simp [EventSystem.advance,begin,index]
  | succ k ih =>
    have hp : k ≤ 13 := by omega
    have ⟨hs,hh,ht⟩ := ih hp
    have hl := index_live tape head k (by omega)
    change let c := (scanner.step (scanner.system.advance (begin tape head) k)).1
      c.state.val = index tape head (k+1) ∧ c.head = head + (k+1) ∧ c.tape = tape
    rw [step]
    simp only [Prod.fst]
    constructor
    · rw [next_val _ _ (by simpa [hs] using hl)]
      simp [index,hs,hh,ht]
    · constructor
      · simp [hh]; omega
      · exact ht

/-- The finite tree path has a total executable inverse: peel one low bit
per step, then restore reading order. -/
def unpath : Nat → Nat → List Bool
  | 0, _ => []
  | k+1, q => unpath k (q / 2) ++ [decide (q % 2 = 1)]

def path (bits : List Bool) : Nat :=
  bits.foldl (fun q bit => 2*q + if bit then 1 else 0) 1

theorem unpath_path (bits : List Bool) : unpath bits.length (path bits) = bits := by
  induction bits using List.reverseRecOn with
  | nil => rfl
  | append_singleton bits bit ih =>
    have hd : (2 * path bits + (if bit then 1 else 0)) / 2 = path bits := by
      cases bit <;> simp <;> omega
    have hb : decide ((2 * path bits + (if bit then 1 else 0)) % 2 = 1) = bit := by
      cases bit <;> simp <;> omega
    simp only [List.length_append,List.length_singleton,path,List.foldl_append,
      List.foldl_cons,List.foldl_nil,unpath]
    change unpath bits.length ((2 * path bits + (if bit then 1 else 0)) / 2) ++
      [decide ((2 * path bits + (if bit then 1 else 0)) % 2 = 1)] = bits ++ [bit]
    rw [hd,hb,ih]

def observed (tape : Int → Bool) (head : Int) (n : Nat) : List Bool :=
  (List.range n).map (fun i : Nat => tape (head + i))

theorem index_path (tape : Int → Bool) (head : Int) (k : Nat) :
    index tape head k = path (observed tape head k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [observed,path] at ih
    simp [index,observed,path,List.range_succ,List.map_append,List.foldl_append,← ih]

/-- This finite-control lookup can be compiled into dispatch rows. Invalid or
non-leaf states have no claimed interpretation. -/
def result (q : Fin 16384) : Option Alphabet := decode (unpath 13 q.val)

/-- After 13 transitions the finite control decodes to the original valid
simulator symbol. This uses no preloaded information beyond the binary tape. -/
theorem scan_block (tape : Int → Alphabet) (position : Int) :
    let c := scanner.system.advance (begin (binaryTape tape) (13*position)) 13
    result c.state = some (tape position) ∧
    c.head = 13*position + 13 ∧ c.tape = binaryTape tape := by
  have ⟨hs,hh,ht⟩ := scan (binaryTape tape) (13*position) 13 (by decide)
  constructor
  · unfold result
    rw [hs,index_path]
    have hlen : (observed (binaryTape tape) (13*position) 13).length = 13 := by simp [observed]
    have hu := unpath_path (observed (binaryTape tape) (13*position) 13)
    rw [hlen] at hu
    rw [hu]
    change decode (readBlock (binaryTape tape) position) = _
    exact decode_readBlock tape position
  · exact ⟨hh,ht⟩

/-- The scanner has reached the leaf half of its finite state space. -/
theorem scan_leaf (tape : Int → Bool) (head : Int) :
    8192 ≤ (scanner.system.advance (begin tape head) 13).state.val := by
  have hs := (scan tape head 13 (by decide)).1
  rw [hs]
  have hb := (index_bounds tape head 13).1
  norm_num at hb
  exact hb

namespace Fixtures
example : (scanner.system.advance (begin (fun _ => false) 0) 13).state.val = 8192 := by
  have h := (scan (fun _ => false) 0 13 (by decide)).1
  simpa [index] using h
end Fixtures

/-- Every row is silent, including all states outside the scanning path. -/
theorem no_beeps (tape : Int → Bool) (head : Int) (k : Nat) :
    ¬ scanner.system.BeepFrom (begin tape head) k := by
  simp [EventSystem.BeepFrom,Machine.system,step]

end Shared.Beeping.BinaryBlockScan
