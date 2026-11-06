import Shared.Beeping.NPcoNP.NativeIncBlock

/-! Candidate whole-bank specification for the physical insertion scan. -/
namespace Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBlock
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 10000000

def inputWord (n : Nat) (rest : List Nat) : List Bool :=
  List.replicate n true ++ (false :: (encode rest ++ [false]))

def outputWord (n : Nat) (rest : List Nat) : List Bool :=
  List.replicate (n+1) true ++ (false :: encode rest)

theorem holds_append_intro (t : Int → Bool) (h : Int) (xs ys : List Bool)
    (hx : Holds t h xs) (hy : Holds t (h+(xs.length : Int)) ys) :
    Holds t h (xs++ys) := by
  induction xs generalizing h with
  | nil => simpa using hy
  | cons x xs ih =>
    change t h=x ∧ Holds t (h+1) xs at hx
    change t h=x ∧ Holds t (h+1) (xs++ys)
    refine ⟨hx.1,ih (h+1) hx.2 ?_⟩
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm] using hy

theorem split_ones (n : Nat) (h : Int) (t : Int → Bool) (tail : List Bool)
    (ht : Holds t h (List.replicate n true ++ tail)) :
    (∀ i : Nat, i<n → t (h+(i : Int))=true) ∧
      Holds t (h+(n : Int)) tail := by
  constructor
  · intro i hi
    have hlen : i<(List.replicate n true ++ tail).length := by simp; omega
    have hg := Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape.holds_get t h _ ht i hlen
    have hi' : i<(List.replicate n true).length := by simpa using hi
    rw [List.getElem_append_left hi'] at hg
    simpa using hg
  · have htail := holds_append_tail t h (List.replicate n true) tail ht
    simpa using htail

theorem prefix_from_cells (n : Nat) (h : Int) (u : Int → Bool)
    (ones : ∀ i : Nat, i<n → u (h+(i : Int))=true)
    (lastOne : u (h+(n : Int))=true)
    (lastZero : u (h+(n : Int)+1)=false) :
    Holds u h (List.replicate (n+1) true ++ [false]) := by
  apply holds_ones_delimiter (n+1) h u
  · intro i hi
    by_cases hsmall : i<n
    · exact ones i hsmall
    · have he : i=n := by omega
      simpa [he] using lastOne
  · have he : h+((n+1 : Nat):Int)=h+(n : Int)+1 := by push_cast; omega
    rw [he]
    exact lastZero

theorem continued_prefix (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true) :
    Holds (clearAt (h+(n : Int)+1) (setAt (h+(n : Int)) t)) h
      (List.replicate (n+1) true ++ [false]) := by
  let p := h+(n : Int)
  apply prefix_from_cells n h
  · intro i hi
    have ha : h+(i : Int) ≠ p := by dsimp [p]; omega
    have hb : h+(i : Int) ≠ p+1 := by dsimp [p]; omega
    rw [shift_next_frame p (h+(i : Int)) t ha hb]
    exact ones i hi
  · exact (shift_next_bits p t).1
  · exact (shift_next_bits p t).2

theorem finished_prefix (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true)
    (after : t (h+(n : Int)+1)=false) :
    Holds (setAt (h+(n : Int)) t) h (List.replicate (n+1) true ++ [false]) := by
  apply prefix_from_cells n h
  · intro i hi
    have hn : h+(i : Int)≠h+(n : Int) := by omega
    simp [setAt,hn,ones i hi]
  · simp [setAt]
  · have hn : h+(n : Int)+1≠h+(n : Int) := by omega
    simp [setAt,hn,after]

/-- The 14/22 scan inserts one one into the leading run and shifts every
following encoded block one cell right. The suffix is required to end with
a supplied zero sentinel; the protected left tape is unchanged. -/
theorem shift_bank (rest : List Nat) (n : Nat) (h : Int) (t : Int → Bool)
    (input : Holds t h (inputWord n rest)) :
    ∃ e : Config 284, e.state=23 ∧
      e.head=h+((n+(encode rest).length : Nat):Int) ∧
      Holds e.tape h (outputWord n rest) ∧
      (∀ p, p<h ∨ h+((n+(encode rest).length : Nat):Int)<p → e.tape p=t p) ∧
      silentSegment machine (cfg 14 h t) e (n+2+(encode rest).length) := by
  induction rest generalizing n h t with
  | nil =>
    have split := split_ones n h t (false :: (encode [] ++ [false])) input
    have hz : t (h+(n : Int))=false ∧ t (h+(n : Int)+1)=false := by
      simpa [encode,Holds] using split.2
    let u := setAt (h+(n : Int)) t
    refine ⟨cfg 23 (h+(n : Int)) u,rfl,?_,?_,?_,?_⟩
    · simp [cfg,encode]
    · change Holds u h (outputWord n [])
      simpa [outputWord,encode] using finished_prefix n h t split.1 hz.2
    · intro p hp
      change setAt (h+(n : Int)) t p=t p
      have hn : p≠h+(n : Int) := by
        simp only [encode,List.length_nil,Nat.add_zero] at hp
        rcases hp with hp | hp <;> omega
      simp [setAt,hn]
    · simpa [encode] using shift_last_block n h t split.1 hz.1 hz.2
  | cons w ws ih =>
    have split := split_ones n h t (false :: (encode (w::ws) ++ [false])) input
    let a : Int := h+(n : Int)
    have hc : t a=false ∧ t (a+1)=true ∧ Holds t (a+2) (inputWord w ws) := by
      have hh := split.2
      change Holds t a (false :: (encode (w::ws) ++ [false])) at hh
      simpa [inputWord,encode,block,List.replicate_succ,List.append_assoc,Holds,Int.add_assoc] using hh
    let u := clearAt (a+1) (setAt a t)
    have htail : Holds u (a+2) (inputWord w ws) := by
      apply holds_transport t u (a+2) _ hc.2.2
      intro p hp _
      symm
      exact shift_next_frame a p t (by omega) (by omega)
    obtain ⟨e,he,hhead,hout,hframe,hseg⟩ := ih w (a+2) u htail
    have hprefix : Holds u h (List.replicate (n+1) true ++ [false]) := by
      exact continued_prefix n h t split.1
    have hprefix' : Holds e.tape h (List.replicate (n+1) true ++ [false]) := by
      apply holds_transport u e.tape h _ hprefix
      intro p hlo hhi
      symm
      apply hframe p
      left
      simp only [List.length_append,List.length_replicate,List.length_singleton,Nat.cast_add,Nat.cast_one] at hhi
      dsimp [a]
      omega
    have hrest : Holds e.tape (a+2) (encode (w::ws)) := by
      simpa [outputWord,encode,block,List.append_assoc] using hout
    have hwhole : Holds e.tape h (outputWord n (w::ws)) := by
      have hh := holds_append_intro e.tape h (List.replicate (n+1) true ++ [false])
        (encode (w::ws)) hprefix' (by
          simpa [a,Int.add_assoc] using hrest)
      simpa [outputWord,List.append_assoc] using hh
    have hlen : 2≤(encode (w::ws)).length := by
      simp only [encode,List.length_append,block_length]
      omega
    have hbound : a+2+((w+(encode ws).length : Nat):Int) =
        h+((n+(encode (w::ws)).length : Nat):Int) := by
      simp only [encode,List.length_append,block_length,Nat.cast_add]
      dsimp [a]
      push_cast
      omega
    have hfull : ∀ p, p<h ∨ h+((n+(encode (w::ws)).length : Nat):Int)<p → e.tape p=t p := by
      intro p hp
      have hrec : p<a+2 ∨ a+2+((w+(encode ws).length : Nat):Int)<p := by
        rcases hp with hp | hp
        · left; dsimp [a]; omega
        · right; rw [hbound]; exact hp
      rw [hframe p hrec]
      exact shift_next_frame a p t
        (by rcases hp with hp | hp <;> dsimp [a] at * <;> omega)
        (by rcases hp with hp | hp <;> dsimp [a] at * <;> omega)
    have hfirst := shift_next_block n h t split.1 hc.1 hc.2.1
    have hall := segAdd machine _ _ _ (n+2) (w+2+(encode ws).length) hfirst hseg
    refine ⟨e,he,?_,hwhole,hfull,?_⟩
    · rw [hhead]
      simp only [encode,List.length_append,block_length,Nat.cast_add]
      dsimp [a]
      push_cast
      omega
    · convert hall using 1 <;>
        simp [encode,List.length_append,block_length,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Literal state-14 increment on a complete nonempty encoded bank with a
zero sentinel. This theorem does not assert that the machine reaches this
layout or that the state-23 return has completed. -/
theorem encoded_increment (v : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (bank : Holds t h (encode (v::rest) ++ [false])) :
    ∃ e : Config 284, e.state=23 ∧
      e.head=h+(((v+1)+(encode rest).length : Nat):Int) ∧
      Holds e.tape h (encode ((v+1)::rest)) ∧
      (∀ p, p<h ∨ h+(((v+1)+(encode rest).length : Nat):Int)<p → e.tape p=t p) ∧
      silentSegment machine (cfg 14 h t) e (v+3+(encode rest).length) := by
  have input : Holds t h (inputWord (v+1) rest) := by
    simpa [inputWord,encode,block,List.append_assoc] using bank
  obtain ⟨e,he,hh,ho,hframe,hseg⟩ := shift_bank rest (v+1) h t input
  refine ⟨e,he,hh,?_,hframe,?_⟩
  · simpa [outputWord,encode,block,List.append_assoc] using ho
  · simpa [Nat.add_assoc] using hseg

#print axioms encoded_increment
#print axioms shift_bank
#print axioms continued_prefix
#print axioms finished_prefix
#print axioms holds_append_intro
#print axioms split_ones
end Shared.Beeping.NPcoNP.NativeIncBank
