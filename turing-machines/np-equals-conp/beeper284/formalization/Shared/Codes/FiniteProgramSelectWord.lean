import Shared.Codes.FiniteProgramWriteWord

/-! Finite-table selection of one of two fixed code words by a live tape bit.
The table preserves that source cell, moves right, and writes the selected
word. The caller must establish that overwriting the target region is safe. -/
namespace Shared.Codes.FiniteProgramSelectWord
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramWriteWord (writeTape)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def outRow (bit : Bool) (next : Nat) : Row × Row :=
  ((bit,true,next,0),(bit,true,next,0))

/-- A nonempty word finishes at `dest`, not necessarily the next row. -/
def outRows : Nat → List Bool → Nat → Program
  | _, [], _ => []
  | _, [b], dest => [outRow b dest]
  | q, b::c::bs, dest => outRow b (q+1) :: outRows (q+1) (c::bs) dest

theorem outRows_length (q : Nat) (bs : List Bool) (dest : Nat) :
    (outRows q bs dest).length = bs.length := by
  induction bs generalizing q with
  | nil => rfl
  | cons b bs ih => cases bs with
    | nil => rfl
    | cons c cs => simpa [outRows] using ih (q+1)

theorem out_step (pre suffix : Program) (b : Bool) (bs : List Bool) (dest : Nat) (t : Tape) :
    step (pre ++ outRows pre.length (b::bs) dest ++ suffix) (pre.length,t) =
      some (.inr (if bs.isEmpty then dest else pre.length+1,moveTape false b t)) := by
  cases bs <;> simp [step,outRows,outRow]

/-- For a nonempty generated word, each bit is written in one transition;
the final row goes directly to `dest` without an uncharged jump. -/
theorem out_run (pre suffix : Program) (b : Bool) (bs : List Bool) (dest : Nat) (t : Tape) :
    run (pre ++ outRows pre.length (b::bs) dest ++ suffix) (pre.length,t) (b::bs).length =
      some (.inr (dest,writeTape (b::bs) t)) := by
  induction bs generalizing pre b t with
  | nil =>
    simpa [run,advance,writeTape,outRows] using out_step pre suffix b [] dest t
  | cons c cs ih =>
    let pre' : Program := pre ++ [outRow b (pre.length+1)]
    have heq : pre ++ outRows pre.length (b::c::cs) dest ++ suffix =
        pre' ++ outRows pre'.length (c::cs) dest ++ suffix := by
      simp [pre',outRows,List.append_assoc]
    rw [show (b::c::cs).length = 1+(c::cs).length by simp [Nat.add_comm]]
    rw [run_continue _ _ _ 1 _ (out_step pre suffix b (c::cs) dest t)]
    rw [heq]
    simpa [pre',writeTape] using ih pre' c (moveTape false b t)

/-- Every emitted row is valid when the allocated interval and its explicit
destination lie inside the enclosing table. -/
theorem outRows_valid (q : Nat) (bs : List Bool) (dest m : Nat)
    (hinterval : q+bs.length ≤ m) (hdest : dest < m) :
    ∀ r ∈ outRows q bs dest, validRow m r.1 = true ∧ validRow m r.2 = true := by
  induction bs generalizing q with
  | nil => simp [outRows]
  | cons b bs ih =>
    cases bs with
    | nil =>
      simp [outRows,outRow,validRow,hdest]
    | cons c cs =>
      intro r hr
      simp only [outRows,List.mem_cons] at hr
      cases hr with
      | inl he =>
        subst r
        have hnext : q+1 < m := by simp at hinterval; omega
        simp [outRow,validRow,hnext]
      | inr hr =>
        apply ih (q+1) (by simp at hinterval ⊢; omega) r hr

def finish (q : Nat) (zero one : List Bool) : Nat := q+1+zero.length+one.length

def dispatch (q : Nat) (zero one : List Bool) : Row × Row :=
  ((false,true,if zero.isEmpty then finish q zero one else q+1,0),
   (true,true,if one.isEmpty then finish q zero one else q+1+zero.length,0))

/-- The two word paths are finite table rows; the original bit selects one. -/
def selectRows (q : Nat) (zero one : List Bool) : Program :=
  dispatch q zero one ::
    (outRows (q+1) zero (finish q zero one) ++
      outRows (q+1+zero.length) one (finish q zero one))

theorem selectRows_length (q : Nat) (zero one : List Bool) :
    (selectRows q zero one).length = 1+zero.length+one.length := by
  simp [selectRows,outRows_length]
  omega

/-- The selector has valid jumps when at least one continuation row follows
its two code-word paths. -/
theorem selectRows_valid (q : Nat) (zero one : List Bool) (extra : Nat) (hextra : 0 < extra) :
    ∀ r ∈ selectRows q zero one,
      validRow (finish q zero one+extra) r.1 = true ∧
        validRow (finish q zero one+extra) r.2 = true := by
  let m := finish q zero one+extra
  have hd : finish q zero one < m := by simp [m]; omega
  have hzero : q+1+zero.length ≤ m := by simp [m,finish]; omega
  have hone : q+1+zero.length+one.length ≤ m := by simp [m,finish]
  have hz := outRows_valid (q+1) zero (finish q zero one) m hzero hd
  have ho := outRows_valid (q+1+zero.length) one (finish q zero one) m hone hd
  intro r hr
  simp only [selectRows,List.mem_cons,List.mem_append] at hr
  rcases hr with he | hzmem | homem
  · subst r
    have hfirst : q+1 < m := by simp [m,finish]; omega
    have hsecond : q+1+zero.length < m := by simp [m,finish]; omega
    cases h₀ : zero.isEmpty <;> cases h₁ : one.isEmpty <;>
      simp [dispatch,validRow,h₀,h₁] <;> dsimp [m] at * <;> omega
  · exact hz r hzmem
  · exact ho r homem

/-- Assemble a valid enclosing table when its independently supplied prefix
and nonempty continuation have valid rows at the final table length. -/
theorem valid_assembly (pre suffix : Program) (zero one : List Bool)
    (hextra : 0 < suffix.length)
    (hpre : ∀ r ∈ pre, validRow (finish pre.length zero one+suffix.length) r.1 = true ∧
      validRow (finish pre.length zero one+suffix.length) r.2 = true)
    (hsuffix : ∀ r ∈ suffix, validRow (finish pre.length zero one+suffix.length) r.1 = true ∧
      validRow (finish pre.length zero one+suffix.length) r.2 = true) :
    valid (pre ++ selectRows pre.length zero one ++ suffix) = true := by
  let p := pre ++ selectRows pre.length zero one ++ suffix
  have hm : p.length = finish pre.length zero one+suffix.length := by
    simp [p,selectRows_length,finish]
    omega
  have hs := selectRows_valid pre.length zero one suffix.length hextra
  have hall : p.all (fun r => validRow p.length r.1 && validRow p.length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ pre ∨ r ∈ selectRows pre.length zero one ∨ r ∈ suffix := by
      simpa [p,List.mem_append] using hr
    rcases hr' with hp | hs' | ht
    · simpa [hm] using (hpre r hp)
    · simpa [hm] using (hs r hs')
    · simpa [hm] using (hsuffix r ht)
  have hn : p.isEmpty = false := by simp [p,selectRows]
  change (!p.isEmpty && p.all (fun r => validRow p.length r.1 && validRow p.length r.2)) = true
  rw [hn,hall]
  rfl

theorem dispatch_step (pre suffix : Program) (zero one : List Bool) (t : Tape) :
    step (pre ++ selectRows pre.length zero one ++ suffix) (pre.length,t) =
      some (.inr (if t.2.1 then
          (if one.isEmpty then finish pre.length zero one else pre.length+1+zero.length)
        else (if zero.isEmpty then finish pre.length zero one else pre.length+1),
        moveTape false t.2.1 t)) := by
  cases h : t.2.1 <;> simp [step,selectRows,dispatch,h]

/-- The false branch consumes one dispatch step and one step per code bit. -/
theorem select_false (pre suffix : Program) (zero one : List Bool) (t : Tape)
    (hbit : t.2.1 = false) :
    run (pre ++ selectRows pre.length zero one ++ suffix) (pre.length,t) (1+zero.length) =
      some (.inr (finish pre.length zero one,writeTape zero (moveTape false false t))) := by
  cases zero with
  | nil =>
    simpa [run,advance,writeTape,hbit] using dispatch_step pre suffix [] one t
  | cons b bs =>
    let pre' := pre ++ [dispatch pre.length (b::bs) one]
    have heq : pre ++ selectRows pre.length (b::bs) one ++ suffix =
        pre' ++ outRows pre'.length (b::bs) (finish pre.length (b::bs) one) ++
          (outRows (pre.length+1+(b::bs).length) one (finish pre.length (b::bs) one) ++ suffix) := by
      simp [pre',selectRows,List.append_assoc]
    have hd := dispatch_step pre suffix (b::bs) one t
    simp only [hbit,Bool.false_eq_true,reduceIte,List.isEmpty_cons] at hd
    rw [run_continue _ _ _ 1 _ hd,heq]
    simpa [pre'] using out_run pre'
      (outRows (pre.length+1+(b::bs).length) one (finish pre.length (b::bs) one) ++ suffix)
      b bs (finish pre.length (b::bs) one) (moveTape false false t)

/-- The true branch likewise skips the unselected word rows and reaches the
same continuation after one dispatch step plus its own word length. -/
theorem select_true (pre suffix : Program) (zero one : List Bool) (t : Tape)
    (hbit : t.2.1 = true) :
    run (pre ++ selectRows pre.length zero one ++ suffix) (pre.length,t) (1+one.length) =
      some (.inr (finish pre.length zero one,writeTape one (moveTape false true t))) := by
  cases one with
  | nil =>
    simpa [run,advance,writeTape,hbit] using dispatch_step pre suffix zero [] t
  | cons b bs =>
    let pre' := pre ++ [dispatch pre.length zero (b::bs)] ++
      outRows (pre.length+1) zero (finish pre.length zero (b::bs))
    have hlen : pre'.length = pre.length+1+zero.length := by simp [pre',outRows_length]; omega
    have heq : pre ++ selectRows pre.length zero (b::bs) ++ suffix =
        pre' ++ outRows pre'.length (b::bs) (finish pre.length zero (b::bs)) ++ suffix := by
      simp [pre',selectRows,outRows_length,List.append_assoc,Nat.add_comm,Nat.add_left_comm]
    have hd := dispatch_step pre suffix zero (b::bs) t
    simp only [hbit,reduceIte,List.isEmpty_cons] at hd
    rw [run_continue _ _ _ 1 _ hd,heq]
    simpa [hlen] using out_run pre' suffix b bs (finish pre.length zero (b::bs)) (moveTape false true t)

theorem select_run (pre suffix : Program) (zero one : List Bool) (t : Tape) :
    let word := if t.2.1 then one else zero
    run (pre ++ selectRows pre.length zero one ++ suffix) (pre.length,t) (1+word.length) =
      some (.inr (finish pre.length zero one,writeTape word (moveTape false t.2.1 t))) := by
  cases h : t.2.1 with
  | false => simpa [h] using select_false pre suffix zero one t h
  | true => simpa [h] using select_true pre suffix zero one t h

/-- With blank workspace immediately to the right, the source bit is retained
and the selected word is laid down next to it. -/
theorem select_run_blank (pre suffix : Program) (zero one left : List Bool) (bit : Bool) :
    let word := if bit then one else zero
    run (pre ++ selectRows pre.length zero one ++ suffix) (pre.length,(left,bit,[false]))
        (1+word.length) =
      some (.inr (finish pre.length zero one,(word.reverse ++ bit::left,false,[]))) := by
  have h := select_run pre suffix zero one (left,bit,[false])
  simpa [moveTape,Shared.Codes.FiniteProgramWriteWord.writeTape_blank] using h

namespace Fixtures
example : run (selectRows 0 [true,false] [false,true,true]) (0,([],false,[false])) 3 =
    some (.inr (6,([false,true,false],false,[]))) := by decide
example : run (selectRows 0 [true,false] [false,true,true]) (0,([],true,[false])) 4 =
    some (.inr (6,([true,true,false,true],false,[]))) := by decide
example : run (selectRows 0 [] [true]) (0,([],false,[false])) 1 =
    some (.inr (2,([false],false,[]))) := by decide
example : run (selectRows 0 [true] []) (0,([],true,[false])) 1 =
    some (.inr (2,([true],false,[]))) := by decide
end Fixtures

end Shared.Codes.FiniteProgramSelectWord
