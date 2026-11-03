import Shared.Codes.FiniteProgramWitnessController

/-! The single-input boundary for the finite-program model. The pre writes
one left sentinel, scans the complete Google encoding, and reaches the
existing three-bit reverse-block processor. It does not yet decode the tagged
output or dispatch to a completed evaluator. -/
set_option maxHeartbeats 2000000
namespace Shared.Codes.FiniteProgramSingleInput
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed consumed_cons)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.Codes.FiniteProgramWitnessPhases (witnessTape witnessSource)

/-- The first two rows mark the cell immediately left of the input. States
2--4 scan each canonical Boolean-list triple. At the first blank, state 2
moves left into state 5, the start of the relocated continuation. -/
def pre : Program :=
  [((false,false,1,0),(true,false,1,0)),
   ((true,true,2,0),(true,true,2,0)),
   ((false,false,5,0),(true,true,3,0)),
   ((false,true,4,0),(true,true,4,0)),
   ((false,true,2,0),(true,true,2,0))]

def program (zero one : List Bool) : Program :=
  link pre (Shared.Codes.FiniteProgramWitnessController.program zero one) []

@[simp] theorem pre_length : pre.length = 5 := rfl

theorem startup (zero one x : List Bool) :
    run (program zero one) (initial (BitstringEncoding.bitEncode x)) 2 =
      some (.inr (2,tapeAt [true] (BitstringEncoding.bitEncode x))) := by
  cases x with
  | nil =>
    change run (program zero one) (initial []) 2 = some (.inr (2,tapeAt [true] []))
    simp [run,advance,step,program,link,pre,initial,tapeAt,moveTape]
  | cons b xs =>
    change run (program zero one) (initial (true::b::false::BitstringEncoding.bitEncode xs)) 2 =
      some (.inr (2,tapeAt [true] (true::b::false::BitstringEncoding.bitEncode xs)))
    cases b <;> simp [run,advance,step,program,link,pre,initial,tapeAt,moveTape]

theorem scan_marker (zero one L xs : List Bool) :
    run (program zero one) (2,tapeAt L (true::xs)) 1 = some (.inr (3,tapeAt (true::L) xs)) := by
  simp [run,advance,step,program,link,pre,tapeAt,moveTape]

theorem scan_data (zero one L xs : List Bool) (b : Bool) :
    run (program zero one) (3,tapeAt L (b::xs)) 1 = some (.inr (4,tapeAt (b::L) xs)) := by
  cases b <;> simp [run,advance,step,program,link,pre,tapeAt,moveTape]

theorem scan_end (zero one L xs : List Bool) :
    run (program zero one) (4,tapeAt L (false::xs)) 1 = some (.inr (2,tapeAt (false::L) xs)) := by
  simp [run,advance,step,program,link,pre,tapeAt,moveTape]

theorem scan (zero one x L : List Bool) :
    run (program zero one) (2,tapeAt L (BitstringEncoding.bitEncode x)) (3*x.length) =
      some (.inr (2,tapeAt (consumed L (BitstringEncoding.bitEncode x)) [])) := by
  induction x generalizing L with
  | nil => rfl
  | cons b xs ih =>
    change run (program zero one) (2,tapeAt L (true::b::false::BitstringEncoding.bitEncode xs))
      (3*(xs.length+1)) = some (.inr (2,tapeAt (consumed L (true::b::false::BitstringEncoding.bitEncode xs)) []))
    rw [show 3*(xs.length+1) = 1+(1+(1+3*xs.length)) by omega]
    rw [run_continue _ _ _ 1 _ (scan_marker zero one L _)]
    rw [run_continue _ _ _ 1 _ (scan_data zero one (true::L) _ b)]
    rw [run_continue _ _ _ 1 _ (scan_end zero one (b::true::L) _)]
    simpa only [consumed_cons] using ih (false::b::true::L)

theorem enter (zero one L : List Bool) :
    run (program zero one) (2,tapeAt L []) 1 =
      some (.inr (5,tapeLeft L [false])) := by
  cases L <;> simp [run,advance,step,program,link,pre,tapeAt,tapeLeft,moveTape]

theorem scan_and_enter (zero one x : List Bool) :
    run (program zero one) (initial (BitstringEncoding.bitEncode x)) (3*x.length+3) =
      some (.inr (5,tapeLeft ((BitstringEncoding.bitEncode x).reverse ++ [true]) [false])) := by
  rw [show 3*x.length+3 = 2+(3*x.length+1) by omega,
    run_continue _ _ _ 2 _ (startup zero one x),
    run_continue _ _ _ (3*x.length) _ (scan zero one x [true]),enter]
  rfl

/-- The pre's boundary differs from the phase processor's tape only by
finitely many false padding cells. This includes the empty input. -/
theorem entry_tape (x : List Bool) :
    TapeRel (tapeLeft ((BitstringEncoding.bitEncode x).reverse ++ [true]) [false])
      (witnessTape x [] []) := by
  unfold TapeRel witnessTape witnessSource tapeLeft
  change (⟨_,Turing.ListBlank.mk _,Turing.ListBlank.mk [false]⟩ : Turing.Tape Bool) =
    ⟨_,Turing.ListBlank.mk _,Turing.ListBlank.mk [false,false,false,false]⟩
  congr 1
  apply Quotient.sound
  exact Or.inl ⟨3,by decide⟩


/-- For nonempty input, the same literal linked table proceeds from the scan
into the already-proved reverse triple processor. -/
theorem run_nonempty (zero one x : List Bool) (hne : x ≠ []) :
    ∃ d, run (program zero one) (initial (BitstringEncoding.bitEncode x))
      (3*x.length+3+Shared.Codes.FiniteProgramWitnessController.loopCost zero one x.reverse []) = some (.inr d) ∧
      d.1 = 5+Shared.Codes.FiniteProgramWitnessController.boundary zero one ∧
      TapeRel d.2 (witnessTape []
        (Shared.Codes.FiniteProgramWitnessController.loopOutput zero one x.reverse []) []) := by
  let raw := tapeLeft ((BitstringEncoding.bitEncode x).reverse ++ [true]) [false]
  let c : Config := (0,raw)
  have hne' : x.reverse ≠ [] := by simpa using hne
  have ht : TapeRel c.2 (witnessTape x.reverse.reverse [] []) := by
    simpa [c,raw] using entry_tape x
  obtain ⟨d,hd,hstate,htape⟩ := Shared.Codes.FiniteProgramWitnessController.run_blocks
    zero one x.reverse [] [] hne' c rfl ht
  let payload := Shared.Codes.FiniteProgramWitnessController.program zero one
  have hv : valid payload = true := Shared.Codes.FiniteProgramWitnessController.program_valid zero one
  have hc : c.1 < payload.length := Shared.Codes.FiniteProgramLink.valid_nonempty payload hv
  have hshift := run_shift pre payload [] hv c hc
    (Shared.Codes.FiniteProgramWitnessController.loopCost zero one x.reverse [])
  rw [hd] at hshift
  change run (program zero one) (5,raw) _ = some (.inr (shiftConfig 5 d)) at hshift
  refine ⟨shiftConfig 5 d,?_,?_,?_⟩
  · rw [run_continue _ _ _ _ _ (scan_and_enter zero one x)]
    exact hshift
  · change 5+d.1 = 5+Shared.Codes.FiniteProgramWitnessController.boundary zero one
    rw [hstate]
  · exact htape

/-- The explicit scan-and-processing charge is quadratic in the input length
for fixed output words. -/
def costBound (zero one : List Bool) (n : Nat) : Nat :=
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
  let gain := 3*(1+w)
  3*n+3+n*(3*(16*(n*gain+gain)+16*w+31)+4)

theorem cost_bound (zero one x : List Bool) :
    3*x.length+3+Shared.Codes.FiniteProgramWitnessController.loopCost zero one x.reverse [] ≤
      costBound zero one x.length := by
  have h := Shared.Codes.FiniteProgramWitnessController.loopCost_bound zero one x.reverse []
  simp only [List.length_reverse,List.length_nil,zero_add] at h
  dsimp [costBound]
  omega


/-- With one-bit output words, a triple emits exactly the reverse of its
six-bit contribution to the pair encoding. -/
theorem groupOutput_pair (b : Bool) (xs : List Bool) :
    Shared.Codes.FiniteProgramWitnessController.groupOutput [true] [true] b xs =
      xs ++ [false,true,b,true,true,true] := by
  cases b <;> simp [Shared.Codes.FiniteProgramWitnessController.groupOutput,
    Shared.Codes.FiniteProgramWitnessPhases.witnessOutput,
    Shared.Codes.FiniteProgramWitnessPhases.witnessPred,
    Shared.Codes.FiniteProgramTaggedLoop.result,
    Shared.Codes.FiniteProgramTaggedLoop.output,List.append_assoc]

def reverseBlock (b : Bool) : List Bool := [false,true,b,true,true,true]

theorem loopOutput_pair (todo xs : List Bool) :
    Shared.Codes.FiniteProgramWitnessController.loopOutput [true] [true] todo xs =
      xs ++ todo.flatMap reverseBlock := by
  induction todo generalizing xs with
  | nil => simp [Shared.Codes.FiniteProgramWitnessController.loopOutput]
  | cons b bs ih =>
    simp [Shared.Codes.FiniteProgramWitnessController.loopOutput, groupOutput_pair,
      ih, reverseBlock,List.append_assoc]

theorem pair_bits_reverse (x : List Bool) :
    false :: x.reverse.flatMap reverseBlock =
      (BitstringEncoding.bitEncode (x,([] : List Bool))).reverse := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    have he : BitstringEncoding.bitEncode ((b::xs),([] : List Bool)) =
        [true,true,true,b,true,false] ++ BitstringEncoding.bitEncode (xs,([] : List Bool)) := by
      rfl
    rw [he,List.reverse_append]
    simp only [List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.reverse_nil,List.nil_append]
    rw [←ih]
    simp [reverseBlock]

theorem pair_output (x : List Bool) :
    false :: Shared.Codes.FiniteProgramWitnessController.loopOutput [true] [true] x.reverse [] =
      (BitstringEncoding.bitEncode (x,([] : List Bool))).reverse := by
  simpa [loopOutput_pair] using pair_bits_reverse x


/-- The literal prefix and relocated processor form a valid finite table. -/
theorem program_valid (zero one : List Bool) : valid (program zero one) = true := by
  let body := Shared.Codes.FiniteProgramWitnessController.program zero one
  let m := 5+body.length
  have hv : valid body = true := Shared.Codes.FiniteProgramWitnessController.program_valid zero one
  have hn : 0 < body.length := Shared.Codes.FiniteProgramLink.valid_nonempty body hv
  have hl : (program zero one).length = m := by simp [program,link,pre_length,m,body]
  have hb : ∀ row ∈ body, validRow body.length row.1 = true ∧ validRow body.length row.2 = true := by
    intro row hr
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 row hr
  have hp : ∀ row ∈ pre, validRow m row.1 = true ∧ validRow m row.2 = true := by
    intro row hr
    have hm : 5 < m := by dsimp [m]; omega
    have hh : pre.all (fun row => validRow m row.1 && validRow m row.2) = true := by
      simp [pre,validRow,hm]; omega
    simpa only [Bool.and_eq_true] using ((List.all_eq_true.mp hh) row hr)
  have hall : (program zero one).all
      (fun row => validRow (program zero one).length row.1 &&
        validRow (program zero one).length row.2) = true := by
    apply List.all_eq_true.mpr
    intro row hr
    have hr' : row ∈ pre ∨ row ∈ body.map (shiftPair 5) := by
      simpa [program,link,pre_length,body] using hr
    rw [hl]
    rcases hr' with hp' | hm'
    · simpa only [Bool.and_eq_true] using hp row hp'
    · obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hm'
      obtain ⟨h₁,h₂⟩ := hb r hm
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r.1 5 body.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r.2 5 body.length h₂⟩
  have hnon : (program zero one).isEmpty = false := by simp [program,link,pre]
  change (!(program zero one).isEmpty && (program zero one).all
    (fun row => validRow (program zero one).length row.1 &&
      validRow (program zero one).length row.2)) = true
  rw [hnon,hall]
  rfl


/-- The produced tagged buffer is exactly the reversed canonical pair input,
without its final delimiter blank. -/
theorem run_nonempty_pair (x : List Bool) (hne : x ≠ []) :
    ∃ d, run (program [true] [true]) (initial (BitstringEncoding.bitEncode x))
      (3*x.length+3+Shared.Codes.FiniteProgramWitnessController.loopCost [true] [true] x.reverse []) = some (.inr d) ∧
      d.1 = 5+Shared.Codes.FiniteProgramWitnessController.boundary [true] [true] ∧
      TapeRel d.2 (witnessTape []
        ((BitstringEncoding.bitEncode (x,([] : List Bool))).reverse.tail) []) := by
  obtain ⟨d,hr,hq,ht⟩ := run_nonempty [true] [true] x hne
  have hout := congrArg List.tail (pair_output x)
  simp only [List.tail_cons] at hout
  exact ⟨d,hr,hq,by simpa [hout] using ht⟩

noncomputable def costPolynomial (zero one : List Bool) : Polynomial Nat :=
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
  let gain := 3*(1+w)
  Polynomial.C 3 * Polynomial.X + Polynomial.C 3 + Polynomial.X *
    (Polynomial.C 3 * (Polynomial.C 16 *
      (Polynomial.X * Polynomial.C gain + Polynomial.C gain) + Polynomial.C (16*w+31)) + Polynomial.C 4)

theorem costPolynomial_eval (zero one : List Bool) (n : Nat) :
    (costPolynomial zero one).eval n = costBound zero one n := by
  simp [costPolynomial,costBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X]
  omega

/-- One fixed exponent pays for every single-input scan and reverse-block
processing stage, measured on the actual encoded input length. -/
theorem cost_fixed_exponent (zero one : List Bool) : ∃ k : Nat, ∀ x : List Bool,
    3*x.length+3+Shared.Codes.FiniteProgramWitnessController.loopCost zero one x.reverse [] ≤
      ((BitstringEncoding.bitEncode x).length+2)^k := by
  obtain ⟨k,hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent (costPolynomial zero one)
  refine ⟨k,fun x => ?_⟩
  have hinput : x.length ≤ (BitstringEncoding.bitEncode x).length := by
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length]
    omega
  calc
    _ ≤ costBound zero one x.length := cost_bound zero one x
    _ = (costPolynomial zero one).eval x.length := (costPolynomial_eval zero one x.length).symm
    _ ≤ (x.length+2)^k := hk x.length
    _ ≤ ((BitstringEncoding.bitEncode x).length+2)^k := Nat.pow_le_pow_left (by omega) k


namespace Fixtures
example : run (program [true] [true]) (initial (BitstringEncoding.bitEncode ([] : List Bool))) 3 =
    some (.inr (5,tapeLeft [true] [false])) := by
  have h := scan_and_enter [true] [true] []
  change run (program [true] [true]) (initial (BitstringEncoding.bitEncode ([] : List Bool))) 3 =
    some (.inr (5,tapeLeft [true] [false])) at h
  exact h
example : run (program [true] [true]) (initial (BitstringEncoding.bitEncode [false,true])) 9 =
    some (.inr (5,tapeLeft ((BitstringEncoding.bitEncode [false,true]).reverse ++ [true]) [false])) := by
  simpa using scan_and_enter [true] [true] [false,true]
example : false :: Shared.Codes.FiniteProgramWitnessController.loopOutput [true] [true] [true,false] [] =
    (BitstringEncoding.bitEncode ([false,true],([] : List Bool))).reverse := by
  simpa using pair_output [false,true]
example : valid (program [true] [true]) = true := program_valid [true] [true]
end Fixtures

end Shared.Codes.FiniteProgramSingleInput
