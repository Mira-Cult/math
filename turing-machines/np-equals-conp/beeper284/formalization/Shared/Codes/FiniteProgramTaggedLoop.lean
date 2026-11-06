import Shared.Codes.FiniteProgramExtendAdvance

/-! A concrete cyclic table for repeated tagged-buffer extension while a
predecessor source bit is available. This is not an end-of-input detector. -/
namespace Shared.Codes.FiniteProgramTaggedLoop
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramExtendAdvance (handoffPre branch bridge)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramLink (link shiftPair link_row)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue tape)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.CircuitTable (step_eq_executeRow)

def base (zero one : List Bool) : Program := Shared.Codes.FiniteProgramExtendAdvance.program zero one []
def stop (zero one : List Bool) : Nat := (handoffPre zero one).length+14

def program (zero one : List Bool) : Program :=
  let p := base zero one
  p.set (stop zero one) (branch p.length) ++ [bridge 0]

theorem base_valid (zero one : List Bool) : valid (base zero one) = true := by
  apply Shared.Codes.FiniteProgramExtendAdvance.program_valid zero one []
  simp

theorem base_length (zero one : List Bool) : (base zero one).length = (handoffPre zero one).length+15 := by
  simp [base,Shared.Codes.FiniteProgramExtendAdvance.program,link,
    Shared.Codes.FiniteProgramExtendAdvance.shiftProgram,Shared.Codes.FiniteProgramTaggedAdvance.program]

theorem stop_bound (zero one : List Bool) : stop zero one < (base zero one).length := by
  simp [stop,base_length]

theorem base_stop (zero one : List Bool) (t : Tape) :
    step (base zero one) (stop zero one,t) = some (.inl false) := by
  have hrow := link_row (handoffPre zero one) Shared.Codes.FiniteProgramExtendAdvance.shiftProgram [] 14
    (((false,true,0,1),(true,true,0,1)) : Row × Row) (by decide)
  have hr : rowAt (base zero one) (stop zero one,t) =
      some (if t.2.1 then (shiftPair (handoffPre zero one).length ((false,true,0,1),(true,true,0,1))).2
        else (shiftPair (handoffPre zero one).length ((false,true,0,1),(true,true,0,1))).1) := by
    simp [rowAt,base,Shared.Codes.FiniteProgramExtendAdvance.program,stop,hrow]
  rw [step_eq_executeRow _ _ _ hr]
  cases h : t.2.1 <;> simp [shiftPair,Shared.Codes.FiniteProgramLink.shiftRow,executeRow]

theorem base_other (zero one : List Bool) (d : Config)
    (hd : d.1 < (base zero one).length) (hne : d.1 ≠ stop zero one) :
    step (base zero one) d = step (program zero one) d := by
  have hlookup : (program zero one)[d.1]? = (base zero one)[d.1]? := by
    simp [program,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,hlookup]

theorem stop_row (zero one : List Bool) :
    (program zero one)[stop zero one]? = some (branch (base zero one).length) := by
  have hs := stop_bound zero one
  simp [program,List.getElem?_append_left,hs]

theorem bridge_row (zero one : List Bool) :
    (program zero one)[(base zero one).length]? = some (bridge 0) := by
  simp [program]

theorem restart (zero one : List Bool) (b : Bool) (L R : List Bool) :
    run (program zero one) (stop zero one,tapeAt L (b::false::R)) 2 =
      some (.inr (0,tapeAt L (b::false::R))) := by
  have hs := stop_row zero one
  have hb := bridge_row zero one
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape]

def output (zero one : List Bool) (b : Bool) (xs : List Bool) : List Bool :=
  xs ++ b::(if b then one else zero)

def cost (zero one : List Bool) (b : Bool) (xs : List Bool) : Nat :=
  16*xs.length+16*(if b then one else zero).length+31

/-- A real finite-table cycle extends the tagged buffer, moves to the
predecessor source bit, and returns control to state zero. -/
theorem cycle (zero one : List Bool) (b prior p : Bool) (xs L : List Bool) :
    run (program zero one) (0,tapeAt (p::L) (b::false::tagged xs ++ [false,prior,false]))
      (cost zero one b xs) =
      some (.inr (0,tapeAt L (p::false::tagged (output zero one b xs) ++ [false,false]))) := by
  have hfirst := Shared.Codes.FiniteProgramExtendAdvance.extend_advance zero one [] b prior p xs L
  dsimp only at hfirst
  change run (base zero one) (0,tapeAt (p::L) (b::false::tagged xs ++ [false,prior,false]))
    (16*xs.length+16*(if b then one else zero).length+29) =
      some (.inr (stop zero one,tapeAt L (p::false::tagged (output zero one b xs) ++ [false,false]))) at hfirst
  have hp := Shared.Codes.FiniteProgramFirstEntry.first_entry (base zero one) (program zero one)
    _ _ _ (stop zero one) false (base_valid zero one) (by simp [base_length])
    (base_stop zero one) (base_other zero one) hfirst
  have ht : cost zero one b xs = (16*xs.length+16*(if b then one else zero).length+29)+2 := by simp [cost]
  rw [ht,run_continue _ _ _ _ _ hp]
  simp only [List.cons_append]
  exact restart zero one p L (tagged (output zero one b xs) ++ [false,false])

/-- Appending an explicit blank at the far right does not change a tape. -/
theorem tapeAt_append_blank (left right : List Bool) (head : Bool) :
    TapeRel (tapeAt left (head::right)) (tapeAt left (head::(right ++ [false]))) := by
  unfold TapeRel
  change (⟨head,Turing.ListBlank.mk left,Turing.ListBlank.mk right⟩ : Turing.Tape Bool) =
    ⟨head,Turing.ListBlank.mk left,Turing.ListBlank.mk (right ++ [false])⟩
  have hr : Turing.ListBlank.mk right = Turing.ListBlank.mk (right ++ [false]) := by
    apply Quotient.sound
    exact Or.inl ⟨1,by simp⟩
  rw [hr]

def canonical (left : List Bool) (b : Bool) (xs : List Bool) : Config :=
  (0,tapeAt left (b::false::tagged xs ++ [false,false,false]))

/-- A cycle is stable under blank padding and ends related to the next
canonical configuration. -/
theorem cycle_related (zero one : List Bool) (b p : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2) :
    ∃ d, run (program zero one) c (cost zero one b xs) = some (.inr d) ∧
      d.1 = 0 ∧ TapeRel d.2 (canonical L p (output zero one b xs)).2 := by
  have h := run_related (program zero one) c (canonical (p::L) b xs) (by simpa [canonical] using hq) ht
    (cost zero one b xs)
  have hc := cycle zero one b false p xs L
  change run (program zero one) (canonical (p::L) b xs) (cost zero one b xs) = _ at hc
  rw [hc] at h
  cases hs : run (program zero one) c (cost zero one b xs) with
  | none => simp [hs,StatusRel] at h
  | some v => cases v with
    | inl out => simp [hs,StatusRel] at h
    | inr d =>
      have hd : d.1 = 0 ∧ TapeRel d.2 (tapeAt L (p::false::tagged (output zero one b xs) ++ [false,false])) := by
        simpa only [hs,StatusRel] using h
      refine ⟨d,rfl,hd.1,?_⟩
      apply Eq.trans hd.2
      have hp := tapeAt_append_blank L (false::tagged (output zero one b xs) ++ [false,false]) p
      change TapeRel (tapeAt L (p::false::tagged (output zero one b xs) ++ [false,false]))
        (canonical L p (output zero one b xs)).2
      simpa [canonical,List.append_assoc] using hp

/-- The input list gives predecessor bits nearest first. The last returned
bit remains under the head; the accumulated buffer includes metadata bits. -/
def result (zero one : List Bool) : List Bool → Bool → List Bool → Bool × List Bool
  | [], b, xs => (b,xs)
  | p::ps, b, xs => result zero one ps p (output zero one b xs)

def totalCost (zero one : List Bool) : List Bool → Bool → List Bool → Nat
  | [], _, _ => 0
  | p::ps, b, xs => cost zero one b xs + totalCost zero one ps p (output zero one b xs)

/-- For every finite list of available predecessor bits, the same concrete
table completes every cycle and returns a tape equivalent to the specified
accumulated buffer. No end-of-input decision is made by this theorem. -/
theorem cycles (zero one : List Bool) (remaining : List Bool) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    ∃ d, run (program zero one) c (totalCost zero one remaining b xs) = some (.inr d) ∧
      d.1 = 0 ∧ TapeRel d.2 (canonical L (result zero one remaining b xs).1
        (result zero one remaining b xs).2).2 := by
  induction remaining generalizing b xs c with
  | nil =>
    refine ⟨c,rfl,hq,?_⟩
    simpa [result] using ht
  | cons p ps ih =>
    have ht' : TapeRel c.2 (canonical (p::(ps++L)) b xs).2 := by simpa using ht
    obtain ⟨d,hd,hq',htape⟩ := cycle_related zero one b p xs (ps++L) c hq ht'
    obtain ⟨last,hlast,hqlast,htlast⟩ := ih p (output zero one b xs) d hq' htape
    refine ⟨last,?_,hqlast,?_⟩
    · change run (program zero one) c
        (cost zero one b xs + totalCost zero one ps p (output zero one b xs)) = some (.inr last)
      rw [run_continue _ _ _ _ _ hd]
      exact hlast
    · simpa [result] using htlast

def maxWord (zero one : List Bool) : Nat := max zero.length one.length

theorem selected_length_le (zero one : List Bool) (b : Bool) :
    (if b then one else zero).length ≤ maxWord zero one := by
  cases b <;> simp [maxWord]

theorem output_length_le (zero one : List Bool) (b : Bool) (xs : List Bool) :
    (output zero one b xs).length ≤ xs.length+1+maxWord zero one := by
  simp only [output,List.length_append,List.length_cons]
  have h := selected_length_le zero one b
  omega

/-- Uniform quadratic upper bound in the number of cycles. The fixed word
lengths and initial buffer length are explicit parameters. -/
theorem totalCost_bound (zero one : List Bool) (remaining : List Bool) (b : Bool) (xs : List Bool) :
    totalCost zero one remaining b xs ≤
      remaining.length * (16*(xs.length+remaining.length*(1+maxWord zero one)) +
        16*maxWord zero one+31) := by
  induction remaining generalizing b xs with
  | nil => simp [totalCost]
  | cons p ps ih =>
    let w := maxWord zero one
    let k := ps.length
    let bound := 16*(xs.length+(k+1)*(1+w))+16*w+31
    have hword : (if b then one else zero).length ≤ w := selected_length_le zero one b
    have hbuf : (output zero one b xs).length ≤ xs.length+1+w := output_length_le zero one b xs
    have hsize : (output zero one b xs).length+k*(1+w) ≤ xs.length+(k+1)*(1+w) := by
      rw [Nat.add_mul]
      omega
    have hlocal : cost zero one b xs ≤ bound := by
      dsimp [cost,bound]
      omega
    have hind : 16*((output zero one b xs).length+k*(1+w))+16*w+31 ≤ bound := by
      dsimp [bound]
      omega
    have hrec := ih p (output zero one b xs)
    change totalCost zero one ps p (output zero one b xs) ≤
      k * (16*((output zero one b xs).length+k*(1+w))+16*w+31) at hrec
    have hrec' : totalCost zero one ps p (output zero one b xs) ≤ k*bound :=
      le_trans hrec (Nat.mul_le_mul_left k hind)
    change cost zero one b xs + totalCost zero one ps p (output zero one b xs) ≤ (k+1)*bound
    calc
      _ ≤ bound+k*bound := Nat.add_le_add hlocal hrec'
      _ = (k+1)*bound := by simp [Nat.add_mul,Nat.add_comm]

/-- The cyclic table is valid for every pair of fixed output words. This
does not assert that malformed tapes avoid its Boolean result rows. -/
theorem program_valid (zero one : List Bool) : valid (program zero one) = true := by
  let p := base zero one
  let m := p.length+1
  have hm : (program zero one).length = m := by simp [program,m,p]
  have hold : ∀ r ∈ p, validRow p.length r.1 = true ∧ validRow p.length r.2 = true := by
    intro r hr
    have hv := base_valid zero one
    change valid p = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hr
    simpa only [Bool.and_eq_true] using h
  have hbound : p.length ≤ m := by simp [m]
  have hp : ∀ r ∈ p.set (stop zero one) (branch p.length),
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
  have hall : (program zero one).all
      (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ p.set (stop zero one) (branch p.length) ∨ r = bridge 0 := by
      simpa [program,p,List.mem_append] using hr
    rw [hm]
    rcases hr' with hp' | hb'
    · simpa only [Bool.and_eq_true] using hp r hp'
    · subst r; simpa only [Bool.and_eq_true] using hb
  have hn : (program zero one).isEmpty = false := by simp [program]
  change (!(program zero one).isEmpty && (program zero one).all
    (fun r => validRow (program zero one).length r.1 && validRow (program zero one).length r.2)) = true
  rw [hn,hall]
  rfl

namespace Fixtures
example : run (program [false] [true]) (0,tapeAt [true] [false,false,false,false,false]) 47 =
    some (.inr (0,tapeAt [] (true::false::tagged [false,false] ++ [false,false]))) := by decide
example : totalCost [false] [true] [true,false] false [] = 126 := by decide
end Fixtures

end Shared.Codes.FiniteProgramTaggedLoop
