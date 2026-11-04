import Shared.PNP.Record285.PythonControlSkip
import Shared.PNP.Record285.PythonInlineDecoder

/-! The actual typed carry-decoder loop. This is part of the partial source
control-flow model; it is not yet an unbounded controller refinement. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlDecode
open Shared.Beeping
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip

def decodeLoop : List Loop := ⟨100,111⟩::context

def guard (s : Store) : Status := .live ⟨111,s,decodeLoop⟩
def entry (s : Store) : Status := .live ⟨100,s,context⟩
def exit (s : Store) : Status := .live ⟨111,s,context⟩

theorem rows : code[99]? = lines19[4]? ∧
    code[100]? = lines20[0]? ∧ code[101]? = lines20[1]? ∧
    code[102]? = lines20[2]? ∧ code[103]? = lines20[3]? ∧ code[104]? = lines20[4]? ∧
    code[105]? = lines21[0]? ∧ code[106]? = lines21[1]? ∧ code[107]? = lines21[2]? ∧
    code[108]? = lines21[3]? ∧ code[109]? = lines21[4]? ∧
    code[110]? = lines22[0]? ∧ code[111]? = lines22[1]? := by decide

theorem flow : seek code 101 16 = 111 ∧ jumpFalse code 102 20 = 110 ∧
    jumpFalse code 104 24 = 108 ∧ seek code 108 24 = 109 ∧
    seek code 110 20 = 111 := by decide

/-- Exact full-store effect of one Python carry iteration. -/
def cycleStore (s : Store) : Store :=
  let halved := put s "digit" (s "digit"/2)
  if s "write" = 0 then put halved "write" 1
  else if s "direction" = 0 then put (put halved "write" 0) "direction" 1
  else put (put (put halved "write" 0) "direction" 0) "state" (s "state"+1)

theorem guard_even (s : Store) (h : s "digit"%2=0) :
    Silent (guard s) (exit s) 1 := by
  constructor
  · simp [Silent,pySystem,EventSystem.advance,step,guard,exit,decodeLoop,context,
      settle,advance,rows,lines20,eval,op,flow,h]
  · intro t ht
    have ht0 : t=0 := by omega
    subst t
    simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,guard,decodeLoop,context,
      settle,advance,rows,lines20,eval,op,flow,h]

/-- A single odd iteration takes one of three finite silent paths according
to the carry bits, with its exact complete-store result. -/
theorem guard_odd (s : Store) (h : s "digit"%2=1) :
    ∃ n, 0 < n ∧ Silent (guard s) (guard (cycleStore s)) n := by
  by_cases hw : s "write"=0
  · refine ⟨4,by decide,?_⟩
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,guard,decodeLoop,context,settle,
        advance,rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,cycleStore]
    · intro t ht
      have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
      rcases hc with rfl|rfl|rfl|rfl <;>
        simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,guard,decodeLoop,context,
          settle,advance,rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw]
  · by_cases hd : s "direction"=0
    · refine ⟨7,by decide,?_⟩
      constructor
      · simp [Silent,pySystem,EventSystem.advance,step,guard,decodeLoop,context,settle,
          advance,rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd,cycleStore]
      · intro t ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,guard,decodeLoop,context,
            settle,advance,rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd]
    · refine ⟨9,by decide,?_⟩
      constructor
      · simp [Silent,pySystem,EventSystem.advance,step,guard,decodeLoop,context,settle,
          advance,rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd,cycleStore]
      · intro t ht
        have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 := by omega
        rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,guard,decodeLoop,context,
            settle,advance,rows,lines20,lines21,lines22,eval,op,simple,augOp,flow,put,h,hw,hd]

/-- Store a binary carry accumulator while preserving every other entry. -/
def storeOf (s : Store) (digit : Nat) (d : PythonInlineDecoder.Digits) : Store :=
  put (put (put (put s "digit" digit) "write" (if d.write then 1 else 0))
    "direction" (if d.direction then 1 else 0)) "state" d.state

@[simp] theorem store_digit (s : Store) (digit : Nat) (d : PythonInlineDecoder.Digits) :
    storeOf s digit d "digit" = digit := by simp [storeOf,put]

theorem cycle_storeOf (s : Store) (digit : Nat) (d : PythonInlineDecoder.Digits) :
    cycleStore (storeOf s digit d) =
      storeOf s (digit/2) (PythonInlineDecoder.bump d) := by
  rcases d with ⟨w,dir,n⟩
  cases w <;> cases dir <;> funext key <;>
    by_cases hdigit : key="digit" <;> by_cases hw : key="write" <;>
    by_cases hdir : key="direction" <;> by_cases hstate : key="state" <;>
    simp [cycleStore,storeOf,PythonInlineDecoder.bump,put,hdigit,hw,hdir,hstate]

/-- All carry iterations terminate, preserving the complete store and
leaving the even delimiter for the following line. -/
theorem decode_loop (digit : Nat) (s : Store) (d : PythonInlineDecoder.Digits) :
    ∃ n, 0 < n ∧ Silent (guard (storeOf s digit d))
      (exit (storeOf s (2*(popUnary digit).2)
        (PythonInlineDecoder.bumpN (popUnary digit).1 d))) n := by
  induction digit using Nat.strongRecOn generalizing s d with
  | ind digit ih =>
    by_cases ho : digit%2=1
    · have hp : 0 < digit := by omega
      obtain ⟨n,hn,hfirst⟩ := guard_odd (storeOf s digit d) (by simpa using ho)
      rw [cycle_storeOf] at hfirst
      obtain ⟨m,hm,hrest⟩ := ih (digit/2) (by omega) s (PythonInlineDecoder.bump d)
      have h := silent_trans hfirst hrest
      have hpop : popUnary digit = ((popUnary (digit/2)).1+1,(popUnary (digit/2)).2) := by
        rw [popUnary]; simp [ho]
      refine ⟨n+m,by omega,?_⟩
      rw [hpop]
      simpa [PythonInlineDecoder.bumpN] using h
    · have he : digit%2=0 := by omega
      have hdigit : 2*(digit/2) = digit := by omega
      have hpop : popUnary digit = (0,digit/2) := by rw [popUnary]; simp [ho]
      refine ⟨1,by decide,?_⟩
      rw [hpop]
      simpa [PythonInlineDecoder.bumpN,hdigit] using
        guard_even (storeOf s digit d) (by simpa using he)

theorem entry_step (s : Store) : pySystem.step (entry s) = pySystem.step (guard s) := by rfl

theorem decode_from_entry (digit : Nat) (s : Store) (d : PythonInlineDecoder.Digits) :
    ∃ n, 0 < n ∧ Silent (entry (storeOf s digit d))
      (exit (storeOf s (2*(popUnary digit).2)
        (PythonInlineDecoder.bumpN (popUnary digit).1 d))) n := by
  obtain ⟨n,hn,h⟩ := decode_loop digit s d
  exact ⟨n,hn,same_silent (entry_step _) hn h⟩

/-- Initialization, the whole carry loop, and delimiter consumption reach
row 112 with the exact decoded digits and complete retained store. -/
theorem candidate_decode_terminates (s : Store) :
    ∃ n, 0 < n ∧ Silent (outerExit s)
      (.live ⟨112,storeOf s (popUnary (s "digit")).2
        (PythonInlineDecoder.bumpN (popUnary (s "digit")).1 ⟨false,false,0⟩),context⟩) n := by
  let zero : PythonInlineDecoder.Digits := ⟨false,false,0⟩
  have hinit : Silent (outerExit s) (entry (storeOf s (s "digit") zero)) 1 := by
    have heffect : put (put (put s "write" 0) "direction" 0) "state" 0 =
        storeOf s (s "digit") zero := by
      funext key
      by_cases hd : key="digit" <;> by_cases hw : key="write" <;>
        by_cases hr : key="direction" <;> by_cases hs : key="state" <;>
        simp [storeOf,zero,put,hd,hw,hr,hs]
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,outerExit,entry,context,settle,advance,
        rows,lines19,simple,values,eval,assignAll,heffect]
    · intro t ht
      have ht0 : t=0 := by omega
      subst t
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,outerExit,context,
        settle,advance,rows,lines19,simple,values,eval,assignAll]
  obtain ⟨m,hm,hloop⟩ := decode_from_entry (s "digit") s zero
  let d := PythonInlineDecoder.bumpN (popUnary (s "digit")).1 zero
  let after := storeOf s (2*(popUnary (s "digit")).2) d
  have hlast : Silent (exit after) (.live ⟨112,storeOf s (popUnary (s "digit")).2 d,context⟩) 1 := by
    have heffect : put after "digit" (after "digit"/2) = storeOf s (popUnary (s "digit")).2 d := by
      funext key
      by_cases hd : key="digit" <;> by_cases hw : key="write" <;>
        by_cases hr : key="direction" <;> by_cases hs : key="state" <;>
        simp [after,storeOf,put,hd,hw,hr,hs]
    constructor
    · simp [Silent,pySystem,EventSystem.advance,step,exit,context,settle,advance,
        rows,lines22,simple,eval,op,augOp,heffect]
    · intro t ht
      have ht0 : t=0 := by omega
      subst t
      simp [pySystem,EventSystem.BeepFrom,EventSystem.advance,step,exit,context,
        settle,advance,rows,lines22,simple,eval,op,augOp]
  have h := silent_trans (silent_trans hinit hloop) hlast
  refine ⟨1+m+1,by omega,?_⟩
  simpa [after,d,zero] using h

/-- The complete typed record-selection and carry-decoding block terminates
silently for arbitrary finite input and preserves every other store entry. -/
theorem candidate_record_terminates (s : Store) :
    let stream := skipUnary (s "state") (s "digit")
    ∃ n, 0 < n ∧ Silent (.live ⟨94,s,context⟩)
      (.live ⟨112,storeOf s (popUnary stream).2
        (PythonInlineDecoder.bumpN (popUnary stream).1 ⟨false,false,0⟩),context⟩) n := by
  let stream := skipUnary (s "state") (s "digit")
  let mid := put (put s "state" 0) "digit" stream
  have hmid : mid "digit" = stream := by simp [mid,put]
  obtain ⟨n,hn,hskip⟩ := candidate_skip_terminates s
  obtain ⟨m,hm,hdecode⟩ := candidate_decode_terminates mid
  rw [hmid] at hdecode
  have heffect (tail : Nat) (d : PythonInlineDecoder.Digits) :
      storeOf mid tail d = storeOf s tail d := by
    funext key
    by_cases hd : key="digit" <;> by_cases hw : key="write" <;>
      by_cases hr : key="direction" <;> by_cases hs : key="state" <;>
      simp [mid,storeOf,put,hd,hw,hr,hs]
  rw [heffect] at hdecode
  refine ⟨n+m,by omega,?_⟩
  exact silent_trans hskip hdecode

/-- The decoded store has the source action's exact write bit, direction,
next state and post-record digit. -/
theorem candidate_record_fields (s : Store) :
    let stream := skipUnary (s "state") (s "digit")
    let record := popUnary stream
    ∃ n out, 0 < n ∧ Silent (.live ⟨94,s,context⟩) (.live ⟨112,out,context⟩) n ∧
      out "write" = record.1%2 ∧ out "direction" = (record.1/2)%2 ∧
      out "state" = record.1/4 ∧ out "digit" = record.2 ∧
      ∀ key, key ≠ "write" → key ≠ "direction" → key ≠ "state" → key ≠ "digit" → out key = s key := by
  let stream := skipUnary (s "state") (s "digit")
  let d := PythonInlineDecoder.bumpN (popUnary stream).1 ⟨false,false,0⟩
  let out := storeOf s (popUnary stream).2 d
  obtain ⟨n,hn,hsegment⟩ := candidate_record_terminates s
  have hf := PythonInlineDecoder.read_fields stream
  rw [PythonInlineDecoder.read_correct] at hf
  change (if d.write then 1 else 0) = (popUnary stream).1%2 ∧
    (if d.direction then 1 else 0) = ((popUnary stream).1/2)%2 ∧
    d.state = (popUnary stream).1/4 ∧ _ at hf
  refine ⟨n,out,hn,hsegment,?_,?_,?_,?_,?_⟩
  · simpa [out,storeOf,put] using hf.1
  · simpa [out,storeOf,put] using hf.2.1
  · simpa [out,storeOf,put] using hf.2.2.1
  · simp [out,storeOf,put,stream]
  · intro key hw hd hs hdi
    simp [out,storeOf,put,hw,hd,hs,hdi]

end Shared.PNP.Record285.PythonControlDecode
