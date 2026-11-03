import Shared.ComplexityBridge.TM2WitnessComplete

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2WitnessLookup
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program

theorem start_delimit (v tail : List Bool) (b bit matched : Bool) (flag : Option Bool) (witness query : List Bool) :
    machine.step (cfg .start bit matched flag (BitstringEncoding.delimit v ++ tail) (b::witness) query [] [] []) =
      some (pemb b false (stackVals [] witness query [] [] []) (Turing.initList Parse (BitstringEncoding.delimit v ++ tail))) := by
  cases v with
  | nil => exact start_cons false b bit matched flag tail witness query
  | cons x xs => exact start_cons true b bit matched flag (x::BitstringEncoding.delimit xs ++ tail) witness query

theorem iteration_raw (v tail : List Bool) (b bit matched : Bool) (flag : Option Bool)
    (witness query : List Bool) :
    ∃ t ≤ 8*(v.length+query.length+2) + 2*((v.length+query.length+2)*Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare),
      runSteps machine.step t (cfg .start bit matched flag (BitstringEncoding.delimit v ++ tail) (b::witness) query [] [] []) =
        some (cfg (if Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v) then (if b then .yes else .no) else .start)
          b (Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v)) none tail witness query [] [] []) := by
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Compare
  let otherP := stackVals [] witness query [] [] []
  let otherC := stackVals tail witness query [] [] []
  let sourceStart := Turing.initList Parse (BitstringEncoding.delimit v ++ tail)
  let sourceEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] v
  have hparse := Shared.ComplexityBridge.TM2Undelimit.valid_run v tail
  change runSteps Parse.step (3*v.length+2) sourceStart = some sourceEnd at hparse
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Parse.step machine.step (pemb b false otherP) pTerminal pStable (pStep b false otherP)
    (3*v.length+2) sourceStart sourceEnd (Or.inl rfl) hparse
  let cmpStart := Shared.ComplexityBridge.TM2NumeralCompare.cfg .scan (none,none,none) v query
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2NumeralCompare.compare_progress v query
  change runSteps Compare.step n cmpStart = some q at hr
  have hterm : cTerminal q := by
    unfold cTerminal
    by_cases he : Computability.decodeNat v = Computability.decodeNat query
    · left; simpa [he] using hq
    · right; simpa [he] using hq
  obtain ⟨c,hc,hcr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Compare.step machine.step (cemb b false otherC) cTerminal cStable (cStep b false otherC)
    n cmpStart q hterm hr
  let result := Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v)
  have hresult : q.l = some (if result then .accept else .reject) := by
    by_cases he : Computability.decodeNat query = Computability.decodeNat v
    · have hz : result = true := (Shared.ComplexityBridge.TM2NumeralPairCompare.answer_correct query v).2 he
      simp [hz,he.symm] at hq ⊢
      exact hq
    · have hz : result = false := by
        cases hv : result with
        | false => rfl
        | true => exact False.elim (he ((Shared.ComplexityBridge.TM2NumeralPairCompare.answer_correct query v).1 hv))
      have he' : Computability.decodeNat v ≠ Computability.decodeNat query := Ne.symm he
      simp [hz,he'] at hq ⊢
      exact hq
  have hn' : n ≤ v.length+query.length+2 := by have hh := max_le (Nat.le_add_right v.length query.length) (Nat.le_add_left query.length v.length); omega
  have hmul : n*D ≤ (v.length+query.length+2)*D := Nat.mul_le_mul_right D hn'
  have hleft := Shared.ComplexityBridge.TM2GenericStackBound.run_length Compare n cmpStart q hr .left
  have hright := Shared.ComplexityBridge.TM2GenericStackBound.run_length Compare n cmpStart q hr .right
  change (q.stk .left).length ≤ v.length+n*D at hleft
  change (q.stk .right).length ≤ query.length+n*D at hright
  have hclean : (q.stk .left).length+(q.stk .right).length ≤ v.length+query.length+2*((v.length+query.length+2)*D) := by omega
  let d := (q.stk .left).length+(q.stk .right).length+2
  have hdr := clear_run (q.stk .left) (q.stk .right) tail witness query b result
  refine ⟨1+a+1+(2*query.length+2)+c+1+d,?_,?_⟩
  · change 1+a+1+(2*query.length+2)+c+1+d ≤ 8*(v.length+query.length+2)+2*((v.length+query.length+2)*D)
    dsimp [d]; omega
  · have htotal : 1+a+1+(2*query.length+2)+c+1+d = 1+(a+(1+((2*query.length+2)+(c+(1+d))))) := by omega
    rw [htotal,runSteps_add]
    change (machine.step (cfg .start bit matched flag (BitstringEncoding.delimit v ++ tail) (b::witness) query [] [] [])).bind _ = _
    rw [start_delimit]
    change runSteps machine.step (a+(1+((2*query.length+2)+(c+(1+d))))) (pemb b false otherP sourceStart) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+((2*query.length+2)+(c+(1+d)))) (pemb b false otherP sourceEnd) = _
    rw [runSteps_add]
    change (machine.step (pemb b false otherP sourceEnd)).bind _ = _
    rw [parse_done]
    change runSteps machine.step ((2*query.length+2)+(c+(1+d))) (cfg .copy b false none tail witness query [] v []) = _
    rw [runSteps_add,copy_run]
    change runSteps machine.step (c+(1+d)) (cemb b false otherC cmpStart) = _
    rw [runSteps_add,hcr]
    change runSteps machine.step (1+d) (cemb b false otherC q) = _
    rw [runSteps_add]
    change (machine.step (cemb b false otherC q)).bind _ = _
    rw [compare_done q b result tail witness query hresult]
    exact hdr


/-- First-match lookup on raw framed names. A malformed block encountered
before a match returns false; later blocks are not inspected after a match. -/
def lookupRaw (raw : List Bool) : List Bool → List Bool → Bool
  | [], _ => false
  | b::witness, query =>
    match BitstringEncoding.undelimit raw with
    | none => false
    | some (v,tail) =>
      if Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v) then b
      else lookupRaw tail witness query

theorem lookupRaw_frames (vars : List (List Bool)) (witness query : List Bool) :
    lookupRaw (frames vars) witness query = Shared.ComplexityBridge.RawCNFLookup.lookup vars witness query := by
  induction vars generalizing witness with
  | nil => cases witness <;> rfl
  | cons v vs ih =>
    cases witness with
    | nil => rfl
    | cons b witness => simp [lookupRaw,frames_cons,BitstringEncoding.undelimit_delimit,Shared.ComplexityBridge.RawCNFLookup.lookup,ih]

def rejectedCfg (bit : Bool) (witness query scratch : List Bool) : machine.Cfg :=
  ⟨some (.inl .no),(bit,false,.inl none),stackVals [] witness query scratch [] []⟩

theorem parse_rejected (bit : Bool) (witness query scratch : List Bool) :
    machine.step (pemb bit false (stackVals [] witness query [] [] [])
      (Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch [])) =
        some (rejectedCfg bit witness query scratch) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

/-- An incomplete delimiter also terminates the finite lookup, with false. -/
theorem invalid_iteration (raw : List Bool) (hne : raw ≠ [])
    (hbad : BitstringEncoding.undelimit raw = none)
    (b bit matched : Bool) (flag : Option Bool) (witness query : List Bool) :
    ∃ t ≤ raw.length+3, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start bit matched flag raw (b::witness) query [] [] []) = some q ∧
      q.l = some (.inl .no) := by
  obtain ⟨n,hn,scratch,hr⟩ := Shared.ComplexityBridge.TM2Undelimit.invalid_run raw [] [] none hbad
  rw [← Shared.ComplexityBridge.TM2Undelimit.initial_eq] at hr
  let other := stackVals [] witness query [] [] []
  let finish := Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []
  change runSteps Parse.step n (Turing.initList Parse raw) = some finish at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Parse.step machine.step (pemb b false other) pTerminal pStable (pStep b false other)
    n (Turing.initList Parse raw) finish (Or.inr rfl) hr
  refine ⟨1+a+1,by omega,rejectedCfg b witness query scratch,?_,rfl⟩
  cases raw with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    rw [show 1+a+1 = 1+(a+1) by omega,runSteps_add]
    change (machine.step (cfg .start bit matched flag (x::xs) (b::witness) query [] [] [])).bind _ = _
    rw [start_cons]
    change runSteps machine.step (a+1) (pemb b false other (Turing.initList Parse (x::xs))) = _
    rw [runSteps_add,har]
    exact parse_rejected b witness query scratch


/-- The loaded machine terminates for all raw frames, including malformed
input. The bound is uniform in the complete raw frame and query lengths. -/
theorem lookupRaw_progress_bounded (witness raw query : List Bool)
    (bit matched : Bool) (flag : Option Bool) (B : Nat) (hB : raw.length+query.length ≤ B) :
    ∃ t ≤ (raw.length+1)*iterationBound B, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start bit matched flag raw witness query [] [] []) = some q ∧
      q.l = some (.inl (if lookupRaw raw witness query then .yes else .no)) := by
  induction witness generalizing raw bit matched flag with
  | nil =>
    refine ⟨1,?_,cfg .no false false none raw [] query [] [] [],?_,?_⟩
    · have hp := iterationBound_pos B
      have hm : iterationBound B ≤ (raw.length+1)*iterationBound B := by
        calc
          iterationBound B = 1*iterationBound B := by simp
          _ ≤ (raw.length+1)*iterationBound B := Nat.mul_le_mul_right _ (by omega)
      exact le_trans hp hm
    · exact start_empty_witness raw query bit matched flag
    · rfl
  | cons b witness ih =>
    cases hr : raw with
    | nil =>
      refine ⟨1,?_,cfg .no b false none [] witness query [] [] [],?_,?_⟩
      · simpa using iterationBound_pos B
      · exact start_empty_vars b bit matched flag witness query
      · rfl
    | cons x xs =>
      have hB' : (x::xs).length+query.length ≤ B := by simpa [hr] using hB
      cases hparse : BitstringEncoding.undelimit (x::xs) with
      | none =>
        obtain ⟨t,ht,q,hq,hlabel⟩ := invalid_iteration (x::xs) (by simp) hparse b bit matched flag witness query
        refine ⟨t,?_,q,hq,?_⟩
        · have hk : (x::xs).length+3 ≤ iterationBound B := by
            unfold iterationBound
            simp only [List.length_cons] at *
            omega
          have hm : iterationBound B ≤ ((x::xs).length+1)*iterationBound B := by
            calc
              iterationBound B = 1*iterationBound B := by simp
              _ ≤ ((x::xs).length+1)*iterationBound B := Nat.mul_le_mul_right _ (by omega)
          exact le_trans ht (le_trans hk hm)
        · simpa [lookupRaw,hparse] using hlabel
      | some p =>
        rcases p with ⟨v,tail⟩
        have hraw := Shared.ComplexityBridge.CNFWitness.undelimit_sound (x::xs) v tail hparse
        have hlen : (x::xs).length = 2*v.length+1+tail.length := by
          rw [← hraw,List.length_append,BitstringEncoding.length_delimit]
        have hvB : v.length+query.length ≤ B := by omega
        have htailB : tail.length+query.length ≤ B := by omega
        obtain ⟨t,ht,htRun⟩ := iteration_raw v tail b bit matched flag witness query
        have htB : t ≤ iterationBound B := le_trans ht (iterationBound_mono hvB)
        cases he : Shared.ComplexityBridge.TM2NumeralPairCompare.answer (query,v) with
        | true =>
          refine ⟨t,?_,cfg (if b then .yes else .no) b true none tail witness query [] [] [],?_,?_⟩
          · have hm : iterationBound B ≤ ((x::xs).length+1)*iterationBound B := by
              calc
                iterationBound B = 1*iterationBound B := by simp
                _ ≤ ((x::xs).length+1)*iterationBound B := Nat.mul_le_mul_right _ (by omega)
            exact le_trans htB hm
          · simpa [he,hraw] using htRun
          · cases b <;> simp [lookupRaw,hparse,he,cfg]
        | false =>
          obtain ⟨u,hu,q,huRun,huLabel⟩ := ih tail b false none htailB
          refine ⟨t+u,?_,q,?_,?_⟩
          · have hm : (tail.length+2)*iterationBound B ≤ ((x::xs).length+1)*iterationBound B :=
              Nat.mul_le_mul_right _ (by omega)
            have heq : (tail.length+2)*iterationBound B = (tail.length+1)*iterationBound B + iterationBound B := by
              calc
                (tail.length+2)*iterationBound B = ((tail.length+1)+1)*iterationBound B := by simp [Nat.add_assoc]
                _ = (tail.length+1)*iterationBound B + iterationBound B := by simp [Nat.add_mul]
            rw [heq] at hm
            omega
          · rw [runSteps_add,← hraw,htRun]
            simpa [he] using huRun
          · simpa [lookupRaw,hparse,he] using huLabel

theorem lookupRaw_progress (raw witness query : List Bool) (bit matched : Bool) (flag : Option Bool) :
    ∃ t ≤ (raw.length+query.length+1)*iterationBound (raw.length+query.length), ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start bit matched flag raw witness query [] [] []) = some q ∧
      q.l = some (.inl (if lookupRaw raw witness query then .yes else .no)) := by
  obtain ⟨t,ht,q,hr,hq⟩ := lookupRaw_progress_bounded witness raw query bit matched flag _ (Nat.le_refl _)
  refine ⟨t,?_,q,hr,hq⟩
  have hm := Nat.mul_le_mul_right (iterationBound (raw.length+query.length))
    (show raw.length+1 ≤ raw.length+query.length+1 by omega)
  omega

end Shared.ComplexityBridge.TM2WitnessLookup
