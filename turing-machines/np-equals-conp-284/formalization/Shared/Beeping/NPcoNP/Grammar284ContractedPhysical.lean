import Shared.Beeping.NPcoNP.Grammar284AdministrativeTags
import Shared.Beeping.NPcoNP.Grammar284JumpProgress

/-! Connect the checked graph-contraction chase to its physical administrative
execution, under an explicit initial tape window. -/
namespace Shared.Beeping.NPcoNP.Grammar284ContractedPhysical
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Grammar284ContractCoverage
open Shared.Beeping.NPcoNP.Grammar284JumpProgress
open Shared.Beeping.NPcoNP.Grammar284AdministrativeChain
open Shared.Beeping.NPcoNP.Grammar284AdministrativeTags
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

theorem jump_row_kind (i dst : Nat) (entry : Path × String) (row : Row)
    (hleaf : traceState557.acc.leaves[i]?=some entry)
    (hrow : producerFullRows[i]?=some row) (hop : row.op="jump") (htarget : row.targets=[dst]) :
    AdministrativeJump entry dst := by
  obtain ⟨bound,hget⟩ := Array.getElem?_eq_some_iff.mp hleaf
  have hc := allRows i bound
  simp only [indexedRowCheck,hleaf,hrow,beq_iff_eq] at hc
  have rowEq : row=⟨"jump",[dst]⟩ := by cases row; simp_all
  rw [rowEq] at hc
  have listGet : traceState557.acc.leaves.toList[i]?=some entry := by
    simpa only [Array.getElem?_toList] using hleaf
  obtain ⟨lbound,lhget⟩ := List.getElem?_eq_some_iff.mp listGet
  have member : entry ∈ traceState557.acc.leaves.toList := by
    rw [←lhget]
    exact List.getElem_mem lbound
  exact listed_jump_kind entry member dst hc

theorem trace_start_row {i final n : Nat} (trace : JumpTrace producerFullRows i final n)
    (row : Row) (hfinal : producerFullRows[final]?=some row) :
    ∃ first, producerFullRows[i]?=some first := by
  cases trace with
  | done => exact ⟨row,hfinal⟩
  | jump _ _ _ _ r hr _ _ _ => exact ⟨r,hr⟩

theorem leaf_at_row (i : Nat) (row : Row) (hrow : producerFullRows[i]?=some row) :
    ∃ entry, traceState557.acc.leaves[i]?=some entry := by
  obtain ⟨bound,_⟩ := Array.getElem?_eq_some_iff.mp hrow
  have lb : i<traceState557.acc.leaves.size := by
    rw [producerLeafCount,fullRows_size] at *
    exact bound
  exact ⟨traceState557.acc.leaves[i],Array.getElem?_eq_getElem lb⟩

theorem trace_to_chain {i final n : Nat} (trace : JumpTrace producerFullRows i final n)
    (row : Row) (hfinal : producerFullRows[final]?=some row)
    (entry last : Path × String) (hleaf : traceState557.acc.leaves[i]?=some entry)
    (hlast : traceState557.acc.leaves[final]?=some last) :
    AdministrativeChain n entry last := by
  induction trace generalizing entry with
  | done i =>
    have he : entry=last := Option.some.inj (hleaf.symm.trans hlast)
    subst entry
    exact AdministrativeChain.nil last
  | jump i j k n r hr hj ht tail ih =>
    obtain ⟨rj,hrj⟩ := trace_start_row tail row hfinal
    obtain ⟨middle,hmid⟩ := leaf_at_row j rj hrj
    have hkind := jump_row_kind i j entry r hleaf hr hj ht
    exact AdministrativeChain.cons n entry middle last j hkind hmid (ih hfinal middle hmid hlast)

/-- A successful checked contraction chase executes physically and silently
from a supplied parser window to the contracted row's expanded leaf. -/
theorem contraction_runs (fuel i result : Nat)
    (targetAt : Grammar284.target producerFullRows producerNumbering.map fuel i=some result)
    (entry : Path × String) (hleaf : traceState557.acc.leaves[i]?=some entry)
    (origin separator : Int) (t : Int → Bool)
    (word : Holds t origin entry.1) (left : ∀ q, q<origin → t q=false)
    (gap : ∀ q, origin+((entry.1.length : Nat) : Int)-1<q → q<separator-1 → t q=false)
    (room : origin+55<separator) (right : t (separator-1)=true) (sep : t separator=false) :
    ∃ (final count steps : Nat) (last : Path × String) (out : Int → Bool),
      count<fuel ∧ count≤steps ∧ traceState557.acc.leaves[final]?=some last ∧
      producerNumbering.map[final]?=some (some result) ∧
      Holds out origin last.1 ∧ (∀ q, q<origin → out q=false) ∧
      (∀ q, origin+((last.1.length : Nat) : Int)-1<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ out separator=false ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨final,count,row,hcount,htrace,hfinal,hnot,hmap⟩ := target_sound _ _ _ _ _ targetAt
  obtain ⟨last,hlast⟩ := leaf_at_row final row hfinal
  have hchain := trace_to_chain htrace row hfinal entry last hleaf hlast
  have listGet : traceState557.acc.leaves.toList[i]?=some entry := by
    simpa only [Array.getElem?_toList] using hleaf
  obtain ⟨bound,hget⟩ := List.getElem?_eq_some_iff.mp listGet
  have mem : entry ∈ traceState557.acc.leaves.toList := by
    rw [←hget]
    exact List.getElem_mem bound
  obtain ⟨steps,out,hsteps,_,hout,hleft,hgap,hright,hsep,hbank,hseg⟩ :=
    chain_runs count entry last hchain origin separator t mem word left gap room right sep
  exact ⟨final,count,steps,last,out,hcount,hsteps,hlast,hmap,hout,hleft,hgap,hright,hsep,hbank,hseg⟩

#print axioms contraction_runs
end Shared.Beeping.NPcoNP.Grammar284ContractedPhysical
