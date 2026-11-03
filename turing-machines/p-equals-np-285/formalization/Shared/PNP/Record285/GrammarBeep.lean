import Shared.PNP.Record285.GrammarReturnRoot

/-! A beep leaf with a true marker: exact finite dispatch and marked row. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch

def beepState : Fin 285 := ⟨121,by decide⟩

theorem beep_row : Record285.machine.table.row beepState true =
    ⟨false,.left,⟨1,by decide⟩,true⟩ := by
  rw [ArtifactEndpoint.literal_rows]
  decide

def markedRootEntry (code : List Bool) (head : Int) (leftTail rightTail : Nat) :
    PhysicalNumeric.Config 285 :=
  denote (rightWord treeRoot (-(code.length:Int)) code true rootLeft []) head leftTail rightTail

theorem rightWord_append_bit_marked (q : Fin 285) (head : Int) (pre : List Bool)
    (b : Bool) (left : List Bool) :
    rightWord q head (pre++[b]) true left [] = rightWord q head pre b left [true] := by
  cases pre <;> simp [rightWord,List.append_assoc]

/-- A grammar beep path reaches state 121 on a true marker in exactly the
path length, before taking the marked row. -/
theorem root_beep_symbolic (code : List Bool)
    (hwalk : walk rootIndex code = some .beep) :
    run code.length (rightWord treeRoot (-(code.length:Int)) code true rootLeft []) =
      some ⟨beepState,0,code.reverse++rootLeft,true,[]⟩ := by
  obtain ⟨pre,bit,parent,row,hcode,hroute,_,hexpected,hrow⟩ :=
    root_final_edge code .beep (by simpa only [rootIndex] using hwalk)
  have hr : row = ⟨bit,.right,beepState,false⟩ := by
    simpa only [expected,Option.some.injEq,beepState] using hexpected.symm
  have hnum : NumericTables.target.table.row (state parent) bit =
      ⟨bit,.right,beepState,false⟩ := by
    rw [← ArtifactEndpoint.literal_rows]
    exact hrow.trans hr
  have hs := route_scan pre treeRoot (state parent) hroute (-(code.length:Int)) bit rootLeft [true]
  have hhead : -(code.length:Int)+(pre.length:Int) = -1 := by
    rw [hcode]
    simp only [List.length_append,List.length_singleton,Int.natCast_add,Int.natCast_one]
    omega
  rw [hhead] at hs
  have hlast : SymbolicDispatch.step ⟨state parent,-1,pre.reverse++rootLeft,bit,[true]⟩ =
      some ⟨beepState,0,bit::pre.reverse++rootLeft,true,[]⟩ := by
    simp [SymbolicDispatch.step,hnum]
  rw [hcode,rightWord_append_bit_marked]
  have hlen : (pre++[bit]).length = pre.length+1 := by simp
  rw [hcode,hlen] at hs
  rw [hlen,run_add,hs]
  simp only [Option.bind_some,run,hlast,List.reverse_append,List.reverse_singleton,
    List.singleton_append]

end Shared.PNP.Record285.Grammar
