import Shared.PNP.Record285.HalfOdd

/-! Complete native-half operation on the unary value one. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfOne
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (atWord even_bit even_tail suffixBits)
open Shared.PNP.Record285.IncrementReturn (atLeftWord completeBits completeCost completeRight)
open Shared.PNP.Record285.IncrementMeaning (foldRuns)
open Shared.PNP.Record285.DecrementNonzeroScan (scannedLeft scanCost)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.SymbolicDispatch (bits pathLeft pathCost)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.HalfCycle (boundary)
open Shared.PNP.Record285.HalfOdd (continuation)
attribute [local irreducible] Record285.machine

theorem boundary_zero : Record285.machine.table.row boundary false =
    ⟨false,.left,HalfCycle.restore,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem restore_one : Record285.machine.table.row HalfCycle.restore true =
    ⟨false,.right,continuation,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem enter_one (M : Machine 285) (begin initial qboundary qrestore qscan : Fin 285)
    (h1 : M.table.row begin true = ⟨true,.right,initial,false⟩)
    (h2 : M.table.row initial true = ⟨true,.right,qboundary,false⟩)
    (h3 : M.table.row qboundary false = ⟨false,.left,qrestore,false⟩)
    (h4 : M.table.row qrestore true = ⟨false,.right,qscan,false⟩)
    (head : Int) (left tail : Nat) :
    silent M 4 ⟨begin,head,left,true,runPattern true 1 false tail⟩ =
      some (atWord qscan (head+2) (2*(1+2*left)) (runPattern true 0 false tail)) := by
  have hb : (2*(2*left+1)+1).testBit 0 = true := by
    rw [show 2*(2*left+1)+1 = 1+2*(2*left+1) by omega]
    exact odd_bit _
  have hd : (2*(2*left+1)+1)/2 = 2*left+1 := by
    rw [show 2*(2*left+1)+1 = 1+2*(2*left+1) by omega]
    exact odd_tail _
  simp only [silent,PhysicalNumeric.step,h1,h2,h3,Bool.false_eq_true,if_false,
    bitVal,if_true,Nat.add_zero,runPattern_succ_read,runPattern_succ_tail,
    runPattern_zero_read,runPattern_zero_tail,atWord,even_bit,even_tail]
  simp only [hb,hd,h4,Bool.false_eq_true,if_false,Nat.add_zero]
  have hh : head+1+1-1+1 = head+2 := by omega
  have hl : 2*(2*left+1) = 2*(1+2*left) := by omega
  simp only [hh,hl]

theorem empty_shift (M : Machine 285) (qshift qcheck qret : Fin 285)
    (rows : DecrementNonzeroShift.Rows M qshift qcheck qret)
    (head : Int) (left retained : Nat) :
    silent M 2 (atWord qshift head (2*(1+2*left)) (4*retained)) =
      some (atLeftWord qret (head-2) (1+2*left) (2*(4*retained+1))) := by
  rw [show 4*retained = 2*(2*retained) by omega]
  simp only [atWord,atLeftWord,even_bit,even_tail,odd_bit,odd_tail,silent,PhysicalNumeric.step,
    rows.scanZero,rows.checkZero,Bool.false_eq_true,if_false,bitVal,if_true,Nat.add_zero]
  have hh : head-1-1 = head-2 := by omega
  have hr : 2*(2*(2*retained)+1) = 2*(4*retained+1) := by omega
  simp only [hh,hr]

def shiftCost : List Nat → Nat
  | [] => scanCost 0 []+2
  | first::rest => scanCost 0 (first::rest)+2+completeCost (foldRuns rest []) first

/-- The value-one exit shifts the entire following bank and stops at the
shared return scanner. Even an empty listed bank is handled. -/
theorem shift_to_return (fields : List Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (shiftCost fields)
      (atWord DecrementNonzeroScan.scan head (2*(1+2*left))
        (runPattern true 0 false (suffixBits fields retained))) =
      some (atLeftWord DecrementNonzeroShift.returnState (head-2) (1+2*left)
        (2*IncrementSelector.blocksBits fields (4*retained+1))) := by
  cases fields with
  | nil =>
    have hs := DecrementNonzeroScan.scan_suffix Record285.machine DecrementNonzeroScan.scan
      DecrementNonzeroScan.check DecrementNonzeroScan.shift DecrementNonzeroScan.literal_rows
      [] 0 head (2*(1+2*left)) retained
    have he := empty_shift Record285.machine DecrementNonzeroScan.shift
      DecrementNonzeroShift.check DecrementNonzeroShift.returnState DecrementNonzeroShift.literal_rows
      head left retained
    simp only [shiftCost,scannedLeft,pushBit,IncrementSelector.blocksBits,scanCost,
      IncrementShift.cost] at hs ⊢
    rw [silent_add,hs]
    simp only [Option.bind_some]
    have hh : head+((0+1+1:Nat):Int)-2 = head := by omega
    simpa only [hh] using he
  | cons first rest =>
    exact HalfOdd.second_shift first rest head (1+2*left) retained

theorem target_one_to_return (fields : List Nat) (head : Int) (left retained : Nat) :
    silent Record285.machine (4+shiftCost fields)
      ⟨HalfSelector.state 0,head,left,true,runPattern true 1 false (suffixBits fields retained)⟩ =
      some (atLeftWord DecrementNonzeroShift.returnState head (1+2*left)
        (2*IncrementSelector.blocksBits fields (4*retained+1))) := by
  have he := enter_one Record285.machine (HalfSelector.state 0) ⟨68,by decide⟩ boundary
    HalfCycle.restore continuation HalfCycle.half_begin_one HalfCycle.initial_one boundary_zero
    restore_one head left (suffixBits fields retained)
  have hs := shift_to_return fields (head+2) left retained
  have hh : head+2-2 = head := by omega
  rw [hh] at hs
  rw [silent_add,he]
  simp only [Option.bind_some]
  exact hs

/-- The value-one return scanner restores all preceding fields and the
zero quotient, with the additional zero field and high suffix explicit. -/
theorem return_to_break (gap : Nat) (before fields : List Nat)
    (head : Int) (far retained : Nat) :
    let pos := head+1+IncrementSelector.cost (gap::before)
    let steps := 1+completeCost (0::foldRuns before []) gap
    silent Record285.machine steps
      (atLeftWord DecrementNonzeroShift.returnState pos
        (1+2*DecrementSelector.leftAfter (gap::before) (2*far))
        (2*IncrementSelector.blocksBits fields (4*retained+1))) =
      some (atLeftWord IncrementReturn.breakState (head-1) far
        (4*IncrementSelector.blocksBits (gap::(before++[0]++fields++[0])) retained)) := by
  dsimp only
  let pos := head+1+IncrementSelector.cost (gap::before)
  have hl : 1+2*DecrementSelector.leftAfter (gap::before) (2*far) =
      1+2*completeBits (0::foldRuns before []) gap far := by
    rw [DecrementNonzeroReturn.selected_left_exact]
    simp only [completeBits,runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  have ho : completeRight (0::foldRuns before []) gap
      (2*(2*IncrementSelector.blocksBits fields (4*retained+1))+1) =
      4*IncrementSelector.blocksBits (gap::(before++[0]++fields++[0])) retained := by
    rw [IncrementMeaning.scan_output]
    simp only [IncrementMeaning.backFold]
    rw [IncrementMeaning.backFold_foldRuns]
    simp only [IncrementMeaning.backFold,← IncrementMeaning.blocks_cons,← IncrementMeaning.blocks_append]
    have hz : 4*retained+1 = IncrementSelector.blocksBits [0] retained := by
      simp [IncrementSelector.blocksBits,runPattern,bitVal]; omega
    rw [hz,← IncrementMeaning.blocks_append]
    congr 2
    simp [List.append_assoc]
  have hr := IncrementMeaning.scan_leading Record285.machine IncrementShift.returnState
    IncrementReturn.checkState IncrementReturn.breakState IncrementReturn.literal_rows
    (0::foldRuns before []) gap pos far (2*IncrementSelector.blocksBits fields (4*retained+1))
  rw [← hl,ho] at hr
  have hc := DecrementNonzeroReturn.return_cost_exact gap before
  have hh : pos-(1+(completeCost (0::foldRuns before []) gap:Int)) = head-1 := by
    dsimp only [pos,completeCost]
    omega
  rw [hh] at hr
  exact hr

theorem root_one_to_break (code : List Bool) (gap : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length))
    (head : Int) (leftTail retained : Nat) :
    let blocks := gap::before
    let far := bits (pathLeft code) leftTail
    let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks
    let back := 1+completeCost (0::foldRuns before []) gap
    silent Record285.machine (start+(4+shiftCost fields)+back)
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[1]) (suffixBits fields retained)))) =
      some (atLeftWord IncrementReturn.breakState (head-1) far
        (4*IncrementSelector.blocksBits (gap::(before++[0]++fields++[0])) retained)) := by
  dsimp only
  let blocks := gap::before
  let far := bits (pathLeft code) leftTail
  let left := DecrementSelector.leftAfter blocks (2*far)
  let targetHead := head+1+IncrementSelector.cost blocks
  let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost blocks
  let back := 1+completeCost (0::foldRuns before []) gap
  let tail := suffixBits fields retained
  have hd := HalfDispatch.root_dispatch_half code before.length hwalk head leftTail
    (2*runPattern false gap true (2*IncrementSelector.blocksBits (before++[1]) tail))
  have ht := HalfDispatch.terminal_to_target code gap 1 before hwalk head leftTail tail
  have he := target_one_to_return fields targetHead left retained
  have hr := return_to_break gap before fields head far retained
  rw [show start+(4+shiftCost fields)+back =
      code.length+(((2*gap+5)+pathCost code+IncrementSelector.cost blocks)+
        ((4+shiftCost fields)+back)) by dsimp [start]; omega,
    silent_add,hd]
  simp only [Option.bind_some]
  rw [silent_add,ht]
  simp only [Option.bind_some]
  rw [silent_add,he]
  simp only [Option.bind_some]
  exact hr

theorem break_to_root (code : List Bool) (gap i : Nat)
    (hwalk : walk 162 code = some (.half i)) (head : Int) (leftTail bank : Nat) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    silent Record285.machine ((3*p.1+2*gap+9)+(precode.length+17))
      (atLeftWord IncrementReturn.breakState (head-1) (bits (pathLeft code) leftTail)
        (4*runPattern true (gap+1) false bank)) =
      some (SymbolicDispatch.denote
        (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let rightTail := runPattern false (p.1+gap+1) true (2*bank)
  have hzcode := HalfOdd.half_path_zero code i hwalk
  have hz : false ∈ code.reverse := by simpa using hzcode
  have hroot := IncrementCleanup.path_peel_preserves_root code hzcode
  have hroot' : peel (pathLeft code) = (p.1,p.2++rootLeft) := by
    simpa only [rootLeft,List.append_assoc] using hroot
  have hsafe := (producer_half_safe code i hwalk).2.2
  have hprefix := peel_prefix_safe code hsafe hz
  have hleft := IncrementCleanup.path_peel_bits code leftTail
  rw [hroot'] at hleft
  have hcleanup := IncrementCleanup.literal_cleanup p.1 gap head (bits (p.2++rootLeft) leftTail) bank
  rw [← hleft] at hcleanup
  have hpref : pathLeft precode = p.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hword : 1+2*runPattern false (p.1+gap+2) true (2*bank) = 1+4*rightTail := by
    dsimp only [rightTail]
    rw [show p.1+gap+2 = (p.1+gap+1)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false]
    omega
  have hr := literal_return_root precode hprefix (head-p.1-1) leftTail rightTail
  have hpos : (head-p.1-1)-1 = head-p.1-2 := by omega
  rw [hpref,hpos,← hword] at hr
  have hbreak : IncrementReturn.breakState = IncrementCleanup.lexical := rfl
  rw [hbreak,silent_add,hcleanup]
  simp only [Option.bind_some]
  exact hr

/-- Value one is halved to zero and takes the success control path. The
complete suffix is preserved after one new zero field. -/
theorem root_one_returns_root (code : List Bool) (gap : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]++fields++[0]) retained
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
    let back := 1+completeCost (0::foldRuns before []) gap
    let steps := start+(4+shiftCost fields)+back+(3*p.1+2*gap+9)+(precode.length+17)
    silent Record285.machine steps
      (rootEntry code head leftTail
        (2*runPattern false gap true
          (2*IncrementSelector.blocksBits (before++[1]) (suffixBits fields retained)))) =
      some (SymbolicDispatch.denote
        (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1) leftTail rightTail) := by
  dsimp only
  let p := peel code.reverse
  let precode := p.2.reverse
  let bank := IncrementSelector.blocksBits (before++[0]++fields++[0]) retained
  let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
  let back := 1+completeCost (0::foldRuns before []) gap
  have hfirst := root_one_to_break code gap before fields hwalk head leftTail retained
  dsimp only at hfirst
  have hbank : IncrementSelector.blocksBits (gap::(before++[0]++fields++[0])) retained =
      runPattern true (gap+1) false bank := by
    simp only [IncrementSelector.blocksBits,runPattern,bitVal,if_true,bank]
  rw [hbank] at hfirst
  have hrest := break_to_root code gap before.length hwalk head leftTail bank
  rw [show start+(4+shiftCost fields)+back+(3*p.1+2*gap+9)+(precode.length+17) =
      (start+(4+shiftCost fields)+back)+((3*p.1+2*gap+9)+(precode.length+17)) by omega,
    silent_add,hfirst]
  simp only [Option.bind_some]
  exact hrest

theorem bound_root_one_returns_root_physical (code : List Bool) (gap : Nat) (before fields : List Nat)
    (hwalk : walk 162 code = some (.half before.length)) (head : Int) (leftTail retained : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[1]) (suffixBits fields retained)))) physical) :
    let p := peel code.reverse
    let precode := p.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]++fields++[0]) retained
    let rightTail := runPattern false (p.1+gap+1) true (2*bank)
    let start := code.length+(2*gap+5)+pathCost code+IncrementSelector.cost (gap::before)
    let back := 1+completeCost (0::foldRuns before []) gap
    let steps := start+(4+shiftCost fields)+back+(3*p.1+2*gap+9)+(precode.length+17)
    returnPath code = some (precode++[true]) ∧
    Rel (SymbolicDispatch.denote
      (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-1) leftTail rightTail)
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (root_one_returns_root code gap before fields hwalk head leftTail retained)
  have hz : false ∈ code.reverse := by simpa using HalfOdd.half_path_zero code before.length hwalk
  exact ⟨return_after_zero code.reverse hz,hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.HalfOne
