import PASoundness.M236SecondField

/-! Silent post-emission transfers in the checked occurrence graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

structure FieldTransferRows (k : Nat) (dst : Fin 9) (op : String) : Prop where
  distinct : dst ≠ 6
  decA : sourceRows[k]? = some ("3.k.a.decnz", k+1, some (k+3))
  incDst : sourceRows[k+1]? = some (op, k+2, none)
  jumpBack : sourceRows[k+2]? = some ("jump", k, none)
  incOp : incRegister op = some dst
  noDec : decRegister op = none
  silent : outputForOp op = []

theorem field_transfer_rows_top : FieldTransferRows 49 4 "3.k.top.inc" := by
  constructor <;> decide
theorem field_transfer_rows_b : FieldTransferRows 76 7 "3.k.b.inc" := by
  constructor <;> decide

def bankFieldTransfer (base : RegisterMachine.Bank 9) (dst : Fin 9)
    (a value : Nat) : RegisterMachine.Bank 9 :=
  fun i => if i = 6 then a else if i = dst then value else base i

def cfgFieldTransfer (index : Nat) (base : RegisterMachine.Bank 9) (dst : Fin 9)
    (a value : Nat) (reserve : List Nat) : GraphState :=
  ⟨index, bankFieldTransfer base dst a value, reserve⟩

theorem field_transfer_dec (k : Nat) (dst : Fin 9) (op : String)
    (rows : FieldTransferRows k dst op) (base : RegisterMachine.Bank 9)
    (n value : Nat) (reserve : List Nat) :
    graphSystem.step (cfgFieldTransfer k base dst (n+1) value reserve) =
      (cfgFieldTransfer (k+1) base dst n value (reserve ++ [0]), []) := by
  simp [graphSystem, graphNext, cfgFieldTransfer, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankFieldTransfer, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> fin_cases dst <;> simp_all [bankFieldTransfer, RegisterMachine.write])

theorem field_transfer_zero (k : Nat) (dst : Fin 9) (op : String)
    (rows : FieldTransferRows k dst op) (base : RegisterMachine.Bank 9)
    (value : Nat) (reserve : List Nat) :
    graphSystem.step (cfgFieldTransfer k base dst 0 value reserve) =
      (cfgFieldTransfer (k+3) base dst 0 value reserve, []) := by
  simp [graphSystem, graphNext, cfgFieldTransfer, rows.decA, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp, bankFieldTransfer, RegisterMachine.execute, RegisterMachine.write]

theorem field_transfer_inc (k : Nat) (dst : Fin 9) (op : String)
    (rows : FieldTransferRows k dst op) (base : RegisterMachine.Bank 9)
    (a value : Nat) (reserve : List Nat) :
    graphSystem.step (cfgFieldTransfer (k+1) base dst a value reserve) =
      (cfgFieldTransfer (k+2) base dst a (value+1) reserve, []) := by
  have hdist : dst ≠ 6 := rows.distinct
  simp [graphSystem, graphNext, cfgFieldTransfer, rows.incDst, nextIndex, nextBank, nextReserve,
    rows.incOp, rows.noDec, rows.silent, bankFieldTransfer, RegisterMachine.execute, RegisterMachine.write]
  all_goals (funext i; fin_cases i <;> fin_cases dst <;> simp_all [bankFieldTransfer, RegisterMachine.write])

theorem field_transfer_jump (k : Nat) (dst : Fin 9) (op : String)
    (rows : FieldTransferRows k dst op) (base : RegisterMachine.Bank 9)
    (a value : Nat) (reserve : List Nat) :
    graphSystem.step (cfgFieldTransfer (k+2) base dst a value reserve) =
      (cfgFieldTransfer k base dst a value reserve, []) := by
  simp [graphSystem, graphNext, cfgFieldTransfer, rows.jumpBack, nextIndex, nextBank, nextReserve,
    incRegister, decRegister, outputForOp]

theorem field_transfer_cycle (k : Nat) (dst : Fin 9) (op : String)
    (rows : FieldTransferRows k dst op) (base : RegisterMachine.Bank 9)
    (n value : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgFieldTransfer k base dst (n+1) value reserve) 3
      (cfgFieldTransfer k base dst n (value+1) (reserve ++ [0])) [] := by
  have h1 := WordEventSystem.Block.single graphSystem (field_transfer_dec k dst op rows base n value reserve)
  have h2 := WordEventSystem.Block.single graphSystem (field_transfer_inc k dst op rows base n value (reserve ++ [0]))
  have h3 := WordEventSystem.Block.single graphSystem (field_transfer_jump k dst op rows base n (value+1) (reserve ++ [0]))
  simpa using (h1.trans graphSystem h2).trans graphSystem h3

theorem field_transfer_all (n k : Nat) (dst : Fin 9) (op : String)
    (rows : FieldTransferRows k dst op) (base : RegisterMachine.Bank 9)
    (value : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgFieldTransfer k base dst n value reserve) (3*n)
      (cfgFieldTransfer k base dst 0 (value+n) (reserve ++ List.replicate n 0)) [] := by
  induction n generalizing value reserve with
  | zero => simpa using WordEventSystem.Block.refl graphSystem (cfgFieldTransfer k base dst 0 value reserve)
  | succ n ih =>
    have h := (field_transfer_cycle k dst op rows base n value reserve).trans graphSystem
      (ih (value+1) (reserve ++ [0]))
    simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
      List.replicate_succ, List.append_assoc] using h

/-- Transfer `a` into a distinct destination, preserving all other registers. -/
theorem field_transfer (n k : Nat) (dst : Fin 9) (op : String)
    (rows : FieldTransferRows k dst op) (base : RegisterMachine.Bank 9)
    (value : Nat) (reserve : List Nat) :
    graphSystem.Block (cfgFieldTransfer k base dst n value reserve) (3*n+1)
      (cfgFieldTransfer (k+3) base dst 0 (value+n) (reserve ++ List.replicate n 0)) [] := by
  have h1 := field_transfer_all n k dst op rows base value reserve
  have h2 := WordEventSystem.Block.single graphSystem
    (field_transfer_zero k dst op rows base (value+n) (reserve ++ List.replicate n 0))
  simpa using h1.trans graphSystem h2

/-- The emitter exit has exactly the bank required by a transfer whose
destination is distinct from `a`. -/
theorem emit_exit_to_field_transfer (k : Nat) (base : RegisterMachine.Bank 9)
    (dst : Fin 9) (n : Nat) (reserve : List Nat) (hd : dst ≠ 6) :
    cfgAS k base n 0 reserve =
      cfgFieldTransfer k (bankAS base n 0) dst n (bankAS base n 0 dst) reserve := by
  unfold cfgAS cfgFieldTransfer
  congr 1
  funext i
  fin_cases i <;> fin_cases dst <;> simp_all [bankAS, bankFieldTransfer]

/-- Emit one unary field and silently move the restored value into the
destination register. The row hypotheses hold at 41/49 and 68/76. -/
theorem emit_then_field_transfer (n k : Nat) (dst : Fin 9) (op : String)
    (er : EmitRows k) (tr : FieldTransferRows (k+8) dst op)
    (base : RegisterMachine.Bank 9) (reserve : List Nat) :
    graphSystem.Block (cfgAS k base n 0 reserve) ((7*n+3) + (3*n+1))
      (cfgFieldTransfer ((k+8)+3) (bankAS base n 0) dst 0 (bankAS base n 0 dst+n)
        (((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate n 0))
      (PASoundness.UnaryCodec.unary n) := by
  have he := generic_emit_preserving_a k er n base reserve
  rw [emit_exit_to_field_transfer (k+8) base dst n _ tr.distinct] at he
  have ht := field_transfer n (k+8) dst op tr (bankAS base n 0) (bankAS base n 0 dst)
    ((reserve ++ List.replicate n 0) ++ List.replicate n 0)
  simpa [unary_as_replicate] using he.trans graphSystem ht

/-- Lift the composition to the selected physical execution at an explicitly
reachable prepared graph boundary. -/
theorem selected_emit_then_field_transfer (i n k : Nat) (dst : Fin 9) (op : String)
    (er : EmitRows k) (tr : FieldTransferRows (k+8) dst op)
    (base : RegisterMachine.Bank 9) (reserve : List Nat)
    (h : graphSystem.run i = cfgAS k base n 0 reserve) :
    ∃ finish : Snapshot,
      Good finish ∧
      finish.graphState =
        cfgFieldTransfer ((k+8)+3) (bankAS base n 0) dst 0 (bankAS base n 0 dst+n)
          (((reserve ++ List.replicate n 0) ++ List.replicate n 0) ++ List.replicate n 0) ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + ((7*n+3) + (3*n+1)))) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + ((7*n+3) + (3*n+1)))) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          PASoundness.UnaryCodec.unary n ∧
      graphRefinement.boundary i < graphRefinement.boundary (i + ((7*n+3) + (3*n+1))) := by
  have block := emit_then_field_transfer n k dst op er tr base reserve
  have hr := block.endpoint
  have hp := block.output
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related (i + ((7*n+3) + (3*n+1)))
  refine ⟨finish, hg, ?_, hconfig, ?_, ?_⟩
  · rw [WordEventSystem.run_add, h, hr] at hs
    exact hs
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, WordEventSystem.prefix_add, h, hp]
  · apply graphRefinement.boundary_strict
    omega

def secondDecodedBank (base : RegisterMachine.Bank 9) (rank : Nat) : RegisterMachine.Bank 9 :=
  bankAC (bankRest (secondFieldBase base rank) (Cantor.unpair (base 2)).2)
    (Cantor.unpair (base 2)).1 0

def secondFieldOutputReserve (base : RegisterMachine.Bank 9) (rank : Nat)
    (reserve : List Nat) (padding : Nat) : List Nat :=
  (secondFieldReserve reserve rank padding ++ List.replicate (Cantor.unpair (base 2)).1 0) ++
    List.replicate (Cantor.unpair (base 2)).1 0

/-- From a prepared rank entry, emit both fields and transfer the second
value to `top`; the next graph entry is 52. -/
theorem rank_second_field_then_top (rank : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0) :
    ∃ duration padding, base 2 + 1 ≤ duration ∧
      graphSystem.Block (cfgAS 19 base rank 0 reserve)
        (((((7*rank+3) + (3*rank+1)) + duration) +
          (7*(Cantor.unpair (base 2)).1+3)) + (3*(Cantor.unpair (base 2)).1+1))
        (cfgFieldTransfer 52 (bankAS (secondDecodedBank base rank) (Cantor.unpair (base 2)).1 0)
          4 0 ((bankAS (secondDecodedBank base rank) (Cantor.unpair (base 2)).1 0) 4 +
            (Cantor.unpair (base 2)).1)
          (secondFieldOutputReserve base rank reserve padding ++
            List.replicate (Cantor.unpair (base 2)).1 0))
        (PASoundness.UnaryCodec.unary rank ++
          PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) := by
  obtain ⟨duration, padding, ht, hfields⟩ := rank_then_second_field rank base reserve hc
  change graphSystem.Block (cfgAS 19 base rank 0 reserve) _
    (cfgAS 49 (secondDecodedBank base rank) (Cantor.unpair (base 2)).1 0
      (secondFieldOutputReserve base rank reserve padding)) _ at hfields
  rw [emit_exit_to_field_transfer 49 (secondDecodedBank base rank) 4
    (Cantor.unpair (base 2)).1 _ (by decide)] at hfields
  have htransfer := field_transfer (Cantor.unpair (base 2)).1 49 4 "3.k.top.inc"
    field_transfer_rows_top (bankAS (secondDecodedBank base rank) (Cantor.unpair (base 2)).1 0)
    ((bankAS (secondDecodedBank base rank) (Cantor.unpair (base 2)).1 0) 4)
    (secondFieldOutputReserve base rank reserve padding)
  refine ⟨duration, padding, ht, ?_⟩
  simpa using hfields.trans graphSystem htransfer

def secondTopDuration (rank code duration : Nat) : Nat :=
  (((7*rank+3) + (3*rank+1)) + duration) +
    (7*(Cantor.unpair code).1+3) + (3*(Cantor.unpair code).1+1)

def secondTopState (base : RegisterMachine.Bank 9) (rank : Nat)
    (reserve : List Nat) (padding : Nat) : GraphState :=
  cfgFieldTransfer 52 (bankAS (secondDecodedBank base rank) (Cantor.unpair (base 2)).1 0)
    4 0 ((bankAS (secondDecodedBank base rank) (Cantor.unpair (base 2)).1 0) 4 +
      (Cantor.unpair (base 2)).1)
    (secondFieldOutputReserve base rank reserve padding ++
      List.replicate (Cantor.unpair (base 2)).1 0)

/-- Physical lift of the two fields and `top` transfer at a reached
rank-output boundary; no all-stage reachability is assumed. -/
theorem selected_rank_second_field_then_top (i rank : Nat) (base : RegisterMachine.Bank 9)
    (reserve : List Nat) (hc : base 8 = 0)
    (h : graphSystem.run i = cfgAS 19 base rank 0 reserve) :
    ∃ duration padding finish,
      base 2 + 1 ≤ duration ∧ Good finish ∧
      finish.graphState = secondTopState base rank reserve padding ∧
      mapConfig finish.config = (machineWordSystem machine machineLabels).run
        (graphRefinement.boundary (i + secondTopDuration rank (base 2) duration)) ∧
      (machineWordSystem machine machineLabels).prefixWord
        (graphRefinement.boundary (i + secondTopDuration rank (base 2) duration)) =
        (machineWordSystem machine machineLabels).prefixWord (graphRefinement.boundary i) ++
          (PASoundness.UnaryCodec.unary rank ++
            PASoundness.UnaryCodec.unary (Cantor.unpair (base 2)).1) ∧
      graphRefinement.boundary i <
        graphRefinement.boundary (i + secondTopDuration rank (base 2) duration) := by
  obtain ⟨duration, padding, ht, block⟩ := rank_second_field_then_top rank base reserve hc
  change graphSystem.Block (cfgAS 19 base rank 0 reserve)
    (secondTopDuration rank (base 2) duration) (secondTopState base rank reserve padding) _ at block
  have hr := block.endpoint
  have hp := block.output
  obtain ⟨finish, hg, hs, hconfig⟩ := graphRefinement.related
    (i + secondTopDuration rank (base 2) duration)
  refine ⟨duration, padding, finish, ht, hg, ?_, hconfig, ?_, ?_⟩
  · rw [WordEventSystem.run_add, h, hr] at hs
    exact hs
  · rw [graphRefinement.prefix_eq, graphRefinement.prefix_eq, WordEventSystem.prefix_add, h, hp]
  · apply graphRefinement.boundary_strict
    simp only [secondTopDuration]
    omega

end PASoundness.M236.OccurrenceGraph
