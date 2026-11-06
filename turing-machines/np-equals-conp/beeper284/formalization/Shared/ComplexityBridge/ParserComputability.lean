import Shared.ComplexityBridge.CNFConditional

/-! Primitive-recursive computability of the pinned Google bitstring decoder
for the CNF front end, and the resulting computability of the raw-input SAT
and UNSAT reference functions. These are recursion-theoretic results; no
running-time bound, TM2 simulation, or finite-machine implementation follows.
The executable parser remains the pinned Google definition. -/
namespace Shared.ComplexityBridge.ParserComputability
abbrev Block := Option (List Bool × List Bool)
abbrev State := List Bool × Block × Block

def blockStep (b : Bool) (s : State) : State :=
  (b :: s.1,
   (if b then s.2.2 else some ([], s.1)),
   s.2.1.map (fun p => (b :: p.1, p.2)))

def blockScan (xs : List Bool) : State := xs.foldr blockStep ([], none, none)

theorem blockScan_correct (xs : List Bool) :
    blockScan xs = (xs, BitstringEncoding.undelimit xs,
      BitstringEncoding.undelimit (true :: xs)) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change blockStep b (blockScan xs) = _
    rw [ih]
    cases b <;> simp [blockStep, BitstringEncoding.undelimit]


theorem blockStep_primrec : Primrec₂ blockStep := by
  have hlist : Primrec (fun p : Bool × State => p.1 :: p.2.1) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hchoice : Primrec (fun p : Bool × State =>
      if p.1 then p.2.2.2 else some ([], p.2.1)) := by
    have hc : Primrec (fun p : Bool × State => p.1) := Primrec.fst
    have ht : Primrec (fun p : Bool × State => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have he : Primrec (fun p : Bool × State => some (([] : List Bool), p.2.1)) :=
      Primrec.option_some.comp (Primrec.pair (Primrec.const ([] : List Bool)) (Primrec.fst.comp Primrec.snd))
    refine (Primrec.cond hc ht he).of_eq ?_
    intro p
    rcases p with ⟨b, s⟩
    cases b <;> rfl
  have hmap : Primrec (fun p : Bool × State =>
      p.2.2.1.map (fun q => (p.1 :: q.1, q.2))) := by
    apply Primrec.option_map (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    exact (Primrec.pair
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.pair hlist (Primrec.pair hchoice hmap)).to₂

theorem blockScan_primrec : Primrec blockScan := by
  unfold blockScan
  exact Primrec.list_foldr Primrec.id (Primrec.const (([], none, none) : State))
    (blockStep_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem undelimit_primrec : Primrec BitstringEncoding.undelimit := by
  apply ((Primrec.fst.comp Primrec.snd).comp blockScan_primrec).of_eq
  intro xs
  rw [blockScan_correct]

theorem undelimit_computable : Computable BitstringEncoding.undelimit := undelimit_primrec.to_comp


abbrev Blocks := Option (List (List Bool))
abbrev BlockInput := Nat × List Bool

def nextBlockInput (p : BlockInput) : BlockInput :=
  (p.1 - 1, ((BitstringEncoding.undelimit p.2).map Prod.snd).getD [])

def blockChildren (p : BlockInput) : List BlockInput :=
  if p.1 = 0 then [] else [nextBlockInput p]

def blockCombine (p : BlockInput) (rs : List Blocks) : Option Blocks :=
  if p.2.isEmpty then some (some [])
  else if p.1 = 0 then some none
  else match BitstringEncoding.undelimit p.2 with
    | none => some none
    | some q => rs.head?.map fun r => r.map (q.1 :: ·)

def blocksAux (p : BlockInput) : Blocks := BitstringEncoding.undelimitBlocksAux p.1 p.2

theorem blockChildren_decrease (p : BlockInput) (q : BlockInput)
    (h : q ∈ blockChildren p) : q.1 < p.1 := by
  rcases p with ⟨fuel, input⟩
  cases fuel with
  | zero => simp [blockChildren] at h
  | succ n =>
    simp [blockChildren, nextBlockInput] at h
    subst q
    simp

theorem blockCombine_correct (p : BlockInput) :
    blockCombine p ((blockChildren p).map blocksAux) = some (blocksAux p) := by
  rcases p with ⟨fuel, input⟩
  cases input with
  | nil => simp [blockCombine, blocksAux, BitstringEncoding.undelimitBlocksAux]
  | cons b bs =>
    cases fuel with
    | zero => simp [blockCombine, blocksAux, BitstringEncoding.undelimitBlocksAux]
    | succ n =>
      cases h : BitstringEncoding.undelimit (b :: bs) with
      | none => simp [blockCombine, blocksAux, BitstringEncoding.undelimitBlocksAux, h]
      | some q =>
        rcases q with ⟨payload, rest⟩
        simp [blockCombine, blockChildren, nextBlockInput, blocksAux,
          BitstringEncoding.undelimitBlocksAux, h]


theorem nextBlockInput_primrec : Primrec nextBlockInput := by
  have hr : Primrec (fun p : BlockInput =>
      ((BitstringEncoding.undelimit p.2).map Prod.snd).getD []) := by
    apply Primrec.option_getD.comp _ (Primrec.const [])
    exact Primrec.option_map (undelimit_primrec.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd).to₂
  exact Primrec.pair (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)) hr

theorem blockChildren_primrec : Primrec blockChildren := by
  unfold blockChildren
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const [])
    (Primrec.list_cons.comp nextBlockInput_primrec (Primrec.const []))

set_option maxHeartbeats 2000000 in
theorem blockCombine_primrec : Primrec₂ blockCombine := by
  let Input := BlockInput × List Blocks
  have hempty : Primrec (fun p : Input => p.1.2.isEmpty) := by
    have hl : Primrec (fun p : Input => p.1.2) := Primrec.snd.comp Primrec.fst
    have hh : Primrec₂ (fun (_ : Input) (_ : Bool × List Bool) => false) := Primrec₂.const false
    have h := Primrec.list_casesOn hl (Primrec.const true) hh
    apply h.of_eq
    intro p
    cases p.1.2 <;> rfl
  have hhead : Primrec (fun p : Input × (List Bool × List Bool) => p.1.2.head?) :=
    Primrec.list_head?.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec (fun p : (Input × (List Bool × List Bool)) × Blocks =>
      p.2.map (fun xs => p.1.2.1 :: xs)) := by
    apply Primrec.option_map Primrec.snd
    let X := (Input × (List Bool × List Bool)) × Blocks
    have hv : Primrec (fun p : X × List (List Bool) => p.1.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have hs : Primrec (fun p : X × List (List Bool) => p.2) := Primrec.snd
    exact (Primrec.list_cons.comp hv hs).to₂
  have hsome : Primrec₂ (fun p : Input => fun q : List Bool × List Bool =>
      p.2.head?.map (fun r => r.map (q.1 :: ·))) :=
    (Primrec.option_map hhead hinner.to₂).to₂
  have hparsed : Primrec (fun p : Input =>
      match BitstringEncoding.undelimit p.1.2 with
      | none => (some none : Option Blocks)
      | some q => (p.2.head?.map (fun (r : Blocks) => r.map (q.1 :: ·)) : Option Blocks)) := by
    refine (Primrec.option_casesOn (undelimit_primrec.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.const (some none : Option Blocks)) hsome).of_eq ?_
    intro p
    cases BitstringEncoding.undelimit p.1.2 <;> rfl
  have hzero := Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0))
    (Primrec.const (some none : Option Blocks)) hparsed
  have hf := Primrec.cond hempty (Primrec.const (some (some []) : Option Blocks)) hzero
  apply hf.to₂.of_eq
  intro p rs
  cases p with
  | mk fuel input => cases input <;> simp [blockCombine]

theorem blocksAux_primrec : Primrec blocksAux := by
  exact Primrec.nat_omega_rec' blocksAux (m := Prod.fst) (l := blockChildren)
    (g := blockCombine) Primrec.fst blockChildren_primrec blockCombine_primrec
    blockChildren_decrease blockCombine_correct

theorem undelimitBlocks_primrec : Primrec BitstringEncoding.undelimitBlocks := by
  unfold BitstringEncoding.undelimitBlocks
  exact blocksAux_primrec.comp (Primrec.pair Primrec.list_length Primrec.id)

theorem undelimitBlocks_computable : Computable BitstringEncoding.undelimitBlocks :=
  undelimitBlocks_primrec.to_comp


theorem list_mapM_primrec {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → Option β} (hf : Primrec f) : Primrec (List.mapM f) := by
  have hstep : Primrec (fun p : α × Option (List β) =>
      (f p.1).bind (fun b => p.2.map (b :: ·))) := by
    apply Primrec.option_bind (hf.comp Primrec.fst)
    apply Primrec.option_map (Primrec.snd.comp Primrec.fst)
    exact (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hfold := Primrec.list_foldr (Primrec.id : Primrec (id : List α → List α))
    (Primrec.const (some [] : Option (List β))) (hstep.comp Primrec.snd).to₂
  apply hfold.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [id_eq, List.foldr_cons, List.mapM_cons] at *
    rw [ih]
    cases f a <;> cases xs.mapM f <;> rfl


theorem bitDecode_list_primrec {α : Type} [Primcodable α] [BitstringEncoding α]
    (hf : Primrec (@BitstringEncoding.bitDecode α _)) :
    Primrec (@BitstringEncoding.bitDecode (List α) _) := by
  have hb := Primrec.option_bind undelimitBlocks_primrec
    ((list_mapM_primrec hf).comp Primrec.snd).to₂
  apply hb.of_eq
  intro xs
  rfl

theorem bitDecode_bool_primrec : Primrec (@BitstringEncoding.bitDecode Bool _) := by
  have h : Primrec (fun xs : List Bool => if xs.length = 1 then xs.head? else none) :=
    Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1)) Primrec.list_head?
      (Primrec.const none)
  apply h.of_eq
  intro xs
  cases xs with
  | nil => rfl
  | cons b xs => cases xs <;> rfl


theorem bitDecode_pair_primrec {α β : Type} [Primcodable α] [Primcodable β]
    [BitstringEncoding α] [BitstringEncoding β]
    (ha : Primrec (@BitstringEncoding.bitDecode α _))
    (hb : Primrec (@BitstringEncoding.bitDecode β _)) :
    Primrec (@BitstringEncoding.bitDecode (α × β) _) := by
  have hpair : Primrec (fun p : List Bool × List Bool =>
      (BitstringEncoding.bitDecode p.1 : Option α).bind fun a =>
        (BitstringEncoding.bitDecode p.2 : Option β).map (a, ·)) := by
    apply Primrec.option_bind (ha.comp Primrec.fst)
    apply Primrec.option_map (hb.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hf := Primrec.option_bind undelimit_primrec (hpair.comp Primrec.snd).to₂
  apply hf.of_eq
  intro xs
  change _ = (match BitstringEncoding.undelimit xs with
    | none => none
    | some (a, b) =>
      match (BitstringEncoding.bitDecode a : Option α), (BitstringEncoding.bitDecode b : Option β) with
      | some x, some y => some (x, y)
      | _, _ => none)
  cases h : BitstringEncoding.undelimit xs with
  | none => rfl
  | some p =>
    rcases p with ⟨a, b⟩
    simp only [Option.bind_some]
    cases BitstringEncoding.bitDecode a (α := α) <;>
      cases BitstringEncoding.bitDecode b (α := β) <;> rfl


def positiveStep (b : Bool) (p : Nat × Bool) : Nat × Bool :=
  (if b then (if p.2 then 1 else p.1 + p.1 + 1) else p.1 + p.1, false)

def positiveFold (xs : List Bool) : Nat × Bool := xs.foldr positiveStep (1, true)

theorem positiveFold_correct (xs : List Bool) :
    positiveFold xs = ((Computability.decodePosNum xs : Nat), xs.isEmpty) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change positiveStep b (positiveFold xs) = _
    rw [ih]
    cases b <;> cases xs <;> simp [positiveStep, Computability.decodePosNum,
      PosNum.cast_bit0, PosNum.cast_bit1]

theorem positiveStep_primrec : Primrec₂ positiveStep := by
  have hsum : Primrec (fun p : Bool × (Nat × Bool) => p.2.1 + p.2.1) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  have htrue : Primrec (fun p : Bool × (Nat × Bool) =>
      bif p.2.2 then 1 else p.2.1 + p.2.1 + 1) :=
    Primrec.cond (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
      (Primrec.succ.comp hsum)
  have hv := Primrec.cond Primrec.fst htrue hsum
  apply (Primrec.pair hv (Primrec.const false)).to₂.of_eq
  intro b p
  rcases p with ⟨n, e⟩
  cases b <;> cases e <;> rfl

theorem positiveFold_primrec : Primrec positiveFold := by
  unfold positiveFold
  exact Primrec.list_foldr Primrec.id (Primrec.const ((1, true) : Nat × Bool))
    (positiveStep_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem decodeNat_primrec : Primrec Computability.decodeNat := by
  have he : Primrec (fun xs : List Bool => xs.isEmpty) := by
    have h := Primrec.list_casesOn (Primrec.id : Primrec (id : List Bool → List Bool))
      (Primrec.const true) (Primrec₂.const false : Primrec₂ (fun (_ : List Bool) (_ : Bool × List Bool) => false))
    apply h.of_eq
    intro xs
    cases xs <;> rfl
  have h := Primrec.cond he (Primrec.const 0) (Primrec.fst.comp positiveFold_primrec)
  apply h.of_eq
  intro xs
  rw [positiveFold_correct]
  cases xs with
  | nil => rfl
  | cons b xs => simp [Computability.decodeNat, Computability.decodeNum]

theorem bitDecode_nat_primrec : Primrec (@BitstringEncoding.bitDecode Nat _) := by
  exact Primrec.option_some.comp decodeNat_primrec


theorem parse_primrec : Primrec Shared.ComplexityBridge.CNF.parse := by
  exact bitDecode_list_primrec (bitDecode_list_primrec
    (bitDecode_pair_primrec bitDecode_nat_primrec bitDecode_bool_primrec))

theorem parse_computable : Computable Shared.ComplexityBridge.CNF.parse := parse_primrec.to_comp

theorem sat_computable : Computable Shared.ComplexityBridge.CNF.sat :=
  Shared.ComplexityBridge.CNF.sat_computable_of_parse parse_computable

theorem validUnsat_computable : Computable Shared.ComplexityBridge.CNF.validUnsat :=
  Shared.ComplexityBridge.CNF.validUnsat_computable_of_parse parse_computable

theorem complementSat_computable : Computable Shared.ComplexityBridge.CNF.complementSat :=
  Shared.ComplexityBridge.CNF.complementSat_computable_of_parse parse_computable

theorem satAtIndex_computable : Computable Shared.ComplexityBridge.CNF.satAtIndex :=
  Shared.ComplexityBridge.CNF.satAtIndex_computable_of_parse parse_computable


end Shared.ComplexityBridge.ParserComputability
