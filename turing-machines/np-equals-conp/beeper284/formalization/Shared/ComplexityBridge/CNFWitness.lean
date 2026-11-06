import Shared.ComplexityBridge.ParserComputability
import Shared.ComplexityBridge.TM2PairMap

namespace Shared.ComplexityBridge.CNFWitness
open Shared.ComplexityBridge.CNF

/-- Every successfully parsed delimiter block reconstructs its exact input,
including noncanonical payloads and the remaining suffix. -/
theorem undelimit_sound (input payload rest : List Bool)
    (h : BitstringEncoding.undelimit input = some (payload,rest)) :
    BitstringEncoding.delimit payload ++ rest = input := by
  cases input with
  | nil => simp [BitstringEncoding.undelimit] at h
  | cons b input =>
    cases b with
    | false =>
      simp [BitstringEncoding.undelimit] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
    | true =>
      cases input with
      | nil => simp [BitstringEncoding.undelimit] at h
      | cons b input =>
        cases hu : BitstringEncoding.undelimit input with
        | none => simp [BitstringEncoding.undelimit,hu] at h
        | some p =>
          rcases p with ⟨pl,tl⟩
          simp [BitstringEncoding.undelimit,hu] at h
          rcases h with ⟨rfl,rfl⟩
          have hh := undelimit_sound input pl tl hu
          simp [BitstringEncoding.delimit,hh]
termination_by input.length

/-- Successful list-block parsing reconstructs all source bits. -/
theorem blocksAux_sound (fuel : Nat) (input : List Bool) (blocks : List (List Bool))
    (h : BitstringEncoding.undelimitBlocksAux fuel input = some blocks) :
    (blocks.map BitstringEncoding.delimit).flatten = input := by
  induction fuel generalizing input blocks with
  | zero =>
    cases input with
    | nil => simp [BitstringEncoding.undelimitBlocksAux] at h; subst blocks; rfl
    | cons b xs => simp [BitstringEncoding.undelimitBlocksAux] at h
  | succ n ih =>
    cases input with
    | nil => simp [BitstringEncoding.undelimitBlocksAux] at h; subst blocks; rfl
    | cons b xs =>
      cases hu : BitstringEncoding.undelimit (b::xs) with
      | none => simp [BitstringEncoding.undelimitBlocksAux,hu] at h
      | some p =>
        rcases p with ⟨payload,rest⟩
        cases hr : BitstringEncoding.undelimitBlocksAux n rest with
        | none => simp [BitstringEncoding.undelimitBlocksAux,hu,hr] at h
        | some bs =>
          simp [BitstringEncoding.undelimitBlocksAux,hu,hr] at h
          subst blocks
          have htail := ih rest bs hr
          have hhead := undelimit_sound (b::xs) payload rest hu
          simp only [List.map_cons,List.flatten_cons,htail]
          exact hhead

theorem blocks_sound (input : List Bool) (blocks : List (List Bool))
    (h : BitstringEncoding.undelimitBlocks input = some blocks) :
    (blocks.map BitstringEncoding.delimit).flatten = input :=
  blocksAux_sound input.length input blocks h

/-- A block list and all its payload bits fit inside its framed representation. -/
theorem blocks_length_bound (blocks : List (List Bool)) :
    blocks.length + (blocks.map List.length).sum ≤ ((blocks.map BitstringEncoding.delimit).flatten).length := by
  induction blocks with
  | nil => simp
  | cons b bs ih =>
    simp only [List.length_cons,List.map_cons,List.sum_cons,List.flatten_cons,List.length_append,
      BitstringEncoding.length_delimit] at *
    omega

/-- Mapping an option-valued decoder preserves list length on success. -/
theorem mapM_length {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) : xs.length = ys.length := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; rfl
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [List.mapM_cons,ha] at h
    | some b =>
      cases hr : xs.mapM f with
      | none => simp [List.mapM_cons,ha,hr] at h
      | some bs =>
        simp [List.mapM_cons,ha,hr] at h
        subst ys
        simp [ih bs hr]

/-- A successfully decoded list has no more elements than input bits, even
if its elements have noncanonical representations. -/
theorem decoded_list_length {α : Type} [BitstringEncoding α] (input : List Bool) (xs : List α)
    (h : (BitstringEncoding.bitDecode input : Option (List α)) = some xs) : xs.length ≤ input.length := by
  change (BitstringEncoding.undelimitBlocks input).bind (List.mapM BitstringEncoding.bitDecode) = some xs at h
  cases hb : BitstringEncoding.undelimitBlocks input with
  | none => simp [hb] at h
  | some bs =>
    have hm : bs.mapM BitstringEncoding.bitDecode = some xs := by simpa [hb] using h
    have he := blocks_sound input bs hb
    have hl := blocks_length_bound bs
    have hmLen := mapM_length BitstringEncoding.bitDecode bs xs hm
    rw [he] at hl
    omega

/-- A successful pointwise decoder preserves a sum of local size bounds. -/
theorem mapM_weight_bound {α β : Type} (f : α → Option β) (sourceSize : α → Nat) (targetSize : β → Nat)
    (hs : ∀ a b, f a = some b → targetSize b ≤ sourceSize a)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys) :
    (ys.map targetSize).sum ≤ (xs.map sourceSize).sum := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; simp
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [List.mapM_cons,ha] at h
    | some b =>
      cases hr : xs.mapM f with
      | none => simp [List.mapM_cons,ha,hr] at h
      | some bs =>
        simp [List.mapM_cons,ha,hr] at h
        subst ys
        simp only [List.map_cons,List.sum_cons]
        have hh := hs a b ha
        have ht := ih bs hr
        omega

/-- Every literal occurrence in a successfully parsed formula fits within the
raw input length, including inputs which are not canonical encodings. -/
theorem occurrences_le_parsed_input_length (input : List Bool) (formula : Formula)
    (h : parse input = some formula) : (variableOccurrences formula).length ≤ input.length := by
  change (BitstringEncoding.undelimitBlocks input).bind (List.mapM BitstringEncoding.bitDecode) = some formula at h
  cases hb : BitstringEncoding.undelimitBlocks input with
  | none => simp [hb] at h
  | some bs =>
    have hm : bs.mapM (BitstringEncoding.bitDecode (α := Clause)) = some formula := by simpa [hb] using h
    have hs : ∀ a b, (BitstringEncoding.bitDecode a : Option Clause) = some b → b.length ≤ a.length :=
      fun a b h => decoded_list_length a b h
    have hw := mapM_weight_bound (BitstringEncoding.bitDecode (α := Clause)) List.length List.length hs bs formula hm
    have hblock := blocks_length_bound bs
    have hsource := blocks_sound input bs hb
    rw [hsource] at hblock
    simp only [variableOccurrences,List.length_map,List.length_flatten] at *
    omega

/-- The certificate supplies values for variable occurrences. First occurrence
wins, consistently with the exhaustive reference evaluator. Malformed input
is rejected for every certificate. -/
def verify (a : List Bool × List Bool) : Bool :=
  match parse a.1 with
  | none => false
  | some formula => evalFormula (assignment (variableOccurrences formula) a.2) formula

theorem verify_malformed (input witness : List Bool) (h : parse input = none) :
    verify (input,witness) = false := by simp [verify,h]

/-- The actual all-bitstrings SAT reference has occurrence witnesses bounded
by the raw input length. This is a semantic statement, not a time bound. -/
theorem sat_iff_bounded_verifier (input : List Bool) :
    sat input = true ↔ ∃ witness : List Bool,
      witness.length ≤ input.length ∧ verify (input,witness) = true := by
  cases hp : parse input with
  | none => simp [sat,verify,hp]
  | some formula =>
    simp only [sat,hp,verify]
    constructor
    · intro hsat
      change (assignments (variableOccurrences formula).length).any
        (fun bits => evalFormula (assignment (variableOccurrences formula) bits) formula) = true at hsat
      obtain ⟨bits,hm,hv⟩ := List.any_eq_true.mp hsat
      refine ⟨bits,?_,hv⟩
      rw [(mem_assignments_iff bits _).1 hm]
      exact occurrences_le_parsed_input_length input formula hp
    · rintro ⟨w,_,hw⟩
      exact (satFormula_correct formula).2 ⟨assignment (variableOccurrences formula) w,hw⟩

/-- The certificate relation is executable and primitive recursive. This
result by itself does not claim polynomial time. -/
theorem verify_primrec : Primrec verify := by
  have heval : Primrec (fun p : (List Bool × List Bool) × Formula =>
      evalFormula (assignment (variableOccurrences p.2) p.1.2) p.2) := by
    have hargs : Primrec (fun p : (List Bool × List Bool) × Formula =>
        ((variableOccurrences p.2,p.1.2),p.2)) :=
      Primrec.pair (Primrec.pair (variableOccurrences_primrec.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)) Primrec.snd
    exact evalFormula_primrec.comp hargs
  have hp : Primrec (fun a : List Bool × List Bool => parse a.1) :=
    Shared.ComplexityBridge.ParserComputability.parse_primrec.comp Primrec.fst
  have h := Primrec.option_casesOn hp (Primrec.const false) heval.to₂
  apply h.of_eq
  intro a
  cases hparse : parse a.1 <;> simp [verify,hparse]

theorem verify_computable : Computable verify := verify_primrec.to_comp

/-- Exact remaining membership obligation: the concrete certificate relation
must be compiled and bounded in the canonical TM2 polynomial-time model. -/
def VerifierPoly : Prop := ComplexityTheory.IsPolyTime verify

theorem sat_in_NP_of_verifier_poly (h : VerifierPoly) : sat ∈ ComplexityTheory.NP := by
  refine ⟨Polynomial.X,verify,h,?_⟩
  intro input
  change sat input = true ↔ ∃ witness, witness.length ≤ Polynomial.X.eval input.length ∧ verify (input,witness) = true
  simpa using sat_iff_bounded_verifier input

/-- The remaining hardness premise asks for an actual uniform polynomial
many-one reduction from each canonical NP language. -/
def SatHard : Prop := ∀ L : ComplexityTheory.DecisionProblem, L ∈ ComplexityTheory.NP →
  Shared.ComplexityBridge.CanonicalClasses.PolyRed L sat

def complete_of_obligations (hverify : VerifierPoly) (hhard : SatHard) :
    Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage sat :=
  Shared.ComplexityBridge.CanonicalClasses.cnfComplete (sat_in_NP_of_verifier_poly hverify) hhard

/-- Separate conditional endpoint with the two precise SAT obligations and a
progress-sensitive finite-machine comparison certificate. -/
theorem pnp_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M)
    (hverify : VerifierPoly) (hhard : SatHard) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.ComplexityBridge.TM2Compose.pnp_certified_conditional cert (complete_of_obligations hverify hhard)

theorem npconp_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (hverify : VerifierPoly) (hhard : SatHard) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.ComplexityBridge.TM2PairMap.npconp_certified_conditional cert (complete_of_obligations hverify hhard)

namespace Fixtures
/-- A valid formula encoding with a noncanonical binary representation of the
variable 2. Its prefix is still parsed by the public library decoder. -/
def noncanonical : List Bool :=
  BitstringEncoding.delimit (BitstringEncoding.delimit (BitstringEncoding.delimit [false] ++ [true]))

def singleton : Formula := [[(2,true)]]

example : parse noncanonical = some singleton := by decide
example : noncanonical ≠ BitstringEncoding.bitEncode singleton := by decide
example : verify (noncanonical,[true]) = true := by decide
example : sat noncanonical = true := by decide
example : verify ([true],[true]) = false := by decide
example : verify ([],[]) = true := by decide
end Fixtures

end Shared.ComplexityBridge.CNFWitness
