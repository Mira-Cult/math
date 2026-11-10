import PASoundness.CompactPrenex
import PASoundness.CompactSemantics

/-!
# Constructive normalization in the pinned compact certificate language

Every numeric formula is converted by a total finite algorithm to a literal
positive existential-leading, singleton-alternating prefix over a quantifier-
free matrix. The algorithm carries both K implication proofs. It neither
assumes truth of its input nor obtains coverage from soundness of the theory.
Existing raw certificates can be extended by a normalization tail; the exact
accumulator/stack theorem accounts for every incoming stack.
-/
namespace PASoundness.CompactNormalization

open CompactProof CompactHilbertBasis CompactDerivations CompactNamed
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def freshName (f : Formula) : Nat := f.names.sup id + 1

theorem lt_freshName (f : Formula) (v : Nat) (h : v ∈ f.names) : v < freshName f :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) h)

theorem freshName_fresh (f : Formula) : freshName f ∉ f.names := by
  intro h
  exact Nat.lt_irrefl _ (lt_freshName f _ h)

inductive Alternating : Polarity → Nat → Formula → Prop
  | qf (q : Polarity) (f : Formula) : IsQF f → Alternating q 0 f
  | universal {n x f} : Alternating .ex n f → Alternating .all (n+1) (.all x f)
  | existential {n x f} : Alternating .all n f → Alternating .ex (n+1) (.ex x f)

structure Alternated (f : Formula) (q : Polarity) where
  rank : Nat
  formula : Formula
  equivalent : ProofEquiv f formula
  alternating : Alternating q rank formula

private def qfResult (q : Polarity) (f : Formula) (h : IsQF f) : Alternated f q :=
  ⟨0,f,.refl f,.qf q f h⟩

/-- At most one fresh dummy is inserted before each existing binder. The
recursive call always consumes one original binder, including mismatch cases. -/
def alternate (f : Formula) (q : Polarity) (hp : IsPrenex f) : Alternated f q :=
  match f with
  | .truth => qfResult q .truth trivial
  | .bottom => qfResult q .bottom trivial
  | .member a b => qfResult q (.member a b) trivial
  | .equal a b => qfResult q (.equal a b) trivial
  | .imp a b => qfResult q (.imp a b) hp
  | .all x a =>
      let r := alternate a .ex hp
      match q with
      | .all => ⟨r.rank+1,.all x r.formula,r.equivalent.universal x,
          .universal r.alternating⟩
      | .ex =>
          let body := Formula.all x r.formula
          ⟨r.rank+2,.ex (freshName body) body,
            (r.equivalent.universal x).trans
              (.vacuousExists (freshName body) body (freshName_fresh body)),
            .existential (.universal r.alternating)⟩
  | .ex x a =>
      let r := alternate a .all hp
      match q with
      | .ex => ⟨r.rank+1,.ex x r.formula,r.equivalent.existential x,
          .existential r.alternating⟩
      | .all =>
          let body := Formula.ex x r.formula
          ⟨r.rank+2,.all (freshName body) body,
            (r.equivalent.existential x).trans
              (.vacuousAll (freshName body) body (freshName_fresh body)),
            .universal (.existential r.alternating)⟩

structure Normalized (f : Formula) where
  rank : Nat
  formula : Formula
  positive : 0 < rank
  equivalent : ProofEquiv f formula
  alternating : Alternating .ex rank formula

/-- The leading vacuous existential makes the rank positive even for an
original quantifier-free formula. All names and proofs are computed finitely. -/
def normalizeNamed (f : Formula) : Normalized f :=
  let fr := freshen f (freshName f) (lt_freshName f)
  let pr := prenex fr.formula fr.separated
  let ar := alternate pr.formula .all pr.prenex
  ⟨ar.rank+1,.ex (freshName ar.formula) ar.formula, Nat.zero_lt_succ _,
    ((fr.equivalent.trans pr.equivalent).trans ar.equivalent).trans
      (.vacuousExists (freshName ar.formula) ar.formula (freshName_fresh ar.formula)),
    .existential ar.alternating⟩

theorem decoded_qf (f : Formula) (h : IsQF f) :
    (CompactMatrix.decode f.encode).isQF = true := by
  induction f with
  | truth => rw [Formula.encode, CompactSemantics.decode_zero]; rfl
  | bottom => rw [Formula.encode, RawMatrix.decode_one]; rfl
  | member a b => rw [Formula.encode, CompactSemantics.decode_member]; rfl
  | equal a b => rw [Formula.encode, CompactSemantics.decode_equal]; rfl
  | all | ex => contradiction
  | imp a b ia ib =>
    change (CompactMatrix.decode (imp a.encode b.encode)).isQF = true
    by_cases hz : imp a.encode b.encode = 0
    · rw [hz, CompactSemantics.decode_zero]; rfl
    · rw [CompactSemantics.decode_imp a.encode b.encode hz]
      simp only [CompactMatrix.Formula.isQF, ia h.1, ib h.2, Bool.and_self]

/-- The actual source recognizer accepts the generated literal pattern. -/
theorem alternating_recognized {q : Polarity} {n : Nat} {f : Formula}
    (h : Alternating q n f) :
    ∃ r, CompactMatrix.normalize q n (CompactMatrix.decode f.encode) = some r := by
  induction h with
  | qf q f h =>
    exact ⟨⟨[],CompactMatrix.decode f.encode⟩, by simp [CompactMatrix.normalize,decoded_qf f h]⟩
  | @universal n x f h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨⟨x::r.binders,r.matrix⟩, by
      simp only [Formula.encode,RawMatrix.decode_allCode,CompactMatrix.normalize,
        CompactMatrix.peel,CompactMatrix.peelAll,Option.bind_some,Polarity.flip,hr,
        Option.map_some]⟩
  | @existential n x f h ih =>
    obtain ⟨r,hr⟩ := ih
    exact ⟨⟨x::r.binders,r.matrix⟩, by
      simp only [Formula.encode,RawMatrix.decode_existsCode,CompactMatrix.normalize,
        CompactMatrix.peel,CompactMatrix.peelExists,CompactMatrix.existsAt,
        CompactMatrix.falsity,Option.bind_some,Polarity.flip,hr,Option.map_some]⟩

/-- Uniform result on every numeric source formula, without a proof premise. -/
def result (code : Nat) : Normalized (ofDecoded (CompactMatrix.decode code)) :=
  normalizeNamed (ofDecoded (CompactMatrix.decode code))

def rank (code : Nat) : Nat := (result code).rank

def normalizeCode (code : Nat) : Nat := (result code).formula.encode

theorem rank_positive (code : Nat) : 0 < rank code := (result code).positive

def forward (code : Nat) : KDerivation (imp code (normalizeCode code)) := by
  simpa only [encode_of_code, normalizeCode] using (result code).equivalent.forward

def backward (code : Nat) : KDerivation (imp (normalizeCode code) code) := by
  simpa only [encode_of_code, normalizeCode] using (result code).equivalent.backward

/-- Object-level proof transport: actual derivation in, actual derivation out. -/
def transport {code : Nat} (d : KDerivation code) : KDerivation (normalizeCode code) :=
  .mp d (forward code)

theorem recognized (code : Nat) :
    ∃ r, CompactMatrix.normalize .ex (rank code) (CompactMatrix.decode (normalizeCode code)) = some r :=
  alternating_recognized (result code).alternating

/-- Direct semantic preservation is propagated by the syntax transformations.
It does not use K derivation soundness or the HF comprehension axiom. -/
theorem semantics (code : Nat) (ρ : CompactMatrix.Environment) :
    (CompactMatrix.decode code).Realize ρ ↔
      (CompactMatrix.decode (normalizeCode code)).Realize ρ := by
  have hin := Formula.encode_realize (ofDecoded (CompactMatrix.decode code)) ρ
  rw [encode_of_code] at hin
  exact hin.trans (((result code).equivalent.semantic ρ).trans
    (Formula.encode_realize (result code).formula ρ).symm)

/-- Strong local normalizer tail: every incoming accumulator and every stack
are accounted for, and the original stack is restored exactly. -/
def programTail (code : Nat) : List Nat := program (forward code) ++ [2]

theorem programTail_correct (code stack : Nat) :
    run (programTail code) (code,stack) = (normalizeCode code,stack) := by
  simp only [programTail,run_append,program_correct,run,step_mp]

/-- Normalize a raw compact certificate by preserving its entire instruction
prefix, appending the constructive forward proof, and applying literal MP. -/
def certificateFrom (p : Nat) : Nat :=
  Marker.encode (Marker.decode p ++ programTail (theoremCode p))

theorem certificateFrom_correct (p : Nat) :
    theoremCode (certificateFrom p) = normalizeCode (theoremCode p) := by
  change (sourceLoop (Marker.encode (Marker.decode p ++ programTail (theoremCode p))) (0,0)).1 = _
  rw [sourceLoop_encode,run_append]
  have hs : run (Marker.decode p) (0,0) =
      (theoremCode p,(run (Marker.decode p) (0,0)).2) := by
    apply Prod.ext
    · exact (congrArg Prod.fst (sourceLoop_decode p (0,0))).symm
    · rfl
  rw [hs,programTail_correct]

/-- Full compact prenex coverage with genuine syntactic proof transport. This
is the exact payload needed by the existing Integration interface; it is kept
outside that module to avoid an import cycle. -/
theorem coverage (code : Nat) (h : KProves code) :
    ∃ n g r, 0 < n ∧ KProves g ∧
      CompactMatrix.normalize .ex n (CompactMatrix.decode g) = some r ∧
      ((CompactMatrix.decode code).Realize (fun _ => 0) ↔
        (CompactMatrix.decode g).Realize (fun _ => 0)) := by
  obtain ⟨d⟩ := h
  obtain ⟨r,hr⟩ := recognized code
  exact ⟨rank code,normalizeCode code,r,rank_positive code,⟨transport d⟩,hr,semantics code _⟩

end PASoundness.CompactNormalization
