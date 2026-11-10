import PASoundness.Peano
import PASoundness.CompactProof
import PASoundness.CompactMatrix
import PASoundness.CompactMarker
import PASoundness.RawMatrix
import PASoundness.Source
import PASoundness.UniformMachine

/-!
The PA-specific integration boundary. Computation, complete ordered source
output, decoding, quantified duality, and physical refinement are proved in
their own modules. The structures below explicitly name the remaining arithmetic
interpretation, compact prenex transport, and PA contradiction transport. The
fixed marker's compact-calculus behavior is proved separately. No instance is
supplied for the PA238 interpretation or for PA926.
-/
namespace PASoundness.Integration
open FirstOrder
open Observer Shared.Beeping.Machines

def pa : TheoryPresentation where
  Sentence := Peano.Sentence
  proves := Peano.Proves
  trueInN := fun φ => Nat ⊨ φ

/-- Independent closed theorem in Lean's metatheory. -/
theorem pa_standard_soundness : pa.Sound := Peano.soundness

def compactTruth (code : Nat) : Prop :=
  (CompactMatrix.decode code).Realize (fun _ => 0)

/-- Required arbitrary-conclusion proof translations with their standard-truth
lemmas. Equiconsistency alone supplies none of these four fields. Free compact
names are explicitly assigned zero in this interface. -/
structure ArithmeticInterpretation where
  toPA : Nat → Peano.Sentence
  toCompact : Peano.Sentence → Nat
  proofToPA : ∀ f, CompactProof.KProves f → Peano.Proves (toPA f)
  proofToCompact : ∀ φ, Peano.Proves φ → CompactProof.KProves (toCompact φ)
  truthToPA : ∀ f, (Nat ⊨ toPA f) ↔ compactTruth f
  truthToCompact : ∀ (φ : Peano.Sentence), (Nat ⊨ φ) ↔ compactTruth (toCompact φ)

/-- Actual compact-calculus proof transport to recognized singleton alternating
normal forms. `CompactStructural.prenexCoverage` now constructs this payload
from finite proof normalization; the interface itself does not assert it. -/
structure CompactPrenexCoverage : Prop where
  coverage : ∀ f, CompactProof.KProves f →
    ∃ n g r, 0 < n ∧ CompactProof.KProves g ∧
      CompactMatrix.normalize .ex n (CompactMatrix.decode g) = some r ∧
      (compactTruth f ↔ compactTruth g)

/-- Total executable address value. The theorem interpreter and matrix language
are concrete; this function contains no oracle or external soundness test. -/
def value (a : Address) : Bool :=
  CompactMatrix.record CompactProof.theoremCode a.rank a.certificate a.coordinates

/-- The literal numeric prefix/worklist implementation computes exactly the
value used by this integration source, including tuple-length rejection. -/
theorem raw_record_value (a : Address) :
    RawMatrix.record a.rank a.certificate (Marker.encode a.coordinates) =
      RawMatrix.boolNat (value a) :=
  RawMatrix.record_eq_encoded a.rank a.certificate a.coordinates

def source : WordEventSystem Nat Bool := Source.source value
def events : EventStructure := Source.events value

theorem source_complete : Complete events := Source.complete value

theorem normalized_prefix (n p : Nat)
    (hv : CompactMatrix.valid CompactProof.theoremCode n p) :
    compactTruth (CompactProof.theoremCode p) ↔
      altPrefix .ex n (CompactMatrix.matrixTruth CompactProof.theoremCode n p) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hv
  apply (CompactMatrix.normalize_semantics hr (fun _ => 0)).trans
  apply altPrefix_congr_length
  intro xs _
  simp [CompactMatrix.matrixTruth, hr]

/-- Origin and coverage are derived from the stated proof/truth transports,
the recognized normal-form theorem, and the proved postfix certificate compiler.
They are not postulated as an end-to-end soundness equivalence. -/
def normalization (I : ArithmeticInterpretation) (P : CompactPrenexCoverage) :
    NormalizationCertificate pa where
  valid := CompactMatrix.valid CompactProof.theoremCode
  matrix := CompactMatrix.matrixTruth CompactProof.theoremCode
  origin := by
    intro n p _ hv
    refine ⟨I.toPA (CompactProof.theoremCode p),
      I.proofToPA _ (CompactProof.theorem_origin p), ?_⟩
    exact (I.truthToPA _).trans (normalized_prefix n p hv)
  coverage := by
    intro φ hp
    obtain ⟨n, g, r, hn, hg, hr, ht⟩ := P.coverage (I.toCompact φ) (I.proofToCompact φ hp)
    obtain ⟨p, hpcode⟩ := CompactProof.theorem_coverage hg
    have hv : CompactMatrix.valid CompactProof.theoremCode n p := by
      simp [CompactMatrix.valid, hpcode, hr]
    refine ⟨n, hn, p, hv, ?_⟩
    exact (I.truthToCompact φ).trans (ht.trans
      (by simpa [hpcode] using normalized_prefix n p hv))

/-- Closed emitted-relation correctness. Interpretation hypotheses are used only
to select an interface type; the proof uses the total matrix computation alone. -/
theorem emitted_relation (I : ArithmeticInterpretation) (P : CompactPrenexCoverage) :
    EmittedRelation (normalization I P) (Source.recordValues value) := by
  intro n p xs _ hlen
  exact CompactMatrix.record_spec CompactProof.theoremCode n p xs hlen

def bottomValid (p : Nat) : Prop :=
  Marker.bottomTail p = true ∧ value ⟨1, p, [0]⟩ = true

/-- This boundary uses PA's literal logical falsum. It cannot be filled merely
by a consistent theory having some standard-false quantifier-free axiom. -/
structure ContradictionBridge : Prop where
  origin : ∀ p, bottomValid p → Peano.Proves (⊥ : Peano.Sentence)
  coverage : Peano.Proves (⊥ : Peano.Sentence) → ∃ p, bottomValid p

/-- The fixed suffix no longer forms an open end-to-end producer premise.
Only transport between literal compact bottom and literal PA bottom remains. -/
theorem contradictionBridgeOfTransport
    (transport : CompactProof.KProves 1 ↔ Peano.Proves (⊥ : Peano.Sentence)) :
    ContradictionBridge where
  origin := fun p h => transport.mp (CompactMarker.marker_origin p h)
  coverage := fun h => CompactMarker.marker_coverage (transport.mpr h)

/-- An arbitrary-conclusion interpretation with exact bottom maps supplies the
smaller contradiction transport syntactically, without PA soundness. -/
theorem contradictionBridgeOfInterpretation (I : ArithmeticInterpretation)
    (toPABottom : I.toPA 1 = (⊥ : Peano.Sentence))
    (toCompactBottom : I.toCompact (⊥ : Peano.Sentence) = 1) :
    ContradictionBridge :=
  contradictionBridgeOfTransport ⟨
    fun h => toPABottom ▸ I.proofToPA 1 h,
    fun h => toCompactBottom ▸ I.proofToCompact (⊥ : Peano.Sentence) h⟩

/-- Closed exact source theorem for the displayed compact calculus. This is
not silently renamed as PA inconsistency. -/
theorem source_levelZero_iff_KBottom :
    Q_0 .compactSuffix events ↔ CompactProof.KProves 1 :=
  CompactMarker.levelZero_iff_KBottom

theorem machine_levelZero_iff_KBottom {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate source M) :
    Q_0 .compactSuffix (UniformMachine.events cert) ↔ CompactProof.KProves 1 :=
  (UniformMachine.zero_iff_source cert .compactSuffix).trans source_levelZero_iff_KBottom

def bottomCertificates (Z : ContradictionBridge) : BottomCertificates pa where
  bottom := (⊥ : Peano.Sentence)
  falseInN := FirstOrder.Language.Sentence.not_realize_bot Nat
  valid := bottomValid
  origin := Z.origin
  coverage := Z.coverage

theorem zero_emitted_relation (Z : ContradictionBridge) :
    ZeroEmittedRelation (bottomCertificates Z) .compactSuffix events := by
  intro p
  simp [ZeroReceipt, events, Source.emitted_exact, Admissible,
    bottomCertificates, bottomValid]

/-- A conditional exact level-zero theorem with the intended inconsistency
convention. The nonhalting master has not been declared to physically halt. -/
theorem source_levelZero_iff_inconsistent (Z : ContradictionBridge) :
    Q_0 .compactSuffix events ↔ Peano.Proves (⊥ : Peano.Sentence) :=
  levelZero_exact (bottomCertificates Z) .compactSuffix events
    (zero_emitted_relation Z) source_complete

/-- Structural full-soundness reduction. PA standard soundness is not invoked
in this theorem; only the explicit syntactic/semantic bridges are premises. -/
theorem source_iff_sound (I : ArithmeticInterpretation) (P : CompactPrenexCoverage)
    (Z : ContradictionBridge) : SoundnessAcceptance .compactSuffix events ↔ pa.Sound :=
  Source.acceptance_iff_sound (normalization I P) (bottomCertificates Z) value
    (emitted_relation I P) .compactSuffix (zero_emitted_relation Z)

theorem source_formulas_iff_sound (I : ArithmeticInterpretation) (P : CompactPrenexCoverage)
    (Z : ContradictionBridge) : FormulaAcceptance .compactSuffix events ↔ pa.Sound :=
  Source.formulaAcceptance_iff_sound (normalization I P) (bottomCertificates Z) value
    (emitted_relation I P) .compactSuffix (zero_emitted_relation Z)

/-- Complete conditional theorem for any ordinary finite binary machine with
the local implementation certificate. No concrete table certificate is assumed
to have been constructed by naming or hashing its rows. -/
theorem machine_iff_sound (I : ArithmeticInterpretation) (P : CompactPrenexCoverage)
    (Z : ContradictionBridge) {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate source M) :
    SoundnessAcceptance .compactSuffix
      (UnaryCodec.decodedEvents (UnaryCodec.eventTrace (machineWordSystem M cert.labels))) ↔
      pa.Sound :=
  UniformMachine.acceptance_iff_sound (normalization I P) (bottomCertificates Z) value
    (emitted_relation I P) .compactSuffix (zero_emitted_relation Z) cert

theorem machine_omega_iff_unsound (I : ArithmeticInterpretation) (P : CompactPrenexCoverage)
    (Z : ContradictionBridge) {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate source M) :
    Q_omega .compactSuffix
      (UnaryCodec.decodedEvents (UnaryCodec.eventTrace (machineWordSystem M cert.labels))) ↔
      ¬ pa.Sound :=
  UniformMachine.omega_iff_unsound (normalization I P) (bottomCertificates Z) value
    (emitted_relation I P) .compactSuffix (zero_emitted_relation Z) cert

theorem machine_levelZero_iff_inconsistent (Z : ContradictionBridge)
    {n : Nat} {M : Machine n} (cert : ImplementationCertificate source M) :
    Q_0 .compactSuffix
      (UnaryCodec.decodedEvents (UnaryCodec.eventTrace (machineWordSystem M cert.labels))) ↔
      Peano.Proves (⊥ : Peano.Sentence) :=
  UniformMachine.zero_iff_bottom (bottomCertificates Z) value .compactSuffix
    (zero_emitted_relation Z) cert

/-- Corollary: only here is independent PA soundness applied. -/
theorem pa_machine_acceptance (I : ArithmeticInterpretation) (P : CompactPrenexCoverage)
    (Z : ContradictionBridge) {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate source M) :
    SoundnessAcceptance .compactSuffix
      (UnaryCodec.decodedEvents (UnaryCodec.eventTrace (machineWordSystem M cert.labels))) :=
  (machine_iff_sound I P Z cert).mpr pa_standard_soundness

theorem pa_no_finite_failure (I : ArithmeticInterpretation) (P : CompactPrenexCoverage)
    (Z : ContradictionBridge) {n : Nat} {M : Machine n}
    (cert : ImplementationCertificate source M) :
    ¬ Q_omega .compactSuffix
      (UnaryCodec.decodedEvents (UnaryCodec.eventTrace (machineWordSystem M cert.labels))) := by
  have ha := pa_machine_acceptance I P Z cert
  rintro (hz | ⟨k, hk, _, hb⟩)
  · exact ha.2.1 hz.2
  · exact ha.2.2 k hk hb

end PASoundness.Integration
