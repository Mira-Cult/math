import Shared.ComplexityBridge.TM2OutputProtectedRaw

/-! Replace the raw-output placeholder with an arbitrary valid finite binary
verifier. Both physical handoffs are paid and blank-equivalent tape padding is
tracked. Empty protected output remains a separate source path. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputProtectedVerifier

open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.TM2BinaryPostCosts (Alphabet)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (verifier : Program) : Program :=
  Shared.Codes.FiniteProgramOneExit.program (TM2OutputProtectedRaw.program tm enc out) verifier
    (TM2OutputProtectedRaw.rawExit tm enc out)

theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (verifier : Program) (hv : valid verifier = true) :
    valid (program tm enc out verifier) = true :=
  Shared.Codes.FiniteProgramOneExit.program_valid _ _ _ (TM2OutputProtectedRaw.program_valid tm enc out)
    hv (TM2OutputProtectedRaw.rawExit_bound tm enc out)

/-- An accepted or rejected finite verifier run is preserved across the
concrete protected-output and raw-tape handoffs. No unbounded evaluation is
assumed; `fuel` is the explicit clock for the supplied verifier. -/
theorem run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (verifier : Program) (hv : valid verifier = true)
    (bits : List Bool) (first : Bool) (bs : List Bool) (hrev : bits.reverse = first::bs)
    (t : Tape) (ht : TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (TM2BinaryOutputShape.outputBits tm (TM2OutputProtectedCodec.encode tm enc) (bits.map out.symm)))
    (fuel : Nat) (answer : Bool) (hbounded : bounded verifier bits fuel = some answer) :
    run (program tm enc out verifier) (0,t) (TM2OutputProtectedRaw.cost tm enc out bits bs+2+fuel) =
      some (.inl answer) := by
  let p := TM2OutputProtectedRaw.program tm enc out
  let e := TM2OutputProtectedRaw.rawExit tm enc out
  let n := TM2OutputProtectedRaw.cost tm enc out bits bs
  have hp : valid p = true := TM2OutputProtectedRaw.program_valid tm enc out
  have hp0 : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have he : e < p.length := TM2OutputProtectedRaw.rawExit_bound tm enc out
  have hstop : ∀ u, step p (e,u) = some (.inl false) := TM2OutputProtectedRaw.rawExit_placeholder tm enc out
  obtain ⟨u,hu,hurel⟩ := TM2OutputProtectedRaw.run_nonempty tm enc dec hdec enc0 out bits first bs hrev t ht
  have hpre := Shared.Codes.FiniteProgramOneExit.first_entry p verifier e (0,t) (e,u) n hp hp0 hstop hu
  have hhand := Shared.Codes.FiniteProgramOneExit.handoff p verifier e he u
  let bounced := Shared.Codes.FiniteProgramThreeExit.bounce u
  have hrel : TapeRel bounced (initial bits).2 :=
    (Shared.Codes.FiniteProgramThreeExit.bounce_related u).trans hurel
  have href : run verifier (initial bits) fuel = some (.inl answer) := by
    unfold bounded at hbounded
    cases hr : run verifier (initial bits) fuel with
    | none => simp [hr] at hbounded
    | some s =>
      cases s with
      | inl b => simp [hr] at hbounded; subst b; rfl
      | inr c => simp [hr] at hbounded
  have hr := run_related verifier (0,bounced) (initial bits) rfl hrel fuel
  rw [href] at hr
  have hactual : run verifier (0,bounced) fuel = some (.inl answer) := by
    cases ha : run verifier (0,bounced) fuel with
    | none => simp [ha,StatusRel] at hr
    | some s =>
      cases s with
      | inl b => simp [ha,StatusRel] at hr; subst b; rfl
      | inr c => simp [ha,StatusRel] at hr
  have hv0 : 0 < verifier.length := Shared.Codes.FiniteProgramLink.valid_nonempty verifier hv
  have hshift := Shared.Codes.FiniteProgramOneExit.continuation p verifier e hv (0,bounced) hv0 fuel
  rw [hactual] at hshift
  change run (Shared.Codes.FiniteProgramOneExit.program p verifier e) (0,t) (n+2+fuel) = _
  rw [show n+2+fuel=n+(2+fuel) by omega,
    run_continue _ _ _ _ _ hpre,run_continue _ _ _ _ _ hhand]
  simpa [program,p,e,n,bounced,shiftConfig,shiftStatus] using hshift

end Shared.ComplexityBridge.TM2OutputProtectedVerifier
