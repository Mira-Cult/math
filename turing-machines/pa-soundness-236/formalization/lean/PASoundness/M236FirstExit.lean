import PASoundness.M236BootstrapCertificate

set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.FastBootstrap.Certificate
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.Bootstrap

/-- Reverse the final right move; the read/write bit there is one. -/
def beforeState : Configuration 237 := ⟨76, -3, moveLeft bootState77.tape (read bootState77.tape)⟩

def beforeOps : List Op := bootOps76.dropLast

theorem beforeChunk : runOps bootState76 beforeOps = some (beforeState, 45610, []) := by decide

/-- The complement of the five bootstrap states has no edge back into them. -/
theorem no_reentry : ∀ (q : Fin 237) (b : Bool),
    ¬ rawState q → ¬ rawState (raw.table.row q b).next := by decide

theorem outside_forward (i k : Nat) (h : ¬ rawState (raw.system.run i).state) :
    ¬ rawState (raw.system.run (i + k)).state := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hn := no_reentry (raw.system.run (i + k)).state
      ((raw.system.run (i + k)).tape (raw.system.run (i + k)).head) ih
    simpa only [Nat.add_succ, Machine.next_state] using hn

theorem before_all (last i : Nat) (h : rawState (raw.system.run last).state)
    (hi : i ≤ last) : rawState (raw.system.run i).state := by
  by_cases hn : rawState (raw.system.run i).state
  · exact hn
  · have ho := outside_forward i (last - i) hn
    have he : i + (last - i) = last := Nat.add_sub_of_le hi
    rw [he] at ho
    exact (ho h).elim

theorem before_block : rawSystem.Block rawSystem.initial 2133491 beforeState [] := by
  have b0 := (runOps_sound bootOps0 bootState0 bootState1 bootTicks0 [] bootChunk0).1
  have b1 := (runOps_sound bootOps1 bootState1 bootState2 bootTicks1 [] bootChunk1).1
  have all1 := b0.trans rawSystem b1
  have b2 := (runOps_sound bootOps2 bootState2 bootState3 bootTicks2 [] bootChunk2).1
  have all2 := all1.trans rawSystem b2
  have b3 := (runOps_sound bootOps3 bootState3 bootState4 bootTicks3 [] bootChunk3).1
  have all3 := all2.trans rawSystem b3
  have b4 := (runOps_sound bootOps4 bootState4 bootState5 bootTicks4 [] bootChunk4).1
  have all4 := all3.trans rawSystem b4
  have b5 := (runOps_sound bootOps5 bootState5 bootState6 bootTicks5 [] bootChunk5).1
  have all5 := all4.trans rawSystem b5
  have b6 := (runOps_sound bootOps6 bootState6 bootState7 bootTicks6 [] bootChunk6).1
  have all6 := all5.trans rawSystem b6
  have b7 := (runOps_sound bootOps7 bootState7 bootState8 bootTicks7 [] bootChunk7).1
  have all7 := all6.trans rawSystem b7
  have b8 := (runOps_sound bootOps8 bootState8 bootState9 bootTicks8 [] bootChunk8).1
  have all8 := all7.trans rawSystem b8
  have b9 := (runOps_sound bootOps9 bootState9 bootState10 bootTicks9 [] bootChunk9).1
  have all9 := all8.trans rawSystem b9
  have b10 := (runOps_sound bootOps10 bootState10 bootState11 bootTicks10 [] bootChunk10).1
  have all10 := all9.trans rawSystem b10
  have b11 := (runOps_sound bootOps11 bootState11 bootState12 bootTicks11 [] bootChunk11).1
  have all11 := all10.trans rawSystem b11
  have b12 := (runOps_sound bootOps12 bootState12 bootState13 bootTicks12 [] bootChunk12).1
  have all12 := all11.trans rawSystem b12
  have b13 := (runOps_sound bootOps13 bootState13 bootState14 bootTicks13 [] bootChunk13).1
  have all13 := all12.trans rawSystem b13
  have b14 := (runOps_sound bootOps14 bootState14 bootState15 bootTicks14 [] bootChunk14).1
  have all14 := all13.trans rawSystem b14
  have b15 := (runOps_sound bootOps15 bootState15 bootState16 bootTicks15 [] bootChunk15).1
  have all15 := all14.trans rawSystem b15
  have b16 := (runOps_sound bootOps16 bootState16 bootState17 bootTicks16 [] bootChunk16).1
  have all16 := all15.trans rawSystem b16
  have b17 := (runOps_sound bootOps17 bootState17 bootState18 bootTicks17 [] bootChunk17).1
  have all17 := all16.trans rawSystem b17
  have b18 := (runOps_sound bootOps18 bootState18 bootState19 bootTicks18 [] bootChunk18).1
  have all18 := all17.trans rawSystem b18
  have b19 := (runOps_sound bootOps19 bootState19 bootState20 bootTicks19 [] bootChunk19).1
  have all19 := all18.trans rawSystem b19
  have b20 := (runOps_sound bootOps20 bootState20 bootState21 bootTicks20 [] bootChunk20).1
  have all20 := all19.trans rawSystem b20
  have b21 := (runOps_sound bootOps21 bootState21 bootState22 bootTicks21 [] bootChunk21).1
  have all21 := all20.trans rawSystem b21
  have b22 := (runOps_sound bootOps22 bootState22 bootState23 bootTicks22 [] bootChunk22).1
  have all22 := all21.trans rawSystem b22
  have b23 := (runOps_sound bootOps23 bootState23 bootState24 bootTicks23 [] bootChunk23).1
  have all23 := all22.trans rawSystem b23
  have b24 := (runOps_sound bootOps24 bootState24 bootState25 bootTicks24 [] bootChunk24).1
  have all24 := all23.trans rawSystem b24
  have b25 := (runOps_sound bootOps25 bootState25 bootState26 bootTicks25 [] bootChunk25).1
  have all25 := all24.trans rawSystem b25
  have b26 := (runOps_sound bootOps26 bootState26 bootState27 bootTicks26 [] bootChunk26).1
  have all26 := all25.trans rawSystem b26
  have b27 := (runOps_sound bootOps27 bootState27 bootState28 bootTicks27 [] bootChunk27).1
  have all27 := all26.trans rawSystem b27
  have b28 := (runOps_sound bootOps28 bootState28 bootState29 bootTicks28 [] bootChunk28).1
  have all28 := all27.trans rawSystem b28
  have b29 := (runOps_sound bootOps29 bootState29 bootState30 bootTicks29 [] bootChunk29).1
  have all29 := all28.trans rawSystem b29
  have b30 := (runOps_sound bootOps30 bootState30 bootState31 bootTicks30 [] bootChunk30).1
  have all30 := all29.trans rawSystem b30
  have b31 := (runOps_sound bootOps31 bootState31 bootState32 bootTicks31 [] bootChunk31).1
  have all31 := all30.trans rawSystem b31
  have b32 := (runOps_sound bootOps32 bootState32 bootState33 bootTicks32 [] bootChunk32).1
  have all32 := all31.trans rawSystem b32
  have b33 := (runOps_sound bootOps33 bootState33 bootState34 bootTicks33 [] bootChunk33).1
  have all33 := all32.trans rawSystem b33
  have b34 := (runOps_sound bootOps34 bootState34 bootState35 bootTicks34 [] bootChunk34).1
  have all34 := all33.trans rawSystem b34
  have b35 := (runOps_sound bootOps35 bootState35 bootState36 bootTicks35 [] bootChunk35).1
  have all35 := all34.trans rawSystem b35
  have b36 := (runOps_sound bootOps36 bootState36 bootState37 bootTicks36 [] bootChunk36).1
  have all36 := all35.trans rawSystem b36
  have b37 := (runOps_sound bootOps37 bootState37 bootState38 bootTicks37 [] bootChunk37).1
  have all37 := all36.trans rawSystem b37
  have b38 := (runOps_sound bootOps38 bootState38 bootState39 bootTicks38 [] bootChunk38).1
  have all38 := all37.trans rawSystem b38
  have b39 := (runOps_sound bootOps39 bootState39 bootState40 bootTicks39 [] bootChunk39).1
  have all39 := all38.trans rawSystem b39
  have b40 := (runOps_sound bootOps40 bootState40 bootState41 bootTicks40 [] bootChunk40).1
  have all40 := all39.trans rawSystem b40
  have b41 := (runOps_sound bootOps41 bootState41 bootState42 bootTicks41 [] bootChunk41).1
  have all41 := all40.trans rawSystem b41
  have b42 := (runOps_sound bootOps42 bootState42 bootState43 bootTicks42 [] bootChunk42).1
  have all42 := all41.trans rawSystem b42
  have b43 := (runOps_sound bootOps43 bootState43 bootState44 bootTicks43 [] bootChunk43).1
  have all43 := all42.trans rawSystem b43
  have b44 := (runOps_sound bootOps44 bootState44 bootState45 bootTicks44 [] bootChunk44).1
  have all44 := all43.trans rawSystem b44
  have b45 := (runOps_sound bootOps45 bootState45 bootState46 bootTicks45 [] bootChunk45).1
  have all45 := all44.trans rawSystem b45
  have b46 := (runOps_sound bootOps46 bootState46 bootState47 bootTicks46 [] bootChunk46).1
  have all46 := all45.trans rawSystem b46
  have b47 := (runOps_sound bootOps47 bootState47 bootState48 bootTicks47 [] bootChunk47).1
  have all47 := all46.trans rawSystem b47
  have b48 := (runOps_sound bootOps48 bootState48 bootState49 bootTicks48 [] bootChunk48).1
  have all48 := all47.trans rawSystem b48
  have b49 := (runOps_sound bootOps49 bootState49 bootState50 bootTicks49 [] bootChunk49).1
  have all49 := all48.trans rawSystem b49
  have b50 := (runOps_sound bootOps50 bootState50 bootState51 bootTicks50 [] bootChunk50).1
  have all50 := all49.trans rawSystem b50
  have b51 := (runOps_sound bootOps51 bootState51 bootState52 bootTicks51 [] bootChunk51).1
  have all51 := all50.trans rawSystem b51
  have b52 := (runOps_sound bootOps52 bootState52 bootState53 bootTicks52 [] bootChunk52).1
  have all52 := all51.trans rawSystem b52
  have b53 := (runOps_sound bootOps53 bootState53 bootState54 bootTicks53 [] bootChunk53).1
  have all53 := all52.trans rawSystem b53
  have b54 := (runOps_sound bootOps54 bootState54 bootState55 bootTicks54 [] bootChunk54).1
  have all54 := all53.trans rawSystem b54
  have b55 := (runOps_sound bootOps55 bootState55 bootState56 bootTicks55 [] bootChunk55).1
  have all55 := all54.trans rawSystem b55
  have b56 := (runOps_sound bootOps56 bootState56 bootState57 bootTicks56 [] bootChunk56).1
  have all56 := all55.trans rawSystem b56
  have b57 := (runOps_sound bootOps57 bootState57 bootState58 bootTicks57 [] bootChunk57).1
  have all57 := all56.trans rawSystem b57
  have b58 := (runOps_sound bootOps58 bootState58 bootState59 bootTicks58 [] bootChunk58).1
  have all58 := all57.trans rawSystem b58
  have b59 := (runOps_sound bootOps59 bootState59 bootState60 bootTicks59 [] bootChunk59).1
  have all59 := all58.trans rawSystem b59
  have b60 := (runOps_sound bootOps60 bootState60 bootState61 bootTicks60 [] bootChunk60).1
  have all60 := all59.trans rawSystem b60
  have b61 := (runOps_sound bootOps61 bootState61 bootState62 bootTicks61 [] bootChunk61).1
  have all61 := all60.trans rawSystem b61
  have b62 := (runOps_sound bootOps62 bootState62 bootState63 bootTicks62 [] bootChunk62).1
  have all62 := all61.trans rawSystem b62
  have b63 := (runOps_sound bootOps63 bootState63 bootState64 bootTicks63 [] bootChunk63).1
  have all63 := all62.trans rawSystem b63
  have b64 := (runOps_sound bootOps64 bootState64 bootState65 bootTicks64 [] bootChunk64).1
  have all64 := all63.trans rawSystem b64
  have b65 := (runOps_sound bootOps65 bootState65 bootState66 bootTicks65 [] bootChunk65).1
  have all65 := all64.trans rawSystem b65
  have b66 := (runOps_sound bootOps66 bootState66 bootState67 bootTicks66 [] bootChunk66).1
  have all66 := all65.trans rawSystem b66
  have b67 := (runOps_sound bootOps67 bootState67 bootState68 bootTicks67 [] bootChunk67).1
  have all67 := all66.trans rawSystem b67
  have b68 := (runOps_sound bootOps68 bootState68 bootState69 bootTicks68 [] bootChunk68).1
  have all68 := all67.trans rawSystem b68
  have b69 := (runOps_sound bootOps69 bootState69 bootState70 bootTicks69 [] bootChunk69).1
  have all69 := all68.trans rawSystem b69
  have b70 := (runOps_sound bootOps70 bootState70 bootState71 bootTicks70 [] bootChunk70).1
  have all70 := all69.trans rawSystem b70
  have b71 := (runOps_sound bootOps71 bootState71 bootState72 bootTicks71 [] bootChunk71).1
  have all71 := all70.trans rawSystem b71
  have b72 := (runOps_sound bootOps72 bootState72 bootState73 bootTicks72 [] bootChunk72).1
  have all72 := all71.trans rawSystem b72
  have b73 := (runOps_sound bootOps73 bootState73 bootState74 bootTicks73 [] bootChunk73).1
  have all73 := all72.trans rawSystem b73
  have b74 := (runOps_sound bootOps74 bootState74 bootState75 bootTicks74 [] bootChunk74).1
  have all74 := all73.trans rawSystem b74
  have b75 := (runOps_sound bootOps75 bootState75 bootState76 bootTicks75 [] bootChunk75).1
  have all75 := all74.trans rawSystem b75
  have last := (runOps_sound beforeOps bootState76 beforeState 45610 [] beforeChunk).1
  have full := all75.trans rawSystem last
  have htime : bootTicks0 + bootTicks1 + bootTicks2 + bootTicks3 + bootTicks4 + bootTicks5 + bootTicks6 + bootTicks7 + bootTicks8 + bootTicks9 + bootTicks10 + bootTicks11 + bootTicks12 + bootTicks13 + bootTicks14 + bootTicks15 + bootTicks16 + bootTicks17 + bootTicks18 + bootTicks19 + bootTicks20 + bootTicks21 + bootTicks22 + bootTicks23 + bootTicks24 + bootTicks25 + bootTicks26 + bootTicks27 + bootTicks28 + bootTicks29 + bootTicks30 + bootTicks31 + bootTicks32 + bootTicks33 + bootTicks34 + bootTicks35 + bootTicks36 + bootTicks37 + bootTicks38 + bootTicks39 + bootTicks40 + bootTicks41 + bootTicks42 + bootTicks43 + bootTicks44 + bootTicks45 + bootTicks46 + bootTicks47 + bootTicks48 + bootTicks49 + bootTicks50 + bootTicks51 + bootTicks52 + bootTicks53 + bootTicks54 + bootTicks55 + bootTicks56 + bootTicks57 + bootTicks58 + bootTicks59 + bootTicks60 + bootTicks61 + bootTicks62 + bootTicks63 + bootTicks64 + bootTicks65 + bootTicks66 + bootTicks67 + bootTicks68 + bootTicks69 + bootTicks70 + bootTicks71 + bootTicks72 + bootTicks73 + bootTicks74 + bootTicks75 + 45610 = 2133491 := by decide
  rw [htime] at full
  change rawSystem.Block bootState0 2133491 beforeState []
  simpa only [List.nil_append] using full

theorem before_state : (raw.system.run 2133491).state = 76 := by
  have hs := raw_run_sound 2133491
  change Related (rawSystem.advance rawSystem.initial 2133491) _ ∧
    rawSystem.wordFrom rawSystem.initial 2133491 = _ at hs
  rw [before_block.endpoint, before_block.output] at hs
  have h := hs.1.1
  rw [machineWordSystem_run] at h
  change (76 : Fin 237) = (raw.system.run 2133491).state at h
  exact h.symm

/-- The checked exit time is the first departure from the bootstrap subgraph. -/
theorem raw_first_exit :
    (∀ i, i < 2133492 → rawState (raw.system.run i).state) ∧
      ¬ rawState (raw.system.run 2133492).state := by
  constructor
  · intro i hi
    apply before_all 2133491 i
    · rw [before_state]; decide
    · omega
  · have h := bootstrap_reached.1.1
    rw [machineWordSystem_run] at h
    change (58 : Fin 237) = (raw.system.run 2133492).state at h
    rw [← h]
    decide

theorem selected_first_exit :
    (∀ i, i < 2133492 → selectedState (machine.system.run i).state) ∧
      ¬ selectedState (machine.system.run 2133492).state := by
  constructor
  · intro i hi
    have h := congrArg (fun c => c.state) (map_run i)
    change mapState (raw.system.run i).state = (machine.system.run i).state at h
    rw [← h]
    exact (mapped_state _).mp (raw_first_exit.1 i hi)
  · have h := bootstrap_reached.2.2.2.2.1
    rw [h]
    decide

theorem selected_first_visit :
    (∀ i, i < 2133492 → (machine.system.run i).state ≠ 57) ∧
      (machine.system.run 2133492).state = 57 := by
  constructor
  · intro i hi he
    have hb := selected_first_exit.1 i hi
    rw [he] at hb
    have hn : ¬ selectedState 57 := by decide
    exact hn hb
  · exact bootstrap_reached.2.2.2.2.1

end PASoundness.M236.FastBootstrap.Certificate
