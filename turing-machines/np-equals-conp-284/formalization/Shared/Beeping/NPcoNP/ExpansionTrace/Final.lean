import Shared.Beeping.NPcoNP.ExpansionTrace.Stage5

/-! Generated expansion certificate. It concerns the literal Lean AST;
it does not prove the JSON-to-AST or Python algorithm correspondence. -/
namespace Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
set_option maxRecDepth 8192

theorem producerTrace : steps producerGrammar.nodes 557 traceState0 = some traceState557 := by
  have h10 : steps producerGrammar.nodes 10 traceState0 = some traceState10 := traceChunk0
  have h20 : steps producerGrammar.nodes 20 traceState0 = some traceState20 :=
    chunks producerGrammar.nodes 10 10 traceState0 traceState10 traceState20 h10 traceChunk10
  have h30 : steps producerGrammar.nodes 30 traceState0 = some traceState30 :=
    chunks producerGrammar.nodes 20 10 traceState0 traceState20 traceState30 h20 traceChunk20
  have h40 : steps producerGrammar.nodes 40 traceState0 = some traceState40 :=
    chunks producerGrammar.nodes 30 10 traceState0 traceState30 traceState40 h30 traceChunk30
  have h50 : steps producerGrammar.nodes 50 traceState0 = some traceState50 :=
    chunks producerGrammar.nodes 40 10 traceState0 traceState40 traceState50 h40 traceChunk40
  have h60 : steps producerGrammar.nodes 60 traceState0 = some traceState60 :=
    chunks producerGrammar.nodes 50 10 traceState0 traceState50 traceState60 h50 traceChunk50
  have h70 : steps producerGrammar.nodes 70 traceState0 = some traceState70 :=
    chunks producerGrammar.nodes 60 10 traceState0 traceState60 traceState70 h60 traceChunk60
  have h80 : steps producerGrammar.nodes 80 traceState0 = some traceState80 :=
    chunks producerGrammar.nodes 70 10 traceState0 traceState70 traceState80 h70 traceChunk70
  have h90 : steps producerGrammar.nodes 90 traceState0 = some traceState90 :=
    chunks producerGrammar.nodes 80 10 traceState0 traceState80 traceState90 h80 traceChunk80
  have h100 : steps producerGrammar.nodes 100 traceState0 = some traceState100 :=
    chunks producerGrammar.nodes 90 10 traceState0 traceState90 traceState100 h90 traceChunk90
  have h110 : steps producerGrammar.nodes 110 traceState0 = some traceState110 :=
    chunks producerGrammar.nodes 100 10 traceState0 traceState100 traceState110 h100 traceChunk100
  have h120 : steps producerGrammar.nodes 120 traceState0 = some traceState120 :=
    chunks producerGrammar.nodes 110 10 traceState0 traceState110 traceState120 h110 traceChunk110
  have h130 : steps producerGrammar.nodes 130 traceState0 = some traceState130 :=
    chunks producerGrammar.nodes 120 10 traceState0 traceState120 traceState130 h120 traceChunk120
  have h140 : steps producerGrammar.nodes 140 traceState0 = some traceState140 :=
    chunks producerGrammar.nodes 130 10 traceState0 traceState130 traceState140 h130 traceChunk130
  have h150 : steps producerGrammar.nodes 150 traceState0 = some traceState150 :=
    chunks producerGrammar.nodes 140 10 traceState0 traceState140 traceState150 h140 traceChunk140
  have h160 : steps producerGrammar.nodes 160 traceState0 = some traceState160 :=
    chunks producerGrammar.nodes 150 10 traceState0 traceState150 traceState160 h150 traceChunk150
  have h170 : steps producerGrammar.nodes 170 traceState0 = some traceState170 :=
    chunks producerGrammar.nodes 160 10 traceState0 traceState160 traceState170 h160 traceChunk160
  have h180 : steps producerGrammar.nodes 180 traceState0 = some traceState180 :=
    chunks producerGrammar.nodes 170 10 traceState0 traceState170 traceState180 h170 traceChunk170
  have h190 : steps producerGrammar.nodes 190 traceState0 = some traceState190 :=
    chunks producerGrammar.nodes 180 10 traceState0 traceState180 traceState190 h180 traceChunk180
  have h200 : steps producerGrammar.nodes 200 traceState0 = some traceState200 :=
    chunks producerGrammar.nodes 190 10 traceState0 traceState190 traceState200 h190 traceChunk190
  have h210 : steps producerGrammar.nodes 210 traceState0 = some traceState210 :=
    chunks producerGrammar.nodes 200 10 traceState0 traceState200 traceState210 h200 traceChunk200
  have h220 : steps producerGrammar.nodes 220 traceState0 = some traceState220 :=
    chunks producerGrammar.nodes 210 10 traceState0 traceState210 traceState220 h210 traceChunk210
  have h230 : steps producerGrammar.nodes 230 traceState0 = some traceState230 :=
    chunks producerGrammar.nodes 220 10 traceState0 traceState220 traceState230 h220 traceChunk220
  have h240 : steps producerGrammar.nodes 240 traceState0 = some traceState240 :=
    chunks producerGrammar.nodes 230 10 traceState0 traceState230 traceState240 h230 traceChunk230
  have h250 : steps producerGrammar.nodes 250 traceState0 = some traceState250 :=
    chunks producerGrammar.nodes 240 10 traceState0 traceState240 traceState250 h240 traceChunk240
  have h260 : steps producerGrammar.nodes 260 traceState0 = some traceState260 :=
    chunks producerGrammar.nodes 250 10 traceState0 traceState250 traceState260 h250 traceChunk250
  have h270 : steps producerGrammar.nodes 270 traceState0 = some traceState270 :=
    chunks producerGrammar.nodes 260 10 traceState0 traceState260 traceState270 h260 traceChunk260
  have h280 : steps producerGrammar.nodes 280 traceState0 = some traceState280 :=
    chunks producerGrammar.nodes 270 10 traceState0 traceState270 traceState280 h270 traceChunk270
  have h290 : steps producerGrammar.nodes 290 traceState0 = some traceState290 :=
    chunks producerGrammar.nodes 280 10 traceState0 traceState280 traceState290 h280 traceChunk280
  have h300 : steps producerGrammar.nodes 300 traceState0 = some traceState300 :=
    chunks producerGrammar.nodes 290 10 traceState0 traceState290 traceState300 h290 traceChunk290
  have h310 : steps producerGrammar.nodes 310 traceState0 = some traceState310 :=
    chunks producerGrammar.nodes 300 10 traceState0 traceState300 traceState310 h300 traceChunk300
  have h320 : steps producerGrammar.nodes 320 traceState0 = some traceState320 :=
    chunks producerGrammar.nodes 310 10 traceState0 traceState310 traceState320 h310 traceChunk310
  have h330 : steps producerGrammar.nodes 330 traceState0 = some traceState330 :=
    chunks producerGrammar.nodes 320 10 traceState0 traceState320 traceState330 h320 traceChunk320
  have h340 : steps producerGrammar.nodes 340 traceState0 = some traceState340 :=
    chunks producerGrammar.nodes 330 10 traceState0 traceState330 traceState340 h330 traceChunk330
  have h350 : steps producerGrammar.nodes 350 traceState0 = some traceState350 :=
    chunks producerGrammar.nodes 340 10 traceState0 traceState340 traceState350 h340 traceChunk340
  have h360 : steps producerGrammar.nodes 360 traceState0 = some traceState360 :=
    chunks producerGrammar.nodes 350 10 traceState0 traceState350 traceState360 h350 traceChunk350
  have h370 : steps producerGrammar.nodes 370 traceState0 = some traceState370 :=
    chunks producerGrammar.nodes 360 10 traceState0 traceState360 traceState370 h360 traceChunk360
  have h380 : steps producerGrammar.nodes 380 traceState0 = some traceState380 :=
    chunks producerGrammar.nodes 370 10 traceState0 traceState370 traceState380 h370 traceChunk370
  have h390 : steps producerGrammar.nodes 390 traceState0 = some traceState390 :=
    chunks producerGrammar.nodes 380 10 traceState0 traceState380 traceState390 h380 traceChunk380
  have h400 : steps producerGrammar.nodes 400 traceState0 = some traceState400 :=
    chunks producerGrammar.nodes 390 10 traceState0 traceState390 traceState400 h390 traceChunk390
  have h410 : steps producerGrammar.nodes 410 traceState0 = some traceState410 :=
    chunks producerGrammar.nodes 400 10 traceState0 traceState400 traceState410 h400 traceChunk400
  have h420 : steps producerGrammar.nodes 420 traceState0 = some traceState420 :=
    chunks producerGrammar.nodes 410 10 traceState0 traceState410 traceState420 h410 traceChunk410
  have h430 : steps producerGrammar.nodes 430 traceState0 = some traceState430 :=
    chunks producerGrammar.nodes 420 10 traceState0 traceState420 traceState430 h420 traceChunk420
  have h440 : steps producerGrammar.nodes 440 traceState0 = some traceState440 :=
    chunks producerGrammar.nodes 430 10 traceState0 traceState430 traceState440 h430 traceChunk430
  have h450 : steps producerGrammar.nodes 450 traceState0 = some traceState450 :=
    chunks producerGrammar.nodes 440 10 traceState0 traceState440 traceState450 h440 traceChunk440
  have h460 : steps producerGrammar.nodes 460 traceState0 = some traceState460 :=
    chunks producerGrammar.nodes 450 10 traceState0 traceState450 traceState460 h450 traceChunk450
  have h470 : steps producerGrammar.nodes 470 traceState0 = some traceState470 :=
    chunks producerGrammar.nodes 460 10 traceState0 traceState460 traceState470 h460 traceChunk460
  have h480 : steps producerGrammar.nodes 480 traceState0 = some traceState480 :=
    chunks producerGrammar.nodes 470 10 traceState0 traceState470 traceState480 h470 traceChunk470
  have h490 : steps producerGrammar.nodes 490 traceState0 = some traceState490 :=
    chunks producerGrammar.nodes 480 10 traceState0 traceState480 traceState490 h480 traceChunk480
  have h500 : steps producerGrammar.nodes 500 traceState0 = some traceState500 :=
    chunks producerGrammar.nodes 490 10 traceState0 traceState490 traceState500 h490 traceChunk490
  have h510 : steps producerGrammar.nodes 510 traceState0 = some traceState510 :=
    chunks producerGrammar.nodes 500 10 traceState0 traceState500 traceState510 h500 traceChunk500
  have h520 : steps producerGrammar.nodes 520 traceState0 = some traceState520 :=
    chunks producerGrammar.nodes 510 10 traceState0 traceState510 traceState520 h510 traceChunk510
  have h530 : steps producerGrammar.nodes 530 traceState0 = some traceState530 :=
    chunks producerGrammar.nodes 520 10 traceState0 traceState520 traceState530 h520 traceChunk520
  have h540 : steps producerGrammar.nodes 540 traceState0 = some traceState540 :=
    chunks producerGrammar.nodes 530 10 traceState0 traceState530 traceState540 h530 traceChunk530
  have h550 : steps producerGrammar.nodes 550 traceState0 = some traceState550 :=
    chunks producerGrammar.nodes 540 10 traceState0 traceState540 traceState550 h540 traceChunk540
  exact chunks producerGrammar.nodes 550 7 traceState0 traceState550 traceState557 h550 traceChunk550

theorem producerExpand : expand producerGrammar.nodes 53 (.node producerGrammar.root) [true,true,false] [] {} = some traceState557.acc := by
  apply certify producerGrammar.nodes ⟨53, .node producerGrammar.root, [true,true,false], []⟩ 557 traceState557.acc
  change steps producerGrammar.nodes 557 traceState0 = some traceState557
  exact producerTrace

theorem producerStartCount : traceState557.acc.starts.size = 557 := by rfl
theorem producerLeafCount : traceState557.acc.leaves.size = 279 := by rfl

end Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
