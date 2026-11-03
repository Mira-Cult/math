import Shared.PNP.Record285.TextSegments

/-! Generated row segments. Each segment is parsed and compared with
the numeric data by kernel reduction. Equality with the embedded source
file is a separate explicit premise in `literal_binding`. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.TextCertificate
open Shared.PNP.Record285 Shared.PNP.Record285.NumericBinding
open Shared.PNP.Record285.NumericTables Shared.PNP.Record285.TextSegments
open Shared.Beeping.Machines

def lines0 : List String := ["0 0 1 R 2 0","0 1 1 L 3 0","1 0 1 R 55 0","1 1 0 L 1 0","2 0 0 L 0 0","2 1 0 L 4 0","3 0 1 L 0 0","3 1 1 R 76 0"]
def rows0 : List RawRow := [⟨0,0,1,.right,2,0⟩,⟨0,1,1,.left,3,0⟩,⟨1,0,1,.right,55,0⟩,⟨1,1,0,.left,1,0⟩,⟨2,0,0,.left,0,0⟩,⟨2,1,0,.left,4,0⟩,⟨3,0,1,.left,0,0⟩,⟨3,1,1,.right,76,0⟩]
def data0 : List DataRow := [(true,true,2,false),(true,false,3,false),(true,true,55,false),(false,false,1,false),(false,false,0,false),(false,false,4,false),(true,false,0,false),(true,true,76,false)]
theorem parsed0 : lines0.mapM (fun s => parseRow s.toList) = some rows0 := by decide
theorem mapped0 : rows0.map markedData = data0 := by decide
theorem clean0 : lines0.all clean = true := by decide

def lines1 : List String := ["4 0 1 L 2 0","4 1 1 R 5 0","5 0 0 R 4 0","5 1 0 R 2 0","6 0 1 L 119 0","6 1 1 R 7 0","7 0 0 R 6 0","7 1 1 R 8 0"]
def rows1 : List RawRow := [⟨4,0,1,.left,2,0⟩,⟨4,1,1,.right,5,0⟩,⟨5,0,0,.right,4,0⟩,⟨5,1,0,.right,2,0⟩,⟨6,0,1,.left,119,0⟩,⟨6,1,1,.right,7,0⟩,⟨7,0,0,.right,6,0⟩,⟨7,1,1,.right,8,0⟩]
def data1 : List DataRow := [(true,false,2,false),(true,true,5,false),(false,true,4,false),(false,true,2,false),(true,false,119,false),(true,true,7,false),(false,true,6,false),(true,true,8,false)]
theorem parsed1 : lines1.mapM (fun s => parseRow s.toList) = some rows1 := by decide
theorem mapped1 : rows1.map markedData = data1 := by decide
theorem clean1 : lines1.all clean = true := by decide

def lines2 : List String := ["8 0 0 R 76 0","8 1 1 R 75 0","9 0 0 R 10 0","9 1 1 R 68 0","10 0 1 R 10 0","10 1 1 L 119 0","11 0 0 R 13 0","11 1 1 R 11 0"]
def rows2 : List RawRow := [⟨8,0,0,.right,76,0⟩,⟨8,1,1,.right,75,0⟩,⟨9,0,0,.right,10,0⟩,⟨9,1,1,.right,68,0⟩,⟨10,0,1,.right,10,0⟩,⟨10,1,1,.left,119,0⟩,⟨11,0,0,.right,13,0⟩,⟨11,1,1,.right,11,0⟩]
def data2 : List DataRow := [(false,true,76,false),(true,true,75,false),(false,true,10,false),(true,true,68,false),(true,true,10,false),(true,false,119,false),(false,true,13,false),(true,true,11,false)]
theorem parsed2 : lines2.mapM (fun s => parseRow s.toList) = some rows2 := by decide
theorem mapped2 : rows2.map markedData = data2 := by decide
theorem clean2 : lines2.all clean = true := by decide

def lines3 : List String := ["12 0 0 R 14 0","12 1 1 R 12 0","13 0 1 L 53 0","13 1 0 R 45 0","14 0 1 R 50 0","14 1 1 R 14 0","15 0 0 R 11 0","15 1 1 R 15 0"]
def rows3 : List RawRow := [⟨12,0,0,.right,14,0⟩,⟨12,1,1,.right,12,0⟩,⟨13,0,1,.left,53,0⟩,⟨13,1,0,.right,45,0⟩,⟨14,0,1,.right,50,0⟩,⟨14,1,1,.right,14,0⟩,⟨15,0,0,.right,11,0⟩,⟨15,1,1,.right,15,0⟩]
def data3 : List DataRow := [(false,true,14,false),(true,true,12,false),(true,false,53,false),(false,true,45,false),(true,true,50,false),(true,true,14,false),(false,true,11,false),(true,true,15,false)]
theorem parsed3 : lines3.mapM (fun s => parseRow s.toList) = some rows3 := by decide
theorem mapped3 : rows3.map markedData = data3 := by decide
theorem clean3 : lines3.all clean = true := by decide

def lines4 : List String := ["16 0 0 R 12 0","16 1 1 R 16 0","17 0 0 R 15 0","17 1 1 R 17 0","18 0 0 R 16 0","18 1 1 R 18 0","19 0 0 R 43 0","19 1 1 R 19 0"]
def rows4 : List RawRow := [⟨16,0,0,.right,12,0⟩,⟨16,1,1,.right,16,0⟩,⟨17,0,0,.right,15,0⟩,⟨17,1,1,.right,17,0⟩,⟨18,0,0,.right,16,0⟩,⟨18,1,1,.right,18,0⟩,⟨19,0,0,.right,43,0⟩,⟨19,1,1,.right,19,0⟩]
def data4 : List DataRow := [(false,true,12,false),(true,true,16,false),(false,true,15,false),(true,true,17,false),(false,true,16,false),(true,true,18,false),(false,true,43,false),(true,true,19,false)]
theorem parsed4 : lines4.mapM (fun s => parseRow s.toList) = some rows4 := by decide
theorem mapped4 : rows4.map markedData = data4 := by decide
theorem clean4 : lines4.all clean = true := by decide

def lines5 : List String := ["20 0 0 R 44 0","20 1 1 R 20 0","21 0 0 R 19 0","21 1 1 R 21 0","22 0 0 R 20 0","22 1 1 R 22 0","23 0 0 R 21 0","23 1 1 R 23 0"]
def rows5 : List RawRow := [⟨20,0,0,.right,44,0⟩,⟨20,1,1,.right,20,0⟩,⟨21,0,0,.right,19,0⟩,⟨21,1,1,.right,21,0⟩,⟨22,0,0,.right,20,0⟩,⟨22,1,1,.right,22,0⟩,⟨23,0,0,.right,21,0⟩,⟨23,1,1,.right,23,0⟩]
def data5 : List DataRow := [(false,true,44,false),(true,true,20,false),(false,true,19,false),(true,true,21,false),(false,true,20,false),(true,true,22,false),(false,true,21,false),(true,true,23,false)]
theorem parsed5 : lines5.mapM (fun s => parseRow s.toList) = some rows5 := by decide
theorem mapped5 : rows5.map markedData = data5 := by decide
theorem clean5 : lines5.all clean = true := by decide

def lines6 : List String := ["24 0 0 R 22 0","24 1 1 R 24 0","25 0 0 R 23 0","25 1 1 R 25 0","26 0 0 R 24 0","26 1 1 R 26 0","27 0 0 R 25 0","27 1 1 R 27 0"]
def rows6 : List RawRow := [⟨24,0,0,.right,22,0⟩,⟨24,1,1,.right,24,0⟩,⟨25,0,0,.right,23,0⟩,⟨25,1,1,.right,25,0⟩,⟨26,0,0,.right,24,0⟩,⟨26,1,1,.right,26,0⟩,⟨27,0,0,.right,25,0⟩,⟨27,1,1,.right,27,0⟩]
def data6 : List DataRow := [(false,true,22,false),(true,true,24,false),(false,true,23,false),(true,true,25,false),(false,true,24,false),(true,true,26,false),(false,true,25,false),(true,true,27,false)]
theorem parsed6 : lines6.mapM (fun s => parseRow s.toList) = some rows6 := by decide
theorem mapped6 : rows6.map markedData = data6 := by decide
theorem clean6 : lines6.all clean = true := by decide

def lines7 : List String := ["28 0 0 R 26 0","28 1 1 R 28 0","29 0 0 R 17 0","29 1 1 R 29 0","30 0 0 R 18 0","30 1 1 R 30 0","31 0 0 R 29 0","31 1 1 R 31 0"]
def rows7 : List RawRow := [⟨28,0,0,.right,26,0⟩,⟨28,1,1,.right,28,0⟩,⟨29,0,0,.right,17,0⟩,⟨29,1,1,.right,29,0⟩,⟨30,0,0,.right,18,0⟩,⟨30,1,1,.right,30,0⟩,⟨31,0,0,.right,29,0⟩,⟨31,1,1,.right,31,0⟩]
def data7 : List DataRow := [(false,true,26,false),(true,true,28,false),(false,true,17,false),(true,true,29,false),(false,true,18,false),(true,true,30,false),(false,true,29,false),(true,true,31,false)]
theorem parsed7 : lines7.mapM (fun s => parseRow s.toList) = some rows7 := by decide
theorem mapped7 : rows7.map markedData = data7 := by decide
theorem clean7 : lines7.all clean = true := by decide

def lines8 : List String := ["32 0 0 R 30 0","32 1 1 R 32 0","33 0 0 R 31 0","33 1 1 R 33 0","34 0 0 R 32 0","34 1 1 R 34 0","35 0 0 R 33 0","35 1 1 R 35 0"]
def rows8 : List RawRow := [⟨32,0,0,.right,30,0⟩,⟨32,1,1,.right,32,0⟩,⟨33,0,0,.right,31,0⟩,⟨33,1,1,.right,33,0⟩,⟨34,0,0,.right,32,0⟩,⟨34,1,1,.right,34,0⟩,⟨35,0,0,.right,33,0⟩,⟨35,1,1,.right,35,0⟩]
def data8 : List DataRow := [(false,true,30,false),(true,true,32,false),(false,true,31,false),(true,true,33,false),(false,true,32,false),(true,true,34,false),(false,true,33,false),(true,true,35,false)]
theorem parsed8 : lines8.mapM (fun s => parseRow s.toList) = some rows8 := by decide
theorem mapped8 : rows8.map markedData = data8 := by decide
theorem clean8 : lines8.all clean = true := by decide

def lines9 : List String := ["36 0 0 R 34 0","36 1 1 R 36 0","37 0 0 R 35 0","37 1 1 R 37 0","38 0 0 R 36 0","38 1 1 R 38 0","39 0 0 R 37 0","39 1 1 R 39 0"]
def rows9 : List RawRow := [⟨36,0,0,.right,34,0⟩,⟨36,1,1,.right,36,0⟩,⟨37,0,0,.right,35,0⟩,⟨37,1,1,.right,37,0⟩,⟨38,0,0,.right,36,0⟩,⟨38,1,1,.right,38,0⟩,⟨39,0,0,.right,37,0⟩,⟨39,1,1,.right,39,0⟩]
def data9 : List DataRow := [(false,true,34,false),(true,true,36,false),(false,true,35,false),(true,true,37,false),(false,true,36,false),(true,true,38,false),(false,true,37,false),(true,true,39,false)]
theorem parsed9 : lines9.mapM (fun s => parseRow s.toList) = some rows9 := by decide
theorem mapped9 : rows9.map markedData = data9 := by decide
theorem clean9 : lines9.all clean = true := by decide

def lines10 : List String := ["40 0 0 R 38 0","40 1 1 R 40 0","41 0 0 R 39 0","41 1 1 R 41 0","42 0 0 R 40 0","42 1 1 R 42 0","43 0 0 R 41 0","43 1 1 R 43 0"]
def rows10 : List RawRow := [⟨40,0,0,.right,38,0⟩,⟨40,1,1,.right,40,0⟩,⟨41,0,0,.right,39,0⟩,⟨41,1,1,.right,41,0⟩,⟨42,0,0,.right,40,0⟩,⟨42,1,1,.right,42,0⟩,⟨43,0,0,.right,41,0⟩,⟨43,1,1,.right,43,0⟩]
def data10 : List DataRow := [(false,true,38,false),(true,true,40,false),(false,true,39,false),(true,true,41,false),(false,true,40,false),(true,true,42,false),(false,true,41,false),(true,true,43,false)]
theorem parsed10 : lines10.mapM (fun s => parseRow s.toList) = some rows10 := by decide
theorem mapped10 : rows10.map markedData = data10 := by decide
theorem clean10 : lines10.all clean = true := by decide

def lines11 : List String := ["44 0 0 R 42 0","44 1 1 R 44 0","45 0 0 L 13 0","45 1 1 R 46 0","46 0 0 R 47 0","46 1 1 R 46 0","47 0 0 L 48 0","47 1 1 R 46 0"]
def rows11 : List RawRow := [⟨44,0,0,.right,42,0⟩,⟨44,1,1,.right,44,0⟩,⟨45,0,0,.left,13,0⟩,⟨45,1,1,.right,46,0⟩,⟨46,0,0,.right,47,0⟩,⟨46,1,1,.right,46,0⟩,⟨47,0,0,.left,48,0⟩,⟨47,1,1,.right,46,0⟩]
def data11 : List DataRow := [(false,true,42,false),(true,true,44,false),(false,false,13,false),(true,true,46,false),(false,true,47,false),(true,true,46,false),(false,false,48,false),(true,true,46,false)]
theorem parsed11 : lines11.mapM (fun s => parseRow s.toList) = some rows11 := by decide
theorem mapped11 : rows11.map markedData = data11 := by decide
theorem clean11 : lines11.all clean = true := by decide

def lines12 : List String := ["48 0 1 L 49 0","48 1 1 L 48 0","49 0 0 L 51 0","49 1 0 L 48 0","50 0 0 L 51 0","50 1 0 R 14 0","51 0 0 L 52 0","51 1 1 L 51 0"]
def rows12 : List RawRow := [⟨48,0,1,.left,49,0⟩,⟨48,1,1,.left,48,0⟩,⟨49,0,0,.left,51,0⟩,⟨49,1,0,.left,48,0⟩,⟨50,0,0,.left,51,0⟩,⟨50,1,0,.right,14,0⟩,⟨51,0,0,.left,52,0⟩,⟨51,1,1,.left,51,0⟩]
def data12 : List DataRow := [(true,false,49,false),(true,false,48,false),(false,false,51,false),(false,false,48,false),(false,false,51,false),(false,true,14,false),(false,false,52,false),(true,false,51,false)]
theorem parsed12 : lines12.mapM (fun s => parseRow s.toList) = some rows12 := by decide
theorem mapped12 : rows12.map markedData = data12 := by decide
theorem clean12 : lines12.all clean = true := by decide

def lines13 : List String := ["52 0 0 L 1 0","52 1 1 L 51 0","53 0 0 L 54 0","53 1 1 L 53 0","54 0 0 L 117 0","54 1 1 L 53 0","55 0 0 R 55 0","55 1 0 R 56 0"]
def rows13 : List RawRow := [⟨52,0,0,.left,1,0⟩,⟨52,1,1,.left,51,0⟩,⟨53,0,0,.left,54,0⟩,⟨53,1,1,.left,53,0⟩,⟨54,0,0,.left,117,0⟩,⟨54,1,1,.left,53,0⟩,⟨55,0,0,.right,55,0⟩,⟨55,1,0,.right,56,0⟩]
def data13 : List DataRow := [(false,false,1,false),(true,false,51,false),(false,false,54,false),(true,false,53,false),(false,false,117,false),(true,false,53,false),(false,true,55,false),(false,true,56,false)]
theorem parsed13 : lines13.mapM (fun s => parseRow s.toList) = some rows13 := by decide
theorem mapped13 : rows13.map markedData = data13 := by decide
theorem clean13 : lines13.all clean = true := by decide

def lines14 : List String := ["56 0 0 L 6 0","56 1 0 R 56 0","57 0 1 R 67 0","57 1 0 R 46 0","58 0 0 R 46 0","58 1 1 R 57 0","59 0 0 R 60 0","59 1 1 R 59 0"]
def rows14 : List RawRow := [⟨56,0,0,.left,6,0⟩,⟨56,1,0,.right,56,0⟩,⟨57,0,1,.right,67,0⟩,⟨57,1,0,.right,46,0⟩,⟨58,0,0,.right,46,0⟩,⟨58,1,1,.right,57,0⟩,⟨59,0,0,.right,60,0⟩,⟨59,1,1,.right,59,0⟩]
def data14 : List DataRow := [(false,false,6,false),(false,true,56,false),(true,true,67,false),(false,true,46,false),(false,true,46,false),(true,true,57,false),(false,true,60,false),(true,true,59,false)]
theorem parsed14 : lines14.mapM (fun s => parseRow s.toList) = some rows14 := by decide
theorem mapped14 : rows14.map markedData = data14 := by decide
theorem clean14 : lines14.all clean = true := by decide

def lines15 : List String := ["60 0 0 L 61 0","60 1 1 R 59 0","61 0 1 L 62 0","61 1 1 L 61 0","62 0 0 L 58 0","62 1 0 L 61 0","63 0 0 R 64 0","63 1 1 R 63 0"]
def rows15 : List RawRow := [⟨60,0,0,.left,61,0⟩,⟨60,1,1,.right,59,0⟩,⟨61,0,1,.left,62,0⟩,⟨61,1,1,.left,61,0⟩,⟨62,0,0,.left,58,0⟩,⟨62,1,0,.left,61,0⟩,⟨63,0,0,.right,64,0⟩,⟨63,1,1,.right,63,0⟩]
def data15 : List DataRow := [(false,false,61,false),(true,true,59,false),(true,false,62,false),(true,false,61,false),(false,false,58,false),(false,false,61,false),(false,true,64,false),(true,true,63,false)]
theorem parsed15 : lines15.mapM (fun s => parseRow s.toList) = some rows15 := by decide
theorem mapped15 : rows15.map markedData = data15 := by decide
theorem clean15 : lines15.all clean = true := by decide

def lines16 : List String := ["64 0 0 L 65 0","64 1 1 R 63 0","65 0 1 L 66 0","65 1 1 L 65 0","66 0 0 L 53 0","66 1 0 L 65 0","67 0 0 L 57 0","67 1 0 R 69 0"]
def rows16 : List RawRow := [⟨64,0,0,.left,65,0⟩,⟨64,1,1,.right,63,0⟩,⟨65,0,1,.left,66,0⟩,⟨65,1,1,.left,65,0⟩,⟨66,0,0,.left,53,0⟩,⟨66,1,0,.left,65,0⟩,⟨67,0,0,.left,57,0⟩,⟨67,1,0,.right,69,0⟩]
def data16 : List DataRow := [(false,false,65,false),(true,true,63,false),(true,false,66,false),(true,false,65,false),(false,false,53,false),(false,false,65,false),(false,false,57,false),(false,true,69,false)]
theorem parsed16 : lines16.mapM (fun s => parseRow s.toList) = some rows16 := by decide
theorem mapped16 : rows16.map markedData = data16 := by decide
theorem clean16 : lines16.all clean = true := by decide

def lines17 : List String := ["68 0 0 L 53 0","68 1 1 R 67 0","69 0 0 R 64 0","69 1 0 R 59 0","70 0 0 R 9 0","70 1 1 R 70 0","71 0 0 R 70 0","71 1 1 R 71 0"]
def rows17 : List RawRow := [⟨68,0,0,.left,53,0⟩,⟨68,1,1,.right,67,0⟩,⟨69,0,0,.right,64,0⟩,⟨69,1,0,.right,59,0⟩,⟨70,0,0,.right,9,0⟩,⟨70,1,1,.right,70,0⟩,⟨71,0,0,.right,70,0⟩,⟨71,1,1,.right,71,0⟩]
def data17 : List DataRow := [(false,false,53,false),(true,true,67,false),(false,true,64,false),(false,true,59,false),(false,true,9,false),(true,true,70,false),(false,true,70,false),(true,true,71,false)]
theorem parsed17 : lines17.mapM (fun s => parseRow s.toList) = some rows17 := by decide
theorem mapped17 : rows17.map markedData = data17 := by decide
theorem clean17 : lines17.all clean = true := by decide

def lines18 : List String := ["72 0 0 R 71 0","72 1 1 R 72 0","73 0 0 R 72 0","73 1 1 R 73 0","74 0 0 R 73 0","74 1 1 R 74 0","75 0 1 R 9 0","75 1 0 R 15 0"]
def rows18 : List RawRow := [⟨72,0,0,.right,71,0⟩,⟨72,1,1,.right,72,0⟩,⟨73,0,0,.right,72,0⟩,⟨73,1,1,.right,73,0⟩,⟨74,0,0,.right,73,0⟩,⟨74,1,1,.right,74,0⟩,⟨75,0,1,.right,9,0⟩,⟨75,1,0,.right,15,0⟩]
def data18 : List DataRow := [(false,true,71,false),(true,true,72,false),(false,true,72,false),(true,true,73,false),(false,true,73,false),(true,true,74,false),(true,true,9,false),(false,true,15,false)]
theorem parsed18 : lines18.mapM (fun s => parseRow s.toList) = some rows18 := by decide
theorem mapped18 : rows18.map markedData = data18 := by decide
theorem clean18 : lines18.all clean = true := by decide

def lines19 : List String := ["76 0 1 R 9 0","76 1 0 R 16 0","77 0 1 R 9 0","77 1 0 R 17 0","78 0 1 R 9 0","78 1 0 R 18 0","79 0 1 R 9 0","79 1 0 R 19 0"]
def rows19 : List RawRow := [⟨76,0,1,.right,9,0⟩,⟨76,1,0,.right,16,0⟩,⟨77,0,1,.right,9,0⟩,⟨77,1,0,.right,17,0⟩,⟨78,0,1,.right,9,0⟩,⟨78,1,0,.right,18,0⟩,⟨79,0,1,.right,9,0⟩,⟨79,1,0,.right,19,0⟩]
def data19 : List DataRow := [(true,true,9,false),(false,true,16,false),(true,true,9,false),(false,true,17,false),(true,true,9,false),(false,true,18,false),(true,true,9,false),(false,true,19,false)]
theorem parsed19 : lines19.mapM (fun s => parseRow s.toList) = some rows19 := by decide
theorem mapped19 : rows19.map markedData = data19 := by decide
theorem clean19 : lines19.all clean = true := by decide

def lines20 : List String := ["80 0 1 R 9 0","80 1 0 R 20 0","81 0 1 R 9 0","81 1 0 R 21 0","82 0 1 R 9 0","82 1 0 R 22 0","83 0 1 R 9 0","83 1 0 R 23 0"]
def rows20 : List RawRow := [⟨80,0,1,.right,9,0⟩,⟨80,1,0,.right,20,0⟩,⟨81,0,1,.right,9,0⟩,⟨81,1,0,.right,21,0⟩,⟨82,0,1,.right,9,0⟩,⟨82,1,0,.right,22,0⟩,⟨83,0,1,.right,9,0⟩,⟨83,1,0,.right,23,0⟩]
def data20 : List DataRow := [(true,true,9,false),(false,true,20,false),(true,true,9,false),(false,true,21,false),(true,true,9,false),(false,true,22,false),(true,true,9,false),(false,true,23,false)]
theorem parsed20 : lines20.mapM (fun s => parseRow s.toList) = some rows20 := by decide
theorem mapped20 : rows20.map markedData = data20 := by decide
theorem clean20 : lines20.all clean = true := by decide

def lines21 : List String := ["84 0 1 R 9 0","84 1 0 R 24 0","85 0 1 R 9 0","85 1 0 R 25 0","86 0 1 R 9 0","86 1 0 R 26 0","87 0 1 R 9 0","87 1 0 R 27 0"]
def rows21 : List RawRow := [⟨84,0,1,.right,9,0⟩,⟨84,1,0,.right,24,0⟩,⟨85,0,1,.right,9,0⟩,⟨85,1,0,.right,25,0⟩,⟨86,0,1,.right,9,0⟩,⟨86,1,0,.right,26,0⟩,⟨87,0,1,.right,9,0⟩,⟨87,1,0,.right,27,0⟩]
def data21 : List DataRow := [(true,true,9,false),(false,true,24,false),(true,true,9,false),(false,true,25,false),(true,true,9,false),(false,true,26,false),(true,true,9,false),(false,true,27,false)]
theorem parsed21 : lines21.mapM (fun s => parseRow s.toList) = some rows21 := by decide
theorem mapped21 : rows21.map markedData = data21 := by decide
theorem clean21 : lines21.all clean = true := by decide

def lines22 : List String := ["88 0 1 R 9 0","88 1 0 R 28 0","89 0 1 R 9 0","89 1 0 R 29 0","90 0 1 R 9 0","90 1 0 R 30 0","91 0 1 R 9 0","91 1 0 R 31 0"]
def rows22 : List RawRow := [⟨88,0,1,.right,9,0⟩,⟨88,1,0,.right,28,0⟩,⟨89,0,1,.right,9,0⟩,⟨89,1,0,.right,29,0⟩,⟨90,0,1,.right,9,0⟩,⟨90,1,0,.right,30,0⟩,⟨91,0,1,.right,9,0⟩,⟨91,1,0,.right,31,0⟩]
def data22 : List DataRow := [(true,true,9,false),(false,true,28,false),(true,true,9,false),(false,true,29,false),(true,true,9,false),(false,true,30,false),(true,true,9,false),(false,true,31,false)]
theorem parsed22 : lines22.mapM (fun s => parseRow s.toList) = some rows22 := by decide
theorem mapped22 : rows22.map markedData = data22 := by decide
theorem clean22 : lines22.all clean = true := by decide

def lines23 : List String := ["92 0 1 R 9 0","92 1 0 R 32 0","93 0 1 R 9 0","93 1 0 R 33 0","94 0 1 R 9 0","94 1 0 R 34 0","95 0 1 R 9 0","95 1 0 R 35 0"]
def rows23 : List RawRow := [⟨92,0,1,.right,9,0⟩,⟨92,1,0,.right,32,0⟩,⟨93,0,1,.right,9,0⟩,⟨93,1,0,.right,33,0⟩,⟨94,0,1,.right,9,0⟩,⟨94,1,0,.right,34,0⟩,⟨95,0,1,.right,9,0⟩,⟨95,1,0,.right,35,0⟩]
def data23 : List DataRow := [(true,true,9,false),(false,true,32,false),(true,true,9,false),(false,true,33,false),(true,true,9,false),(false,true,34,false),(true,true,9,false),(false,true,35,false)]
theorem parsed23 : lines23.mapM (fun s => parseRow s.toList) = some rows23 := by decide
theorem mapped23 : rows23.map markedData = data23 := by decide
theorem clean23 : lines23.all clean = true := by decide

def lines24 : List String := ["96 0 1 R 9 0","96 1 0 R 36 0","97 0 1 R 9 0","97 1 0 R 37 0","98 0 1 R 9 0","98 1 0 R 38 0","99 0 1 R 9 0","99 1 0 R 39 0"]
def rows24 : List RawRow := [⟨96,0,1,.right,9,0⟩,⟨96,1,0,.right,36,0⟩,⟨97,0,1,.right,9,0⟩,⟨97,1,0,.right,37,0⟩,⟨98,0,1,.right,9,0⟩,⟨98,1,0,.right,38,0⟩,⟨99,0,1,.right,9,0⟩,⟨99,1,0,.right,39,0⟩]
def data24 : List DataRow := [(true,true,9,false),(false,true,36,false),(true,true,9,false),(false,true,37,false),(true,true,9,false),(false,true,38,false),(true,true,9,false),(false,true,39,false)]
theorem parsed24 : lines24.mapM (fun s => parseRow s.toList) = some rows24 := by decide
theorem mapped24 : rows24.map markedData = data24 := by decide
theorem clean24 : lines24.all clean = true := by decide

def lines25 : List String := ["100 0 1 R 9 0","100 1 0 R 40 0","101 0 1 R 9 0","101 1 0 R 41 0","102 0 1 R 9 0","102 1 0 R 42 0","103 0 1 R 9 0","103 1 0 R 43 0"]
def rows25 : List RawRow := [⟨100,0,1,.right,9,0⟩,⟨100,1,0,.right,40,0⟩,⟨101,0,1,.right,9,0⟩,⟨101,1,0,.right,41,0⟩,⟨102,0,1,.right,9,0⟩,⟨102,1,0,.right,42,0⟩,⟨103,0,1,.right,9,0⟩,⟨103,1,0,.right,43,0⟩]
def data25 : List DataRow := [(true,true,9,false),(false,true,40,false),(true,true,9,false),(false,true,41,false),(true,true,9,false),(false,true,42,false),(true,true,9,false),(false,true,43,false)]
theorem parsed25 : lines25.mapM (fun s => parseRow s.toList) = some rows25 := by decide
theorem mapped25 : rows25.map markedData = data25 := by decide
theorem clean25 : lines25.all clean = true := by decide

def lines26 : List String := ["104 0 1 R 9 0","104 1 0 R 44 0","105 0 1 R 9 0","105 1 0 R 71 0","106 0 1 R 9 0","106 1 0 R 72 0","107 0 1 R 9 0","107 1 0 R 73 0"]
def rows26 : List RawRow := [⟨104,0,1,.right,9,0⟩,⟨104,1,0,.right,44,0⟩,⟨105,0,1,.right,9,0⟩,⟨105,1,0,.right,71,0⟩,⟨106,0,1,.right,9,0⟩,⟨106,1,0,.right,72,0⟩,⟨107,0,1,.right,9,0⟩,⟨107,1,0,.right,73,0⟩]
def data26 : List DataRow := [(true,true,9,false),(false,true,44,false),(true,true,9,false),(false,true,71,false),(true,true,9,false),(false,true,72,false),(true,true,9,false),(false,true,73,false)]
theorem parsed26 : lines26.mapM (fun s => parseRow s.toList) = some rows26 := by decide
theorem mapped26 : rows26.map markedData = data26 := by decide
theorem clean26 : lines26.all clean = true := by decide

def lines27 : List String := ["108 0 1 R 9 0","108 1 0 R 74 0","109 0 0 R 109 0","109 1 1 R 115 0","110 0 0 L 111 0","110 1 1 L 110 0","111 0 0 L 112 0","111 1 1 L 110 0"]
def rows27 : List RawRow := [⟨108,0,1,.right,9,0⟩,⟨108,1,0,.right,74,0⟩,⟨109,0,0,.right,109,0⟩,⟨109,1,1,.right,115,0⟩,⟨110,0,0,.left,111,0⟩,⟨110,1,1,.left,110,0⟩,⟨111,0,0,.left,112,0⟩,⟨111,1,1,.left,110,0⟩]
def data27 : List DataRow := [(true,true,9,false),(false,true,74,false),(false,true,109,false),(true,true,115,false),(false,false,111,false),(true,false,110,false),(false,false,112,false),(true,false,110,false)]
theorem parsed27 : lines27.mapM (fun s => parseRow s.toList) = some rows27 := by decide
theorem mapped27 : rows27.map markedData = data27 := by decide
theorem clean27 : lines27.all clean = true := by decide

def lines28 : List String := ["112 0 0 L 113 0","112 1 1 L 110 0","113 0 0 L 114 0","113 1 1 L 110 0","114 0 0 L 109 0","114 1 1 L 110 0","115 0 0 R 6 0","115 1 1 R 116 0"]
def rows28 : List RawRow := [⟨112,0,0,.left,113,0⟩,⟨112,1,1,.left,110,0⟩,⟨113,0,0,.left,114,0⟩,⟨113,1,1,.left,110,0⟩,⟨114,0,0,.left,109,0⟩,⟨114,1,1,.left,110,0⟩,⟨115,0,0,.right,6,0⟩,⟨115,1,1,.right,116,0⟩]
def data28 : List DataRow := [(false,false,113,false),(true,false,110,false),(false,false,114,false),(true,false,110,false),(false,false,109,false),(true,false,110,false),(false,true,6,false),(true,true,116,false)]
theorem parsed28 : lines28.mapM (fun s => parseRow s.toList) = some rows28 := by decide
theorem mapped28 : rows28.map markedData = data28 := by decide
theorem clean28 : lines28.all clean = true := by decide

def lines29 : List String := ["116 0 0 R 284 0","116 1 0 R 284 0","117 0 0 L 1 0","117 1 0 L 117 0","118 0 0 L 117 0","118 1 0 L 118 0","119 0 0 L 119 0","119 1 1 L 110 0"]
def rows29 : List RawRow := [⟨116,0,0,.right,284,0⟩,⟨116,1,0,.right,284,0⟩,⟨117,0,0,.left,1,0⟩,⟨117,1,0,.left,117,0⟩,⟨118,0,0,.left,117,0⟩,⟨118,1,0,.left,118,0⟩,⟨119,0,0,.left,119,0⟩,⟨119,1,1,.left,110,0⟩]
def data29 : List DataRow := [(false,true,284,false),(false,true,284,false),(false,false,1,false),(false,false,117,false),(false,false,117,false),(false,false,118,false),(false,false,119,false),(true,false,110,false)]
theorem parsed29 : lines29.mapM (fun s => parseRow s.toList) = some rows29 := by decide
theorem mapped29 : rows29.map markedData = data29 := by decide
theorem clean29 : lines29.all clean = true := by decide

def lines30 : List String := ["120 0 0 L 120 0","120 1 0 L 119 0","121 0 1 R 9 0","121 1 0 L 1 1","122 0 0 R 99 0","122 1 0 L 119 0","123 0 0 R 101 0","123 1 0 L 119 0"]
def rows30 : List RawRow := [⟨120,0,0,.left,120,0⟩,⟨120,1,0,.left,119,0⟩,⟨121,0,1,.right,9,0⟩,⟨121,1,0,.left,1,1⟩,⟨122,0,0,.right,99,0⟩,⟨122,1,0,.left,119,0⟩,⟨123,0,0,.right,101,0⟩,⟨123,1,0,.left,119,0⟩]
def data30 : List DataRow := [(false,false,120,false),(false,false,119,false),(true,true,9,false),(false,false,1,true),(false,true,99,false),(false,false,119,false),(false,true,101,false),(false,false,119,false)]
theorem parsed30 : lines30.mapM (fun s => parseRow s.toList) = some rows30 := by decide
theorem mapped30 : rows30.map markedData = data30 := by decide
theorem clean30 : lines30.all clean = true := by decide

def lines31 : List String := ["124 0 0 R 86 0","124 1 0 L 120 0","125 0 0 R 283 0","125 1 1 R 262 0","126 0 0 R 89 0","126 1 0 L 1 0","127 0 0 R 125 0","127 1 1 R 125 0"]
def rows31 : List RawRow := [⟨124,0,0,.right,86,0⟩,⟨124,1,0,.left,120,0⟩,⟨125,0,0,.right,283,0⟩,⟨125,1,1,.right,262,0⟩,⟨126,0,0,.right,89,0⟩,⟨126,1,0,.left,1,0⟩,⟨127,0,0,.right,125,0⟩,⟨127,1,1,.right,125,0⟩]
def data31 : List DataRow := [(false,true,86,false),(false,false,120,false),(false,true,283,false),(true,true,262,false),(false,true,89,false),(false,false,1,false),(false,true,125,false),(true,true,125,false)]
theorem parsed31 : lines31.mapM (fun s => parseRow s.toList) = some rows31 := by decide
theorem mapped31 : rows31.map markedData = data31 := by decide
theorem clean31 : lines31.all clean = true := by decide

def lines32 : List String := ["128 0 0 R 86 0","128 1 1 R 127 0","129 0 0 R 128 0","129 1 0 L 120 0","130 0 0 R 103 0","130 1 1 R 129 0","131 0 0 R 85 0","131 1 1 R 206 0"]
def rows32 : List RawRow := [⟨128,0,0,.right,86,0⟩,⟨128,1,1,.right,127,0⟩,⟨129,0,0,.right,128,0⟩,⟨129,1,0,.left,120,0⟩,⟨130,0,0,.right,103,0⟩,⟨130,1,1,.right,129,0⟩,⟨131,0,0,.right,85,0⟩,⟨131,1,1,.right,206,0⟩]
def data32 : List DataRow := [(false,true,86,false),(true,true,127,false),(false,true,128,false),(false,false,120,false),(false,true,103,false),(true,true,129,false),(false,true,85,false),(true,true,206,false)]
theorem parsed32 : lines32.mapM (fun s => parseRow s.toList) = some rows32 := by decide
theorem mapped32 : rows32.map markedData = data32 := by decide
theorem clean32 : lines32.all clean = true := by decide

def lines33 : List String := ["132 0 0 R 95 0","132 1 1 R 229 0","133 0 0 R 96 0","133 1 0 L 120 0","134 0 0 R 93 0","134 1 1 R 133 0","135 0 0 R 87 0","135 1 1 R 124 0"]
def rows33 : List RawRow := [⟨132,0,0,.right,95,0⟩,⟨132,1,1,.right,229,0⟩,⟨133,0,0,.right,96,0⟩,⟨133,1,0,.left,120,0⟩,⟨134,0,0,.right,93,0⟩,⟨134,1,1,.right,133,0⟩,⟨135,0,0,.right,87,0⟩,⟨135,1,1,.right,124,0⟩]
def data33 : List DataRow := [(false,true,95,false),(true,true,229,false),(false,true,96,false),(false,false,120,false),(false,true,93,false),(true,true,133,false),(false,true,87,false),(true,true,124,false)]
theorem parsed33 : lines33.mapM (fun s => parseRow s.toList) = some rows33 := by decide
theorem mapped33 : rows33.map markedData = data33 := by decide
theorem clean33 : lines33.all clean = true := by decide

def lines34 : List String := ["136 0 0 R 132 0","136 1 1 R 134 0","137 0 0 R 79 0","137 1 0 L 117 0","138 0 0 R 137 0","138 1 1 R 80 0","139 0 0 R 138 0","139 1 0 L 117 0"]
def rows34 : List RawRow := [⟨136,0,0,.right,132,0⟩,⟨136,1,1,.right,134,0⟩,⟨137,0,0,.right,79,0⟩,⟨137,1,0,.left,117,0⟩,⟨138,0,0,.right,137,0⟩,⟨138,1,1,.right,80,0⟩,⟨139,0,0,.right,138,0⟩,⟨139,1,0,.left,117,0⟩]
def data34 : List DataRow := [(false,true,132,false),(true,true,134,false),(false,true,79,false),(false,false,117,false),(false,true,137,false),(true,true,80,false),(false,true,138,false),(false,false,117,false)]
theorem parsed34 : lines34.mapM (fun s => parseRow s.toList) = some rows34 := by decide
theorem mapped34 : rows34.map markedData = data34 := by decide
theorem clean34 : lines34.all clean = true := by decide

def lines35 : List String := ["140 0 0 R 246 0","140 1 1 R 139 0","141 0 0 R 136 0","141 1 1 R 140 0","142 0 0 R 141 0","142 1 0 L 120 0","143 0 0 R 83 0","143 1 1 R 142 0"]
def rows35 : List RawRow := [⟨140,0,0,.right,246,0⟩,⟨140,1,1,.right,139,0⟩,⟨141,0,0,.right,136,0⟩,⟨141,1,1,.right,140,0⟩,⟨142,0,0,.right,141,0⟩,⟨142,1,0,.left,120,0⟩,⟨143,0,0,.right,83,0⟩,⟨143,1,1,.right,142,0⟩]
def data35 : List DataRow := [(false,true,246,false),(true,true,139,false),(false,true,136,false),(true,true,140,false),(false,true,141,false),(false,false,120,false),(false,true,83,false),(true,true,142,false)]
theorem parsed35 : lines35.mapM (fun s => parseRow s.toList) = some rows35 := by decide
theorem mapped35 : rows35.map markedData = data35 := by decide
theorem clean35 : lines35.all clean = true := by decide

def lines36 : List String := ["144 0 0 R 80 0","144 1 0 L 118 0","145 0 0 R 79 0","145 1 1 R 144 0","146 0 0 R 81 0","146 1 0 L 119 0","147 0 0 R 103 0","147 1 0 L 117 0"]
def rows36 : List RawRow := [⟨144,0,0,.right,80,0⟩,⟨144,1,0,.left,118,0⟩,⟨145,0,0,.right,79,0⟩,⟨145,1,1,.right,144,0⟩,⟨146,0,0,.right,81,0⟩,⟨146,1,0,.left,119,0⟩,⟨147,0,0,.right,103,0⟩,⟨147,1,0,.left,117,0⟩]
def data36 : List DataRow := [(false,true,80,false),(false,false,118,false),(false,true,79,false),(true,true,144,false),(false,true,81,false),(false,false,119,false),(false,true,103,false),(false,false,117,false)]
theorem parsed36 : lines36.mapM (fun s => parseRow s.toList) = some rows36 := by decide
theorem mapped36 : rows36.map markedData = data36 := by decide
theorem clean36 : lines36.all clean = true := by decide

def lines37 : List String := ["148 0 0 R 101 0","148 1 1 R 222 0","149 0 0 R 87 0","149 1 1 R 251 0","150 0 0 R 87 0","150 1 1 R 206 0","151 0 0 R 103 0","151 1 0 L 1 0"]
def rows37 : List RawRow := [⟨148,0,0,.right,101,0⟩,⟨148,1,1,.right,222,0⟩,⟨149,0,0,.right,87,0⟩,⟨149,1,1,.right,251,0⟩,⟨150,0,0,.right,87,0⟩,⟨150,1,1,.right,206,0⟩,⟨151,0,0,.right,103,0⟩,⟨151,1,0,.left,1,0⟩]
def data37 : List DataRow := [(false,true,101,false),(true,true,222,false),(false,true,87,false),(true,true,251,false),(false,true,87,false),(true,true,206,false),(false,true,103,false),(false,false,1,false)]
theorem parsed37 : lines37.mapM (fun s => parseRow s.toList) = some rows37 := by decide
theorem mapped37 : rows37.map markedData = data37 := by decide
theorem clean37 : lines37.all clean = true := by decide

def lines38 : List String := ["152 0 0 R 150 0","152 1 1 R 151 0","153 0 0 R 273 0","153 1 1 R 152 0","154 0 0 R 100 0","154 1 1 R 153 0","155 0 0 R 149 0","155 1 1 R 154 0"]
def rows38 : List RawRow := [⟨152,0,0,.right,150,0⟩,⟨152,1,1,.right,151,0⟩,⟨153,0,0,.right,273,0⟩,⟨153,1,1,.right,152,0⟩,⟨154,0,0,.right,100,0⟩,⟨154,1,1,.right,153,0⟩,⟨155,0,0,.right,149,0⟩,⟨155,1,1,.right,154,0⟩]
def data38 : List DataRow := [(false,true,150,false),(true,true,151,false),(false,true,273,false),(true,true,152,false),(false,true,100,false),(true,true,153,false),(false,true,149,false),(true,true,154,false)]
theorem parsed38 : lines38.mapM (fun s => parseRow s.toList) = some rows38 := by decide
theorem mapped38 : rows38.map markedData = data38 := by decide
theorem clean38 : lines38.all clean = true := by decide

def lines39 : List String := ["156 0 0 R 148 0","156 1 1 R 155 0","157 0 0 R 89 0","157 1 0 L 119 0","158 0 0 R 147 0","158 1 1 R 156 0","159 0 0 R 145 0","159 1 1 R 158 0"]
def rows39 : List RawRow := [⟨156,0,0,.right,148,0⟩,⟨156,1,1,.right,155,0⟩,⟨157,0,0,.right,89,0⟩,⟨157,1,0,.left,119,0⟩,⟨158,0,0,.right,147,0⟩,⟨158,1,1,.right,156,0⟩,⟨159,0,0,.right,145,0⟩,⟨159,1,1,.right,158,0⟩]
def data39 : List DataRow := [(false,true,148,false),(true,true,155,false),(false,true,89,false),(false,false,119,false),(false,true,147,false),(true,true,156,false),(false,true,145,false),(true,true,158,false)]
theorem parsed39 : lines39.mapM (fun s => parseRow s.toList) = some rows39 := by decide
theorem mapped39 : rows39.map markedData = data39 := by decide
theorem clean39 : lines39.all clean = true := by decide

def lines40 : List String := ["160 0 0 R 143 0","160 1 1 R 159 0","161 0 0 R 235 0","161 1 1 R 160 0","162 0 0 R 131 0","162 1 1 R 161 0","163 0 0 R 130 0","163 1 1 R 162 0"]
def rows40 : List RawRow := [⟨160,0,0,.right,143,0⟩,⟨160,1,1,.right,159,0⟩,⟨161,0,0,.right,235,0⟩,⟨161,1,1,.right,160,0⟩,⟨162,0,0,.right,131,0⟩,⟨162,1,1,.right,161,0⟩,⟨163,0,0,.right,130,0⟩,⟨163,1,1,.right,162,0⟩]
def data40 : List DataRow := [(false,true,143,false),(true,true,159,false),(false,true,235,false),(true,true,160,false),(false,true,131,false),(true,true,161,false),(false,true,130,false),(true,true,162,false)]
theorem parsed40 : lines40.mapM (fun s => parseRow s.toList) = some rows40 := by decide
theorem mapped40 : rows40.map markedData = data40 := by decide
theorem clean40 : lines40.all clean = true := by decide

def lines41 : List String := ["164 0 0 R 126 0","164 1 1 R 163 0","165 0 0 R 125 0","165 1 1 R 164 0","166 0 0 R 157 0","166 1 1 R 165 0","167 0 0 R 168 0","167 1 1 R 166 0"]
def rows41 : List RawRow := [⟨164,0,0,.right,126,0⟩,⟨164,1,1,.right,163,0⟩,⟨165,0,0,.right,125,0⟩,⟨165,1,1,.right,164,0⟩,⟨166,0,0,.right,157,0⟩,⟨166,1,1,.right,165,0⟩,⟨167,0,0,.right,168,0⟩,⟨167,1,1,.right,166,0⟩]
def data41 : List DataRow := [(false,true,126,false),(true,true,163,false),(false,true,125,false),(true,true,164,false),(false,true,157,false),(true,true,165,false),(false,true,168,false),(true,true,166,false)]
theorem parsed41 : lines41.mapM (fun s => parseRow s.toList) = some rows41 := by decide
theorem mapped41 : rows41.map markedData = data41 := by decide
theorem clean41 : lines41.all clean = true := by decide

def lines42 : List String := ["168 0 0 R 91 0","168 1 0 L 119 0","169 0 0 R 146 0","169 1 1 R 167 0","170 0 0 R 280 0","170 1 1 R 169 0","171 0 0 R 278 0","171 1 1 R 170 0"]
def rows42 : List RawRow := [⟨168,0,0,.right,91,0⟩,⟨168,1,0,.left,119,0⟩,⟨169,0,0,.right,146,0⟩,⟨169,1,1,.right,167,0⟩,⟨170,0,0,.right,280,0⟩,⟨170,1,1,.right,169,0⟩,⟨171,0,0,.right,278,0⟩,⟨171,1,1,.right,170,0⟩]
def data42 : List DataRow := [(false,true,91,false),(false,false,119,false),(false,true,146,false),(true,true,167,false),(false,true,280,false),(true,true,169,false),(false,true,278,false),(true,true,170,false)]
theorem parsed42 : lines42.mapM (fun s => parseRow s.toList) = some rows42 := by decide
theorem mapped42 : rows42.map markedData = data42 := by decide
theorem clean42 : lines42.all clean = true := by decide

def lines43 : List String := ["172 0 0 R 84 0","172 1 1 R 171 0","173 0 0 R 195 0","173 1 1 R 172 0","174 0 0 R 270 0","174 1 1 R 173 0","175 0 0 R 135 0","175 1 1 R 174 0"]
def rows43 : List RawRow := [⟨172,0,0,.right,84,0⟩,⟨172,1,1,.right,171,0⟩,⟨173,0,0,.right,195,0⟩,⟨173,1,1,.right,172,0⟩,⟨174,0,0,.right,270,0⟩,⟨174,1,1,.right,173,0⟩,⟨175,0,0,.right,135,0⟩,⟨175,1,1,.right,174,0⟩]
def data43 : List DataRow := [(false,true,84,false),(true,true,171,false),(false,true,195,false),(true,true,172,false),(false,true,270,false),(true,true,173,false),(false,true,135,false),(true,true,174,false)]
theorem parsed43 : lines43.mapM (fun s => parseRow s.toList) = some rows43 := by decide
theorem mapped43 : rows43.map markedData = data43 := by decide
theorem clean43 : lines43.all clean = true := by decide

def lines44 : List String := ["176 0 0 R 273 0","176 1 1 R 175 0","177 0 0 R 207 0","177 1 1 R 176 0","178 0 0 R 177 0","178 1 0 L 119 0","179 0 0 R 99 0","179 1 1 R 229 0"]
def rows44 : List RawRow := [⟨176,0,0,.right,273,0⟩,⟨176,1,1,.right,175,0⟩,⟨177,0,0,.right,207,0⟩,⟨177,1,1,.right,176,0⟩,⟨178,0,0,.right,177,0⟩,⟨178,1,0,.left,119,0⟩,⟨179,0,0,.right,99,0⟩,⟨179,1,1,.right,229,0⟩]
def data44 : List DataRow := [(false,true,273,false),(true,true,175,false),(false,true,207,false),(true,true,176,false),(false,true,177,false),(false,false,119,false),(false,true,99,false),(true,true,229,false)]
theorem parsed44 : lines44.mapM (fun s => parseRow s.toList) = some rows44 := by decide
theorem mapped44 : rows44.map markedData = data44 := by decide
theorem clean44 : lines44.all clean = true := by decide

def lines45 : List String := ["180 0 0 R 98 0","180 1 0 L 117 0","181 0 0 R 95 0","181 1 1 R 180 0","182 0 0 R 97 0","182 1 1 R 133 0","183 0 0 R 182 0","183 1 1 R 98 0"]
def rows45 : List RawRow := [⟨180,0,0,.right,98,0⟩,⟨180,1,0,.left,117,0⟩,⟨181,0,0,.right,95,0⟩,⟨181,1,1,.right,180,0⟩,⟨182,0,0,.right,97,0⟩,⟨182,1,1,.right,133,0⟩,⟨183,0,0,.right,182,0⟩,⟨183,1,1,.right,98,0⟩]
def data45 : List DataRow := [(false,true,98,false),(false,false,117,false),(false,true,95,false),(true,true,180,false),(false,true,97,false),(true,true,133,false),(false,true,182,false),(true,true,98,false)]
theorem parsed45 : lines45.mapM (fun s => parseRow s.toList) = some rows45 := by decide
theorem mapped45 : rows45.map markedData = data45 := by decide
theorem clean45 : lines45.all clean = true := by decide

def lines46 : List String := ["184 0 0 R 181 0","184 1 1 R 183 0","185 0 0 R 178 0","185 1 1 R 184 0","186 0 0 R 196 0","186 1 1 R 185 0","187 0 0 R 102 0","187 1 1 R 186 0"]
def rows46 : List RawRow := [⟨184,0,0,.right,181,0⟩,⟨184,1,1,.right,183,0⟩,⟨185,0,0,.right,178,0⟩,⟨185,1,1,.right,184,0⟩,⟨186,0,0,.right,196,0⟩,⟨186,1,1,.right,185,0⟩,⟨187,0,0,.right,102,0⟩,⟨187,1,1,.right,186,0⟩]
def data46 : List DataRow := [(false,true,181,false),(true,true,183,false),(false,true,178,false),(true,true,184,false),(false,true,196,false),(true,true,185,false),(false,true,102,false),(true,true,186,false)]
theorem parsed46 : lines46.mapM (fun s => parseRow s.toList) = some rows46 := by decide
theorem mapped46 : rows46.map markedData = data46 := by decide
theorem clean46 : lines46.all clean = true := by decide

def lines47 : List String := ["188 0 0 R 123 0","188 1 1 R 187 0","189 0 0 R 122 0","189 1 1 R 188 0","190 0 0 R 100 0","190 1 0 L 120 0","191 0 0 R 121 0","191 1 1 R 189 0"]
def rows47 : List RawRow := [⟨188,0,0,.right,123,0⟩,⟨188,1,1,.right,187,0⟩,⟨189,0,0,.right,122,0⟩,⟨189,1,1,.right,188,0⟩,⟨190,0,0,.right,100,0⟩,⟨190,1,0,.left,120,0⟩,⟨191,0,0,.right,121,0⟩,⟨191,1,1,.right,189,0⟩]
def data47 : List DataRow := [(false,true,123,false),(true,true,187,false),(false,true,122,false),(true,true,188,false),(false,true,100,false),(false,false,120,false),(false,true,121,false),(true,true,189,false)]
theorem parsed47 : lines47.mapM (fun s => parseRow s.toList) = some rows47 := by decide
theorem mapped47 : rows47.map markedData = data47 := by decide
theorem clean47 : lines47.all clean = true := by decide

def lines48 : List String := ["192 0 0 R 191 0","192 1 0 L 119 0","193 0 0 R 93 0","193 1 1 R 190 0","194 0 0 R 179 0","194 1 1 R 193 0","195 0 0 R 83 0","195 1 0 L 119 0"]
def rows48 : List RawRow := [⟨192,0,0,.right,191,0⟩,⟨192,1,0,.left,119,0⟩,⟨193,0,0,.right,93,0⟩,⟨193,1,1,.right,190,0⟩,⟨194,0,0,.right,179,0⟩,⟨194,1,1,.right,193,0⟩,⟨195,0,0,.right,83,0⟩,⟨195,1,0,.left,119,0⟩]
def data48 : List DataRow := [(false,true,191,false),(false,false,119,false),(false,true,93,false),(true,true,190,false),(false,true,179,false),(true,true,193,false),(false,true,83,false),(false,false,119,false)]
theorem parsed48 : lines48.mapM (fun s => parseRow s.toList) = some rows48 := by decide
theorem mapped48 : rows48.map markedData = data48 := by decide
theorem clean48 : lines48.all clean = true := by decide

def lines49 : List String := ["196 0 0 R 103 0","196 1 0 L 119 0","197 0 0 R 84 0","197 1 0 L 120 0","198 0 0 R 87 0","198 1 1 R 197 0","199 0 0 R 85 0","199 1 1 R 229 0"]
def rows49 : List RawRow := [⟨196,0,0,.right,103,0⟩,⟨196,1,0,.left,119,0⟩,⟨197,0,0,.right,84,0⟩,⟨197,1,0,.left,120,0⟩,⟨198,0,0,.right,87,0⟩,⟨198,1,1,.right,197,0⟩,⟨199,0,0,.right,85,0⟩,⟨199,1,1,.right,229,0⟩]
def data49 : List DataRow := [(false,true,103,false),(false,false,119,false),(false,true,84,false),(false,false,120,false),(false,true,87,false),(true,true,197,false),(false,true,85,false),(true,true,229,false)]
theorem parsed49 : lines49.mapM (fun s => parseRow s.toList) = some rows49 := by decide
theorem mapped49 : rows49.map markedData = data49 := by decide
theorem clean49 : lines49.all clean = true := by decide

def lines50 : List String := ["200 0 0 R 93 0","200 1 1 R 124 0","201 0 0 R 75 0","201 1 0 L 119 0","202 0 0 R 76 0","202 1 0 L 120 0","203 0 0 R 87 0","203 1 1 R 202 0"]
def rows50 : List RawRow := [⟨200,0,0,.right,93,0⟩,⟨200,1,1,.right,124,0⟩,⟨201,0,0,.right,75,0⟩,⟨201,1,0,.left,119,0⟩,⟨202,0,0,.right,76,0⟩,⟨202,1,0,.left,120,0⟩,⟨203,0,0,.right,87,0⟩,⟨203,1,1,.right,202,0⟩]
def data50 : List DataRow := [(false,true,93,false),(true,true,124,false),(false,true,75,false),(false,false,119,false),(false,true,76,false),(false,false,120,false),(false,true,87,false),(true,true,202,false)]
theorem parsed50 : lines50.mapM (fun s => parseRow s.toList) = some rows50 := by decide
theorem mapped50 : rows50.map markedData = data50 := by decide
theorem clean50 : lines50.all clean = true := by decide

def lines51 : List String := ["204 0 0 R 105 0","204 1 1 R 92 0","205 0 0 R 103 0","205 1 1 R 229 0","206 0 0 R 104 0","206 1 0 L 120 0","207 0 0 R 79 0","207 1 0 L 119 0"]
def rows51 : List RawRow := [⟨204,0,0,.right,105,0⟩,⟨204,1,1,.right,92,0⟩,⟨205,0,0,.right,103,0⟩,⟨205,1,1,.right,229,0⟩,⟨206,0,0,.right,104,0⟩,⟨206,1,0,.left,120,0⟩,⟨207,0,0,.right,79,0⟩,⟨207,1,0,.left,119,0⟩]
def data51 : List DataRow := [(false,true,105,false),(true,true,92,false),(false,true,103,false),(true,true,229,false),(false,true,104,false),(false,false,120,false),(false,true,79,false),(false,false,119,false)]
theorem parsed51 : lines51.mapM (fun s => parseRow s.toList) = some rows51 := by decide
theorem mapped51 : rows51.map markedData = data51 := by decide
theorem clean51 : lines51.all clean = true := by decide

def lines52 : List String := ["208 0 0 R 93 0","208 1 1 R 206 0","209 0 0 R 205 0","209 1 1 R 208 0","210 0 0 R 77 0","210 1 0 L 119 0","211 0 0 R 78 0","211 1 0 L 120 0"]
def rows52 : List RawRow := [⟨208,0,0,.right,93,0⟩,⟨208,1,1,.right,206,0⟩,⟨209,0,0,.right,205,0⟩,⟨209,1,1,.right,208,0⟩,⟨210,0,0,.right,77,0⟩,⟨210,1,0,.left,119,0⟩,⟨211,0,0,.right,78,0⟩,⟨211,1,0,.left,120,0⟩]
def data52 : List DataRow := [(false,true,93,false),(true,true,206,false),(false,true,205,false),(true,true,208,false),(false,true,77,false),(false,false,119,false),(false,true,78,false),(false,false,120,false)]
theorem parsed52 : lines52.mapM (fun s => parseRow s.toList) = some rows52 := by decide
theorem mapped52 : rows52.map markedData = data52 := by decide
theorem clean52 : lines52.all clean = true := by decide

def lines53 : List String := ["212 0 0 R 87 0","212 1 1 R 211 0","213 0 0 R 210 0","213 1 1 R 212 0","214 0 0 R 106 0","214 1 0 L 119 0","215 0 0 R 214 0","215 1 0 L 120 0"]
def rows53 : List RawRow := [⟨212,0,0,.right,87,0⟩,⟨212,1,1,.right,211,0⟩,⟨213,0,0,.right,210,0⟩,⟨213,1,1,.right,212,0⟩,⟨214,0,0,.right,106,0⟩,⟨214,1,0,.left,119,0⟩,⟨215,0,0,.right,214,0⟩,⟨215,1,0,.left,120,0⟩]
def data53 : List DataRow := [(false,true,87,false),(true,true,211,false),(false,true,210,false),(true,true,212,false),(false,true,106,false),(false,false,119,false),(false,true,214,false),(false,false,120,false)]
theorem parsed53 : lines53.mapM (fun s => parseRow s.toList) = some rows53 := by decide
theorem mapped53 : rows53.map markedData = data53 := by decide
theorem clean53 : lines53.all clean = true := by decide

def lines54 : List String := ["216 0 0 R 91 0","216 1 1 R 215 0","217 0 0 R 92 0","217 1 0 L 120 0","218 0 0 R 88 0","218 1 1 R 94 0","219 0 0 R 106 0","219 1 1 R 217 0"]
def rows54 : List RawRow := [⟨216,0,0,.right,91,0⟩,⟨216,1,1,.right,215,0⟩,⟨217,0,0,.right,92,0⟩,⟨217,1,0,.left,120,0⟩,⟨218,0,0,.right,88,0⟩,⟨218,1,1,.right,94,0⟩,⟨219,0,0,.right,106,0⟩,⟨219,1,1,.right,217,0⟩]
def data54 : List DataRow := [(false,true,91,false),(true,true,215,false),(false,true,92,false),(false,false,120,false),(false,true,88,false),(true,true,94,false),(false,true,106,false),(true,true,217,false)]
theorem parsed54 : lines54.mapM (fun s => parseRow s.toList) = some rows54 := by decide
theorem mapped54 : rows54.map markedData = data54 := by decide
theorem clean54 : lines54.all clean = true := by decide

def lines55 : List String := ["220 0 0 R 108 0","220 1 1 R 88 0","221 0 0 R 88 0","221 1 1 R 88 0","222 0 0 R 221 0","222 1 0 L 120 0","223 0 0 R 89 0","223 1 1 R 222 0"]
def rows55 : List RawRow := [⟨220,0,0,.right,108,0⟩,⟨220,1,1,.right,88,0⟩,⟨221,0,0,.right,88,0⟩,⟨221,1,1,.right,88,0⟩,⟨222,0,0,.right,221,0⟩,⟨222,1,0,.left,120,0⟩,⟨223,0,0,.right,89,0⟩,⟨223,1,1,.right,222,0⟩]
def data55 : List DataRow := [(false,true,108,false),(true,true,88,false),(false,true,88,false),(true,true,88,false),(false,true,221,false),(false,false,120,false),(false,true,89,false),(true,true,222,false)]
theorem parsed55 : lines55.mapM (fun s => parseRow s.toList) = some rows55 := by decide
theorem mapped55 : rows55.map markedData = data55 := by decide
theorem clean55 : lines55.all clean = true := by decide

def lines56 : List String := ["224 0 0 R 90 0","224 1 0 L 120 0","225 0 0 R 81 0","225 1 1 R 224 0","226 0 0 R 225 0","226 1 0 L 117 0","227 0 0 R 223 0","227 1 1 R 226 0"]
def rows56 : List RawRow := [⟨224,0,0,.right,90,0⟩,⟨224,1,0,.left,120,0⟩,⟨225,0,0,.right,81,0⟩,⟨225,1,1,.right,224,0⟩,⟨226,0,0,.right,225,0⟩,⟨226,1,0,.left,117,0⟩,⟨227,0,0,.right,223,0⟩,⟨227,1,1,.right,226,0⟩]
def data56 : List DataRow := [(false,true,90,false),(false,false,120,false),(false,true,81,false),(true,true,224,false),(false,true,225,false),(false,false,117,false),(false,true,223,false),(true,true,226,false)]
theorem parsed56 : lines56.mapM (fun s => parseRow s.toList) = some rows56 := by decide
theorem mapped56 : rows56.map markedData = data56 := by decide
theorem clean56 : lines56.all clean = true := by decide

def lines57 : List String := ["228 0 0 R 108 0","228 1 1 R 227 0","229 0 0 R 218 0","229 1 0 L 120 0","230 0 0 R 81 0","230 1 1 R 222 0","231 0 0 R 228 0","231 1 1 R 230 0"]
def rows57 : List RawRow := [⟨228,0,0,.right,108,0⟩,⟨228,1,1,.right,227,0⟩,⟨229,0,0,.right,218,0⟩,⟨229,1,0,.left,120,0⟩,⟨230,0,0,.right,81,0⟩,⟨230,1,1,.right,222,0⟩,⟨231,0,0,.right,228,0⟩,⟨231,1,1,.right,230,0⟩]
def data57 : List DataRow := [(false,true,108,false),(true,true,227,false),(false,true,218,false),(false,false,120,false),(false,true,81,false),(true,true,222,false),(false,true,228,false),(true,true,230,false)]
theorem parsed57 : lines57.mapM (fun s => parseRow s.toList) = some rows57 := by decide
theorem mapped57 : rows57.map markedData = data57 := by decide
theorem clean57 : lines57.all clean = true := by decide

def lines58 : List String := ["232 0 0 R 82 0","232 1 0 L 120 0","233 0 0 R 87 0","233 1 1 R 232 0","234 0 0 R 92 0","234 1 1 R 92 0","235 0 0 R 107 0","235 1 1 R 234 0"]
def rows58 : List RawRow := [⟨232,0,0,.right,82,0⟩,⟨232,1,0,.left,120,0⟩,⟨233,0,0,.right,87,0⟩,⟨233,1,1,.right,232,0⟩,⟨234,0,0,.right,92,0⟩,⟨234,1,1,.right,92,0⟩,⟨235,0,0,.right,107,0⟩,⟨235,1,1,.right,234,0⟩]
def data58 : List DataRow := [(false,true,82,false),(false,false,120,false),(false,true,87,false),(true,true,232,false),(false,true,92,false),(true,true,92,false),(false,true,107,false),(true,true,234,false)]
theorem parsed58 : lines58.mapM (fun s => parseRow s.toList) = some rows58 := by decide
theorem mapped58 : rows58.map markedData = data58 := by decide
theorem clean58 : lines58.all clean = true := by decide

def lines59 : List String := ["236 0 0 R 235 0","236 1 0 L 118 0","237 0 0 R 91 0","237 1 1 R 236 0","238 0 0 R 107 0","238 1 0 L 1 0","239 0 0 R 237 0","239 1 1 R 238 0"]
def rows59 : List RawRow := [⟨236,0,0,.right,235,0⟩,⟨236,1,0,.left,118,0⟩,⟨237,0,0,.right,91,0⟩,⟨237,1,1,.right,236,0⟩,⟨238,0,0,.right,107,0⟩,⟨238,1,0,.left,1,0⟩,⟨239,0,0,.right,237,0⟩,⟨239,1,1,.right,238,0⟩]
def data59 : List DataRow := [(false,true,235,false),(false,false,118,false),(false,true,91,false),(true,true,236,false),(false,true,107,false),(false,false,1,false),(false,true,237,false),(true,true,238,false)]
theorem parsed59 : lines59.mapM (fun s => parseRow s.toList) = some rows59 := by decide
theorem mapped59 : rows59.map markedData = data59 := by decide
theorem clean59 : lines59.all clean = true := by decide

def lines60 : List String := ["240 0 0 R 101 0","240 1 1 R 229 0","241 0 0 R 233 0","241 1 1 R 239 0","242 0 0 R 231 0","242 1 1 R 241 0","243 0 0 R 220 0","243 1 1 R 242 0"]
def rows60 : List RawRow := [⟨240,0,0,.right,101,0⟩,⟨240,1,1,.right,229,0⟩,⟨241,0,0,.right,233,0⟩,⟨241,1,1,.right,239,0⟩,⟨242,0,0,.right,231,0⟩,⟨242,1,1,.right,241,0⟩,⟨243,0,0,.right,220,0⟩,⟨243,1,1,.right,242,0⟩]
def data60 : List DataRow := [(false,true,101,false),(true,true,229,false),(false,true,233,false),(true,true,239,false),(false,true,231,false),(true,true,241,false),(false,true,220,false),(true,true,242,false)]
theorem parsed60 : lines60.mapM (fun s => parseRow s.toList) = some rows60 := by decide
theorem mapped60 : rows60.map markedData = data60 := by decide
theorem clean60 : lines60.all clean = true := by decide

def lines61 : List String := ["244 0 0 R 219 0","244 1 1 R 243 0","245 0 0 R 216 0","245 1 1 R 244 0","246 0 0 R 213 0","246 1 1 R 245 0","247 0 0 R 85 0","247 1 0 L 119 0"]
def rows61 : List RawRow := [⟨244,0,0,.right,219,0⟩,⟨244,1,1,.right,243,0⟩,⟨245,0,0,.right,216,0⟩,⟨245,1,1,.right,244,0⟩,⟨246,0,0,.right,213,0⟩,⟨246,1,1,.right,245,0⟩,⟨247,0,0,.right,85,0⟩,⟨247,1,0,.left,119,0⟩]
def data61 : List DataRow := [(false,true,219,false),(true,true,243,false),(false,true,216,false),(true,true,244,false),(false,true,213,false),(true,true,245,false),(false,true,85,false),(false,false,119,false)]
theorem parsed61 : lines61.mapM (fun s => parseRow s.toList) = some rows61 := by decide
theorem mapped61 : rows61.map markedData = data61 := by decide
theorem clean61 : lines61.all clean = true := by decide

def lines62 : List String := ["248 0 0 R 247 0","248 1 0 L 117 0","249 0 0 R 80 0","249 1 1 R 248 0","250 0 0 R 207 0","250 1 1 R 249 0","251 0 0 R 102 0","251 1 0 L 120 0"]
def rows62 : List RawRow := [⟨248,0,0,.right,247,0⟩,⟨248,1,0,.left,117,0⟩,⟨249,0,0,.right,80,0⟩,⟨249,1,1,.right,248,0⟩,⟨250,0,0,.right,207,0⟩,⟨250,1,1,.right,249,0⟩,⟨251,0,0,.right,102,0⟩,⟨251,1,0,.left,120,0⟩]
def data62 : List DataRow := [(false,true,247,false),(false,false,117,false),(false,true,80,false),(true,true,248,false),(false,true,207,false),(true,true,249,false),(false,true,102,false),(false,false,120,false)]
theorem parsed62 : lines62.mapM (fun s => parseRow s.toList) = some rows62 := by decide
theorem mapped62 : rows62.map markedData = data62 := by decide
theorem clean62 : lines62.all clean = true := by decide

def lines63 : List String := ["252 0 0 R 246 0","252 1 1 R 250 0","253 0 0 R 209 0","253 1 1 R 252 0","254 0 0 R 273 0","254 1 1 R 253 0","255 0 0 R 204 0","255 1 1 R 254 0"]
def rows63 : List RawRow := [⟨252,0,0,.right,246,0⟩,⟨252,1,1,.right,250,0⟩,⟨253,0,0,.right,209,0⟩,⟨253,1,1,.right,252,0⟩,⟨254,0,0,.right,273,0⟩,⟨254,1,1,.right,253,0⟩,⟨255,0,0,.right,204,0⟩,⟨255,1,1,.right,254,0⟩]
def data63 : List DataRow := [(false,true,246,false),(true,true,250,false),(false,true,209,false),(true,true,252,false),(false,true,273,false),(true,true,253,false),(false,true,204,false),(true,true,254,false)]
theorem parsed63 : lines63.mapM (fun s => parseRow s.toList) = some rows63 := by decide
theorem mapped63 : rows63.map markedData = data63 := by decide
theorem clean63 : lines63.all clean = true := by decide

def lines64 : List String := ["256 0 0 R 255 0","256 1 0 L 120 0","257 0 0 R 83 0","257 1 1 R 256 0","258 0 0 R 203 0","258 1 1 R 257 0","259 0 0 R 201 0","259 1 1 R 258 0"]
def rows64 : List RawRow := [⟨256,0,0,.right,255,0⟩,⟨256,1,0,.left,120,0⟩,⟨257,0,0,.right,83,0⟩,⟨257,1,1,.right,256,0⟩,⟨258,0,0,.right,203,0⟩,⟨258,1,1,.right,257,0⟩,⟨259,0,0,.right,201,0⟩,⟨259,1,1,.right,258,0⟩]
def data64 : List DataRow := [(false,true,255,false),(false,false,120,false),(false,true,83,false),(true,true,256,false),(false,true,203,false),(true,true,257,false),(false,true,201,false),(true,true,258,false)]
theorem parsed64 : lines64.mapM (fun s => parseRow s.toList) = some rows64 := by decide
theorem mapped64 : rows64.map markedData = data64 := by decide
theorem clean64 : lines64.all clean = true := by decide

def lines65 : List String := ["260 0 0 R 200 0","260 1 1 R 259 0","261 0 0 R 199 0","261 1 1 R 260 0","262 0 0 R 93 0","262 1 1 R 251 0","263 0 0 R 198 0","263 1 1 R 261 0"]
def rows65 : List RawRow := [⟨260,0,0,.right,200,0⟩,⟨260,1,1,.right,259,0⟩,⟨261,0,0,.right,199,0⟩,⟨261,1,1,.right,260,0⟩,⟨262,0,0,.right,93,0⟩,⟨262,1,1,.right,251,0⟩,⟨263,0,0,.right,198,0⟩,⟨263,1,1,.right,261,0⟩]
def data65 : List DataRow := [(false,true,200,false),(true,true,259,false),(false,true,199,false),(true,true,260,false),(false,true,93,false),(true,true,251,false),(false,true,198,false),(true,true,261,false)]
theorem parsed65 : lines65.mapM (fun s => parseRow s.toList) = some rows65 := by decide
theorem mapped65 : rows65.map markedData = data65 := by decide
theorem clean65 : lines65.all clean = true := by decide

def lines66 : List String := ["264 0 0 R 195 0","264 1 1 R 263 0","265 0 0 R 194 0","265 1 1 R 264 0","266 0 0 R 168 0","266 1 1 R 265 0","267 0 0 R 157 0","267 1 1 R 266 0"]
def rows66 : List RawRow := [⟨264,0,0,.right,195,0⟩,⟨264,1,1,.right,263,0⟩,⟨265,0,0,.right,194,0⟩,⟨265,1,1,.right,264,0⟩,⟨266,0,0,.right,168,0⟩,⟨266,1,1,.right,265,0⟩,⟨267,0,0,.right,157,0⟩,⟨267,1,1,.right,266,0⟩]
def data66 : List DataRow := [(false,true,195,false),(true,true,263,false),(false,true,194,false),(true,true,264,false),(false,true,168,false),(true,true,265,false),(false,true,157,false),(true,true,266,false)]
theorem parsed66 : lines66.mapM (fun s => parseRow s.toList) = some rows66 := by decide
theorem mapped66 : rows66.map markedData = data66 := by decide
theorem clean66 : lines66.all clean = true := by decide

def lines67 : List String := ["268 0 0 R 146 0","268 1 1 R 267 0","269 0 0 R 268 0","269 1 0 L 120 0","270 0 0 R 85 0","270 1 1 R 269 0","271 0 0 R 194 0","271 1 1 R 221 0"]
def rows67 : List RawRow := [⟨268,0,0,.right,146,0⟩,⟨268,1,1,.right,267,0⟩,⟨269,0,0,.right,268,0⟩,⟨269,1,0,.left,120,0⟩,⟨270,0,0,.right,85,0⟩,⟨270,1,1,.right,269,0⟩,⟨271,0,0,.right,194,0⟩,⟨271,1,1,.right,221,0⟩]
def data67 : List DataRow := [(false,true,146,false),(true,true,267,false),(false,true,268,false),(false,false,120,false),(false,true,85,false),(true,true,269,false),(false,true,194,false),(true,true,221,false)]
theorem parsed67 : lines67.mapM (fun s => parseRow s.toList) = some rows67 := by decide
theorem mapped67 : rows67.map markedData = data67 := by decide
theorem clean67 : lines67.all clean = true := by decide

def lines68 : List String := ["272 0 0 R 271 0","272 1 0 L 120 0","273 0 0 R 240 0","273 1 1 R 262 0","274 0 0 R 83 0","274 1 1 R 272 0","275 0 0 R 274 0","275 1 1 R 198 0"]
def rows68 : List RawRow := [⟨272,0,0,.right,271,0⟩,⟨272,1,0,.left,120,0⟩,⟨273,0,0,.right,240,0⟩,⟨273,1,1,.right,262,0⟩,⟨274,0,0,.right,83,0⟩,⟨274,1,1,.right,272,0⟩,⟨275,0,0,.right,274,0⟩,⟨275,1,1,.right,198,0⟩]
def data68 : List DataRow := [(false,true,271,false),(false,false,120,false),(false,true,240,false),(true,true,262,false),(false,true,83,false),(true,true,272,false),(false,true,274,false),(true,true,198,false)]
theorem parsed68 : lines68.mapM (fun s => parseRow s.toList) = some rows68 := by decide
theorem mapped68 : rows68.map markedData = data68 := by decide
theorem clean68 : lines68.all clean = true := by decide

def lines69 : List String := ["276 0 0 R 86 0","276 1 1 R 275 0","277 0 0 R 276 0","277 1 0 L 120 0","278 0 0 R 97 0","278 1 1 R 277 0","279 0 0 R 98 0","279 1 0 L 120 0"]
def rows69 : List RawRow := [⟨276,0,0,.right,86,0⟩,⟨276,1,1,.right,275,0⟩,⟨277,0,0,.right,276,0⟩,⟨277,1,0,.left,120,0⟩,⟨278,0,0,.right,97,0⟩,⟨278,1,1,.right,277,0⟩,⟨279,0,0,.right,98,0⟩,⟨279,1,0,.left,120,0⟩]
def data69 : List DataRow := [(false,true,86,false),(true,true,275,false),(false,true,276,false),(false,false,120,false),(false,true,97,false),(true,true,277,false),(false,true,98,false),(false,false,120,false)]
theorem parsed69 : lines69.mapM (fun s => parseRow s.toList) = some rows69 := by decide
theorem mapped69 : rows69.map markedData = data69 := by decide
theorem clean69 : lines69.all clean = true := by decide

def lines70 : List String := ["280 0 0 R 85 0","280 1 1 R 279 0","281 0 0 R 90 0","281 1 1 R 94 0","282 0 0 R 281 0","282 1 0 L 120 0","283 0 0 R 101 0","283 1 1 R 282 0"]
def rows70 : List RawRow := [⟨280,0,0,.right,85,0⟩,⟨280,1,1,.right,279,0⟩,⟨281,0,0,.right,90,0⟩,⟨281,1,1,.right,94,0⟩,⟨282,0,0,.right,281,0⟩,⟨282,1,0,.left,120,0⟩,⟨283,0,0,.right,101,0⟩,⟨283,1,1,.right,282,0⟩]
def data70 : List DataRow := [(false,true,85,false),(true,true,279,false),(false,true,90,false),(true,true,94,false),(false,true,281,false),(false,false,120,false),(false,true,101,false),(true,true,282,false)]
theorem parsed70 : lines70.mapM (fun s => parseRow s.toList) = some rows70 := by decide
theorem mapped70 : rows70.map markedData = data70 := by decide
theorem clean70 : lines70.all clean = true := by decide

def lines71 : List String := ["284 0 0 R 98 0","284 1 1 R 192 0"]
def rows71 : List RawRow := [⟨284,0,0,.right,98,0⟩,⟨284,1,1,.right,192,0⟩]
def data71 : List DataRow := [(false,true,98,false),(true,true,192,false)]
theorem parsed71 : lines71.mapM (fun s => parseRow s.toList) = some rows71 := by decide
theorem mapped71 : rows71.map markedData = data71 := by decide
theorem clean71 : lines71.all clean = true := by decide

def linesFrom72 : List String := []
def rowsFrom72 : List RawRow := []
def dataFrom72 : List DataRow := []
theorem parsedFrom72 : linesFrom72.mapM (fun s => parseRow s.toList) = some rowsFrom72 := rfl
theorem mappedFrom72 : rowsFrom72.map markedData = dataFrom72 := rfl
theorem cleanFrom72 : linesFrom72.all clean = true := rfl

def linesFrom71 : List String := lines71 ++ linesFrom72
def rowsFrom71 : List RawRow := rows71 ++ rowsFrom72
def dataFrom71 : List DataRow := data71 ++ dataFrom72
theorem parsedFrom71 : linesFrom71.mapM (fun s => parseRow s.toList) = some rowsFrom71 :=
  parse_append _ _ _ _ parsed71 parsedFrom72
theorem mappedFrom71 : rowsFrom71.map markedData = dataFrom71 := by
  simp only [rowsFrom71, dataFrom71, List.map_append, mapped71, mappedFrom72]
theorem cleanFrom71 : linesFrom71.all clean = true := by
  simp only [linesFrom71, List.all_append, clean71, cleanFrom72, Bool.and_self]

def linesFrom70 : List String := lines70 ++ linesFrom71
def rowsFrom70 : List RawRow := rows70 ++ rowsFrom71
def dataFrom70 : List DataRow := data70 ++ dataFrom71
theorem parsedFrom70 : linesFrom70.mapM (fun s => parseRow s.toList) = some rowsFrom70 :=
  parse_append _ _ _ _ parsed70 parsedFrom71
theorem mappedFrom70 : rowsFrom70.map markedData = dataFrom70 := by
  simp only [rowsFrom70, dataFrom70, List.map_append, mapped70, mappedFrom71]
theorem cleanFrom70 : linesFrom70.all clean = true := by
  simp only [linesFrom70, List.all_append, clean70, cleanFrom71, Bool.and_self]

def linesFrom69 : List String := lines69 ++ linesFrom70
def rowsFrom69 : List RawRow := rows69 ++ rowsFrom70
def dataFrom69 : List DataRow := data69 ++ dataFrom70
theorem parsedFrom69 : linesFrom69.mapM (fun s => parseRow s.toList) = some rowsFrom69 :=
  parse_append _ _ _ _ parsed69 parsedFrom70
theorem mappedFrom69 : rowsFrom69.map markedData = dataFrom69 := by
  simp only [rowsFrom69, dataFrom69, List.map_append, mapped69, mappedFrom70]
theorem cleanFrom69 : linesFrom69.all clean = true := by
  simp only [linesFrom69, List.all_append, clean69, cleanFrom70, Bool.and_self]

def linesFrom68 : List String := lines68 ++ linesFrom69
def rowsFrom68 : List RawRow := rows68 ++ rowsFrom69
def dataFrom68 : List DataRow := data68 ++ dataFrom69
theorem parsedFrom68 : linesFrom68.mapM (fun s => parseRow s.toList) = some rowsFrom68 :=
  parse_append _ _ _ _ parsed68 parsedFrom69
theorem mappedFrom68 : rowsFrom68.map markedData = dataFrom68 := by
  simp only [rowsFrom68, dataFrom68, List.map_append, mapped68, mappedFrom69]
theorem cleanFrom68 : linesFrom68.all clean = true := by
  simp only [linesFrom68, List.all_append, clean68, cleanFrom69, Bool.and_self]

def linesFrom67 : List String := lines67 ++ linesFrom68
def rowsFrom67 : List RawRow := rows67 ++ rowsFrom68
def dataFrom67 : List DataRow := data67 ++ dataFrom68
theorem parsedFrom67 : linesFrom67.mapM (fun s => parseRow s.toList) = some rowsFrom67 :=
  parse_append _ _ _ _ parsed67 parsedFrom68
theorem mappedFrom67 : rowsFrom67.map markedData = dataFrom67 := by
  simp only [rowsFrom67, dataFrom67, List.map_append, mapped67, mappedFrom68]
theorem cleanFrom67 : linesFrom67.all clean = true := by
  simp only [linesFrom67, List.all_append, clean67, cleanFrom68, Bool.and_self]

def linesFrom66 : List String := lines66 ++ linesFrom67
def rowsFrom66 : List RawRow := rows66 ++ rowsFrom67
def dataFrom66 : List DataRow := data66 ++ dataFrom67
theorem parsedFrom66 : linesFrom66.mapM (fun s => parseRow s.toList) = some rowsFrom66 :=
  parse_append _ _ _ _ parsed66 parsedFrom67
theorem mappedFrom66 : rowsFrom66.map markedData = dataFrom66 := by
  simp only [rowsFrom66, dataFrom66, List.map_append, mapped66, mappedFrom67]
theorem cleanFrom66 : linesFrom66.all clean = true := by
  simp only [linesFrom66, List.all_append, clean66, cleanFrom67, Bool.and_self]

def linesFrom65 : List String := lines65 ++ linesFrom66
def rowsFrom65 : List RawRow := rows65 ++ rowsFrom66
def dataFrom65 : List DataRow := data65 ++ dataFrom66
theorem parsedFrom65 : linesFrom65.mapM (fun s => parseRow s.toList) = some rowsFrom65 :=
  parse_append _ _ _ _ parsed65 parsedFrom66
theorem mappedFrom65 : rowsFrom65.map markedData = dataFrom65 := by
  simp only [rowsFrom65, dataFrom65, List.map_append, mapped65, mappedFrom66]
theorem cleanFrom65 : linesFrom65.all clean = true := by
  simp only [linesFrom65, List.all_append, clean65, cleanFrom66, Bool.and_self]

def linesFrom64 : List String := lines64 ++ linesFrom65
def rowsFrom64 : List RawRow := rows64 ++ rowsFrom65
def dataFrom64 : List DataRow := data64 ++ dataFrom65
theorem parsedFrom64 : linesFrom64.mapM (fun s => parseRow s.toList) = some rowsFrom64 :=
  parse_append _ _ _ _ parsed64 parsedFrom65
theorem mappedFrom64 : rowsFrom64.map markedData = dataFrom64 := by
  simp only [rowsFrom64, dataFrom64, List.map_append, mapped64, mappedFrom65]
theorem cleanFrom64 : linesFrom64.all clean = true := by
  simp only [linesFrom64, List.all_append, clean64, cleanFrom65, Bool.and_self]

def linesFrom63 : List String := lines63 ++ linesFrom64
def rowsFrom63 : List RawRow := rows63 ++ rowsFrom64
def dataFrom63 : List DataRow := data63 ++ dataFrom64
theorem parsedFrom63 : linesFrom63.mapM (fun s => parseRow s.toList) = some rowsFrom63 :=
  parse_append _ _ _ _ parsed63 parsedFrom64
theorem mappedFrom63 : rowsFrom63.map markedData = dataFrom63 := by
  simp only [rowsFrom63, dataFrom63, List.map_append, mapped63, mappedFrom64]
theorem cleanFrom63 : linesFrom63.all clean = true := by
  simp only [linesFrom63, List.all_append, clean63, cleanFrom64, Bool.and_self]

def linesFrom62 : List String := lines62 ++ linesFrom63
def rowsFrom62 : List RawRow := rows62 ++ rowsFrom63
def dataFrom62 : List DataRow := data62 ++ dataFrom63
theorem parsedFrom62 : linesFrom62.mapM (fun s => parseRow s.toList) = some rowsFrom62 :=
  parse_append _ _ _ _ parsed62 parsedFrom63
theorem mappedFrom62 : rowsFrom62.map markedData = dataFrom62 := by
  simp only [rowsFrom62, dataFrom62, List.map_append, mapped62, mappedFrom63]
theorem cleanFrom62 : linesFrom62.all clean = true := by
  simp only [linesFrom62, List.all_append, clean62, cleanFrom63, Bool.and_self]

def linesFrom61 : List String := lines61 ++ linesFrom62
def rowsFrom61 : List RawRow := rows61 ++ rowsFrom62
def dataFrom61 : List DataRow := data61 ++ dataFrom62
theorem parsedFrom61 : linesFrom61.mapM (fun s => parseRow s.toList) = some rowsFrom61 :=
  parse_append _ _ _ _ parsed61 parsedFrom62
theorem mappedFrom61 : rowsFrom61.map markedData = dataFrom61 := by
  simp only [rowsFrom61, dataFrom61, List.map_append, mapped61, mappedFrom62]
theorem cleanFrom61 : linesFrom61.all clean = true := by
  simp only [linesFrom61, List.all_append, clean61, cleanFrom62, Bool.and_self]

def linesFrom60 : List String := lines60 ++ linesFrom61
def rowsFrom60 : List RawRow := rows60 ++ rowsFrom61
def dataFrom60 : List DataRow := data60 ++ dataFrom61
theorem parsedFrom60 : linesFrom60.mapM (fun s => parseRow s.toList) = some rowsFrom60 :=
  parse_append _ _ _ _ parsed60 parsedFrom61
theorem mappedFrom60 : rowsFrom60.map markedData = dataFrom60 := by
  simp only [rowsFrom60, dataFrom60, List.map_append, mapped60, mappedFrom61]
theorem cleanFrom60 : linesFrom60.all clean = true := by
  simp only [linesFrom60, List.all_append, clean60, cleanFrom61, Bool.and_self]

def linesFrom59 : List String := lines59 ++ linesFrom60
def rowsFrom59 : List RawRow := rows59 ++ rowsFrom60
def dataFrom59 : List DataRow := data59 ++ dataFrom60
theorem parsedFrom59 : linesFrom59.mapM (fun s => parseRow s.toList) = some rowsFrom59 :=
  parse_append _ _ _ _ parsed59 parsedFrom60
theorem mappedFrom59 : rowsFrom59.map markedData = dataFrom59 := by
  simp only [rowsFrom59, dataFrom59, List.map_append, mapped59, mappedFrom60]
theorem cleanFrom59 : linesFrom59.all clean = true := by
  simp only [linesFrom59, List.all_append, clean59, cleanFrom60, Bool.and_self]

def linesFrom58 : List String := lines58 ++ linesFrom59
def rowsFrom58 : List RawRow := rows58 ++ rowsFrom59
def dataFrom58 : List DataRow := data58 ++ dataFrom59
theorem parsedFrom58 : linesFrom58.mapM (fun s => parseRow s.toList) = some rowsFrom58 :=
  parse_append _ _ _ _ parsed58 parsedFrom59
theorem mappedFrom58 : rowsFrom58.map markedData = dataFrom58 := by
  simp only [rowsFrom58, dataFrom58, List.map_append, mapped58, mappedFrom59]
theorem cleanFrom58 : linesFrom58.all clean = true := by
  simp only [linesFrom58, List.all_append, clean58, cleanFrom59, Bool.and_self]

def linesFrom57 : List String := lines57 ++ linesFrom58
def rowsFrom57 : List RawRow := rows57 ++ rowsFrom58
def dataFrom57 : List DataRow := data57 ++ dataFrom58
theorem parsedFrom57 : linesFrom57.mapM (fun s => parseRow s.toList) = some rowsFrom57 :=
  parse_append _ _ _ _ parsed57 parsedFrom58
theorem mappedFrom57 : rowsFrom57.map markedData = dataFrom57 := by
  simp only [rowsFrom57, dataFrom57, List.map_append, mapped57, mappedFrom58]
theorem cleanFrom57 : linesFrom57.all clean = true := by
  simp only [linesFrom57, List.all_append, clean57, cleanFrom58, Bool.and_self]

def linesFrom56 : List String := lines56 ++ linesFrom57
def rowsFrom56 : List RawRow := rows56 ++ rowsFrom57
def dataFrom56 : List DataRow := data56 ++ dataFrom57
theorem parsedFrom56 : linesFrom56.mapM (fun s => parseRow s.toList) = some rowsFrom56 :=
  parse_append _ _ _ _ parsed56 parsedFrom57
theorem mappedFrom56 : rowsFrom56.map markedData = dataFrom56 := by
  simp only [rowsFrom56, dataFrom56, List.map_append, mapped56, mappedFrom57]
theorem cleanFrom56 : linesFrom56.all clean = true := by
  simp only [linesFrom56, List.all_append, clean56, cleanFrom57, Bool.and_self]

def linesFrom55 : List String := lines55 ++ linesFrom56
def rowsFrom55 : List RawRow := rows55 ++ rowsFrom56
def dataFrom55 : List DataRow := data55 ++ dataFrom56
theorem parsedFrom55 : linesFrom55.mapM (fun s => parseRow s.toList) = some rowsFrom55 :=
  parse_append _ _ _ _ parsed55 parsedFrom56
theorem mappedFrom55 : rowsFrom55.map markedData = dataFrom55 := by
  simp only [rowsFrom55, dataFrom55, List.map_append, mapped55, mappedFrom56]
theorem cleanFrom55 : linesFrom55.all clean = true := by
  simp only [linesFrom55, List.all_append, clean55, cleanFrom56, Bool.and_self]

def linesFrom54 : List String := lines54 ++ linesFrom55
def rowsFrom54 : List RawRow := rows54 ++ rowsFrom55
def dataFrom54 : List DataRow := data54 ++ dataFrom55
theorem parsedFrom54 : linesFrom54.mapM (fun s => parseRow s.toList) = some rowsFrom54 :=
  parse_append _ _ _ _ parsed54 parsedFrom55
theorem mappedFrom54 : rowsFrom54.map markedData = dataFrom54 := by
  simp only [rowsFrom54, dataFrom54, List.map_append, mapped54, mappedFrom55]
theorem cleanFrom54 : linesFrom54.all clean = true := by
  simp only [linesFrom54, List.all_append, clean54, cleanFrom55, Bool.and_self]

def linesFrom53 : List String := lines53 ++ linesFrom54
def rowsFrom53 : List RawRow := rows53 ++ rowsFrom54
def dataFrom53 : List DataRow := data53 ++ dataFrom54
theorem parsedFrom53 : linesFrom53.mapM (fun s => parseRow s.toList) = some rowsFrom53 :=
  parse_append _ _ _ _ parsed53 parsedFrom54
theorem mappedFrom53 : rowsFrom53.map markedData = dataFrom53 := by
  simp only [rowsFrom53, dataFrom53, List.map_append, mapped53, mappedFrom54]
theorem cleanFrom53 : linesFrom53.all clean = true := by
  simp only [linesFrom53, List.all_append, clean53, cleanFrom54, Bool.and_self]

def linesFrom52 : List String := lines52 ++ linesFrom53
def rowsFrom52 : List RawRow := rows52 ++ rowsFrom53
def dataFrom52 : List DataRow := data52 ++ dataFrom53
theorem parsedFrom52 : linesFrom52.mapM (fun s => parseRow s.toList) = some rowsFrom52 :=
  parse_append _ _ _ _ parsed52 parsedFrom53
theorem mappedFrom52 : rowsFrom52.map markedData = dataFrom52 := by
  simp only [rowsFrom52, dataFrom52, List.map_append, mapped52, mappedFrom53]
theorem cleanFrom52 : linesFrom52.all clean = true := by
  simp only [linesFrom52, List.all_append, clean52, cleanFrom53, Bool.and_self]

def linesFrom51 : List String := lines51 ++ linesFrom52
def rowsFrom51 : List RawRow := rows51 ++ rowsFrom52
def dataFrom51 : List DataRow := data51 ++ dataFrom52
theorem parsedFrom51 : linesFrom51.mapM (fun s => parseRow s.toList) = some rowsFrom51 :=
  parse_append _ _ _ _ parsed51 parsedFrom52
theorem mappedFrom51 : rowsFrom51.map markedData = dataFrom51 := by
  simp only [rowsFrom51, dataFrom51, List.map_append, mapped51, mappedFrom52]
theorem cleanFrom51 : linesFrom51.all clean = true := by
  simp only [linesFrom51, List.all_append, clean51, cleanFrom52, Bool.and_self]

def linesFrom50 : List String := lines50 ++ linesFrom51
def rowsFrom50 : List RawRow := rows50 ++ rowsFrom51
def dataFrom50 : List DataRow := data50 ++ dataFrom51
theorem parsedFrom50 : linesFrom50.mapM (fun s => parseRow s.toList) = some rowsFrom50 :=
  parse_append _ _ _ _ parsed50 parsedFrom51
theorem mappedFrom50 : rowsFrom50.map markedData = dataFrom50 := by
  simp only [rowsFrom50, dataFrom50, List.map_append, mapped50, mappedFrom51]
theorem cleanFrom50 : linesFrom50.all clean = true := by
  simp only [linesFrom50, List.all_append, clean50, cleanFrom51, Bool.and_self]

def linesFrom49 : List String := lines49 ++ linesFrom50
def rowsFrom49 : List RawRow := rows49 ++ rowsFrom50
def dataFrom49 : List DataRow := data49 ++ dataFrom50
theorem parsedFrom49 : linesFrom49.mapM (fun s => parseRow s.toList) = some rowsFrom49 :=
  parse_append _ _ _ _ parsed49 parsedFrom50
theorem mappedFrom49 : rowsFrom49.map markedData = dataFrom49 := by
  simp only [rowsFrom49, dataFrom49, List.map_append, mapped49, mappedFrom50]
theorem cleanFrom49 : linesFrom49.all clean = true := by
  simp only [linesFrom49, List.all_append, clean49, cleanFrom50, Bool.and_self]

def linesFrom48 : List String := lines48 ++ linesFrom49
def rowsFrom48 : List RawRow := rows48 ++ rowsFrom49
def dataFrom48 : List DataRow := data48 ++ dataFrom49
theorem parsedFrom48 : linesFrom48.mapM (fun s => parseRow s.toList) = some rowsFrom48 :=
  parse_append _ _ _ _ parsed48 parsedFrom49
theorem mappedFrom48 : rowsFrom48.map markedData = dataFrom48 := by
  simp only [rowsFrom48, dataFrom48, List.map_append, mapped48, mappedFrom49]
theorem cleanFrom48 : linesFrom48.all clean = true := by
  simp only [linesFrom48, List.all_append, clean48, cleanFrom49, Bool.and_self]

def linesFrom47 : List String := lines47 ++ linesFrom48
def rowsFrom47 : List RawRow := rows47 ++ rowsFrom48
def dataFrom47 : List DataRow := data47 ++ dataFrom48
theorem parsedFrom47 : linesFrom47.mapM (fun s => parseRow s.toList) = some rowsFrom47 :=
  parse_append _ _ _ _ parsed47 parsedFrom48
theorem mappedFrom47 : rowsFrom47.map markedData = dataFrom47 := by
  simp only [rowsFrom47, dataFrom47, List.map_append, mapped47, mappedFrom48]
theorem cleanFrom47 : linesFrom47.all clean = true := by
  simp only [linesFrom47, List.all_append, clean47, cleanFrom48, Bool.and_self]

def linesFrom46 : List String := lines46 ++ linesFrom47
def rowsFrom46 : List RawRow := rows46 ++ rowsFrom47
def dataFrom46 : List DataRow := data46 ++ dataFrom47
theorem parsedFrom46 : linesFrom46.mapM (fun s => parseRow s.toList) = some rowsFrom46 :=
  parse_append _ _ _ _ parsed46 parsedFrom47
theorem mappedFrom46 : rowsFrom46.map markedData = dataFrom46 := by
  simp only [rowsFrom46, dataFrom46, List.map_append, mapped46, mappedFrom47]
theorem cleanFrom46 : linesFrom46.all clean = true := by
  simp only [linesFrom46, List.all_append, clean46, cleanFrom47, Bool.and_self]

def linesFrom45 : List String := lines45 ++ linesFrom46
def rowsFrom45 : List RawRow := rows45 ++ rowsFrom46
def dataFrom45 : List DataRow := data45 ++ dataFrom46
theorem parsedFrom45 : linesFrom45.mapM (fun s => parseRow s.toList) = some rowsFrom45 :=
  parse_append _ _ _ _ parsed45 parsedFrom46
theorem mappedFrom45 : rowsFrom45.map markedData = dataFrom45 := by
  simp only [rowsFrom45, dataFrom45, List.map_append, mapped45, mappedFrom46]
theorem cleanFrom45 : linesFrom45.all clean = true := by
  simp only [linesFrom45, List.all_append, clean45, cleanFrom46, Bool.and_self]

def linesFrom44 : List String := lines44 ++ linesFrom45
def rowsFrom44 : List RawRow := rows44 ++ rowsFrom45
def dataFrom44 : List DataRow := data44 ++ dataFrom45
theorem parsedFrom44 : linesFrom44.mapM (fun s => parseRow s.toList) = some rowsFrom44 :=
  parse_append _ _ _ _ parsed44 parsedFrom45
theorem mappedFrom44 : rowsFrom44.map markedData = dataFrom44 := by
  simp only [rowsFrom44, dataFrom44, List.map_append, mapped44, mappedFrom45]
theorem cleanFrom44 : linesFrom44.all clean = true := by
  simp only [linesFrom44, List.all_append, clean44, cleanFrom45, Bool.and_self]

def linesFrom43 : List String := lines43 ++ linesFrom44
def rowsFrom43 : List RawRow := rows43 ++ rowsFrom44
def dataFrom43 : List DataRow := data43 ++ dataFrom44
theorem parsedFrom43 : linesFrom43.mapM (fun s => parseRow s.toList) = some rowsFrom43 :=
  parse_append _ _ _ _ parsed43 parsedFrom44
theorem mappedFrom43 : rowsFrom43.map markedData = dataFrom43 := by
  simp only [rowsFrom43, dataFrom43, List.map_append, mapped43, mappedFrom44]
theorem cleanFrom43 : linesFrom43.all clean = true := by
  simp only [linesFrom43, List.all_append, clean43, cleanFrom44, Bool.and_self]

def linesFrom42 : List String := lines42 ++ linesFrom43
def rowsFrom42 : List RawRow := rows42 ++ rowsFrom43
def dataFrom42 : List DataRow := data42 ++ dataFrom43
theorem parsedFrom42 : linesFrom42.mapM (fun s => parseRow s.toList) = some rowsFrom42 :=
  parse_append _ _ _ _ parsed42 parsedFrom43
theorem mappedFrom42 : rowsFrom42.map markedData = dataFrom42 := by
  simp only [rowsFrom42, dataFrom42, List.map_append, mapped42, mappedFrom43]
theorem cleanFrom42 : linesFrom42.all clean = true := by
  simp only [linesFrom42, List.all_append, clean42, cleanFrom43, Bool.and_self]

def linesFrom41 : List String := lines41 ++ linesFrom42
def rowsFrom41 : List RawRow := rows41 ++ rowsFrom42
def dataFrom41 : List DataRow := data41 ++ dataFrom42
theorem parsedFrom41 : linesFrom41.mapM (fun s => parseRow s.toList) = some rowsFrom41 :=
  parse_append _ _ _ _ parsed41 parsedFrom42
theorem mappedFrom41 : rowsFrom41.map markedData = dataFrom41 := by
  simp only [rowsFrom41, dataFrom41, List.map_append, mapped41, mappedFrom42]
theorem cleanFrom41 : linesFrom41.all clean = true := by
  simp only [linesFrom41, List.all_append, clean41, cleanFrom42, Bool.and_self]

def linesFrom40 : List String := lines40 ++ linesFrom41
def rowsFrom40 : List RawRow := rows40 ++ rowsFrom41
def dataFrom40 : List DataRow := data40 ++ dataFrom41
theorem parsedFrom40 : linesFrom40.mapM (fun s => parseRow s.toList) = some rowsFrom40 :=
  parse_append _ _ _ _ parsed40 parsedFrom41
theorem mappedFrom40 : rowsFrom40.map markedData = dataFrom40 := by
  simp only [rowsFrom40, dataFrom40, List.map_append, mapped40, mappedFrom41]
theorem cleanFrom40 : linesFrom40.all clean = true := by
  simp only [linesFrom40, List.all_append, clean40, cleanFrom41, Bool.and_self]

def linesFrom39 : List String := lines39 ++ linesFrom40
def rowsFrom39 : List RawRow := rows39 ++ rowsFrom40
def dataFrom39 : List DataRow := data39 ++ dataFrom40
theorem parsedFrom39 : linesFrom39.mapM (fun s => parseRow s.toList) = some rowsFrom39 :=
  parse_append _ _ _ _ parsed39 parsedFrom40
theorem mappedFrom39 : rowsFrom39.map markedData = dataFrom39 := by
  simp only [rowsFrom39, dataFrom39, List.map_append, mapped39, mappedFrom40]
theorem cleanFrom39 : linesFrom39.all clean = true := by
  simp only [linesFrom39, List.all_append, clean39, cleanFrom40, Bool.and_self]

def linesFrom38 : List String := lines38 ++ linesFrom39
def rowsFrom38 : List RawRow := rows38 ++ rowsFrom39
def dataFrom38 : List DataRow := data38 ++ dataFrom39
theorem parsedFrom38 : linesFrom38.mapM (fun s => parseRow s.toList) = some rowsFrom38 :=
  parse_append _ _ _ _ parsed38 parsedFrom39
theorem mappedFrom38 : rowsFrom38.map markedData = dataFrom38 := by
  simp only [rowsFrom38, dataFrom38, List.map_append, mapped38, mappedFrom39]
theorem cleanFrom38 : linesFrom38.all clean = true := by
  simp only [linesFrom38, List.all_append, clean38, cleanFrom39, Bool.and_self]

def linesFrom37 : List String := lines37 ++ linesFrom38
def rowsFrom37 : List RawRow := rows37 ++ rowsFrom38
def dataFrom37 : List DataRow := data37 ++ dataFrom38
theorem parsedFrom37 : linesFrom37.mapM (fun s => parseRow s.toList) = some rowsFrom37 :=
  parse_append _ _ _ _ parsed37 parsedFrom38
theorem mappedFrom37 : rowsFrom37.map markedData = dataFrom37 := by
  simp only [rowsFrom37, dataFrom37, List.map_append, mapped37, mappedFrom38]
theorem cleanFrom37 : linesFrom37.all clean = true := by
  simp only [linesFrom37, List.all_append, clean37, cleanFrom38, Bool.and_self]

def linesFrom36 : List String := lines36 ++ linesFrom37
def rowsFrom36 : List RawRow := rows36 ++ rowsFrom37
def dataFrom36 : List DataRow := data36 ++ dataFrom37
theorem parsedFrom36 : linesFrom36.mapM (fun s => parseRow s.toList) = some rowsFrom36 :=
  parse_append _ _ _ _ parsed36 parsedFrom37
theorem mappedFrom36 : rowsFrom36.map markedData = dataFrom36 := by
  simp only [rowsFrom36, dataFrom36, List.map_append, mapped36, mappedFrom37]
theorem cleanFrom36 : linesFrom36.all clean = true := by
  simp only [linesFrom36, List.all_append, clean36, cleanFrom37, Bool.and_self]

def linesFrom35 : List String := lines35 ++ linesFrom36
def rowsFrom35 : List RawRow := rows35 ++ rowsFrom36
def dataFrom35 : List DataRow := data35 ++ dataFrom36
theorem parsedFrom35 : linesFrom35.mapM (fun s => parseRow s.toList) = some rowsFrom35 :=
  parse_append _ _ _ _ parsed35 parsedFrom36
theorem mappedFrom35 : rowsFrom35.map markedData = dataFrom35 := by
  simp only [rowsFrom35, dataFrom35, List.map_append, mapped35, mappedFrom36]
theorem cleanFrom35 : linesFrom35.all clean = true := by
  simp only [linesFrom35, List.all_append, clean35, cleanFrom36, Bool.and_self]

def linesFrom34 : List String := lines34 ++ linesFrom35
def rowsFrom34 : List RawRow := rows34 ++ rowsFrom35
def dataFrom34 : List DataRow := data34 ++ dataFrom35
theorem parsedFrom34 : linesFrom34.mapM (fun s => parseRow s.toList) = some rowsFrom34 :=
  parse_append _ _ _ _ parsed34 parsedFrom35
theorem mappedFrom34 : rowsFrom34.map markedData = dataFrom34 := by
  simp only [rowsFrom34, dataFrom34, List.map_append, mapped34, mappedFrom35]
theorem cleanFrom34 : linesFrom34.all clean = true := by
  simp only [linesFrom34, List.all_append, clean34, cleanFrom35, Bool.and_self]

def linesFrom33 : List String := lines33 ++ linesFrom34
def rowsFrom33 : List RawRow := rows33 ++ rowsFrom34
def dataFrom33 : List DataRow := data33 ++ dataFrom34
theorem parsedFrom33 : linesFrom33.mapM (fun s => parseRow s.toList) = some rowsFrom33 :=
  parse_append _ _ _ _ parsed33 parsedFrom34
theorem mappedFrom33 : rowsFrom33.map markedData = dataFrom33 := by
  simp only [rowsFrom33, dataFrom33, List.map_append, mapped33, mappedFrom34]
theorem cleanFrom33 : linesFrom33.all clean = true := by
  simp only [linesFrom33, List.all_append, clean33, cleanFrom34, Bool.and_self]

def linesFrom32 : List String := lines32 ++ linesFrom33
def rowsFrom32 : List RawRow := rows32 ++ rowsFrom33
def dataFrom32 : List DataRow := data32 ++ dataFrom33
theorem parsedFrom32 : linesFrom32.mapM (fun s => parseRow s.toList) = some rowsFrom32 :=
  parse_append _ _ _ _ parsed32 parsedFrom33
theorem mappedFrom32 : rowsFrom32.map markedData = dataFrom32 := by
  simp only [rowsFrom32, dataFrom32, List.map_append, mapped32, mappedFrom33]
theorem cleanFrom32 : linesFrom32.all clean = true := by
  simp only [linesFrom32, List.all_append, clean32, cleanFrom33, Bool.and_self]

def linesFrom31 : List String := lines31 ++ linesFrom32
def rowsFrom31 : List RawRow := rows31 ++ rowsFrom32
def dataFrom31 : List DataRow := data31 ++ dataFrom32
theorem parsedFrom31 : linesFrom31.mapM (fun s => parseRow s.toList) = some rowsFrom31 :=
  parse_append _ _ _ _ parsed31 parsedFrom32
theorem mappedFrom31 : rowsFrom31.map markedData = dataFrom31 := by
  simp only [rowsFrom31, dataFrom31, List.map_append, mapped31, mappedFrom32]
theorem cleanFrom31 : linesFrom31.all clean = true := by
  simp only [linesFrom31, List.all_append, clean31, cleanFrom32, Bool.and_self]

def linesFrom30 : List String := lines30 ++ linesFrom31
def rowsFrom30 : List RawRow := rows30 ++ rowsFrom31
def dataFrom30 : List DataRow := data30 ++ dataFrom31
theorem parsedFrom30 : linesFrom30.mapM (fun s => parseRow s.toList) = some rowsFrom30 :=
  parse_append _ _ _ _ parsed30 parsedFrom31
theorem mappedFrom30 : rowsFrom30.map markedData = dataFrom30 := by
  simp only [rowsFrom30, dataFrom30, List.map_append, mapped30, mappedFrom31]
theorem cleanFrom30 : linesFrom30.all clean = true := by
  simp only [linesFrom30, List.all_append, clean30, cleanFrom31, Bool.and_self]

def linesFrom29 : List String := lines29 ++ linesFrom30
def rowsFrom29 : List RawRow := rows29 ++ rowsFrom30
def dataFrom29 : List DataRow := data29 ++ dataFrom30
theorem parsedFrom29 : linesFrom29.mapM (fun s => parseRow s.toList) = some rowsFrom29 :=
  parse_append _ _ _ _ parsed29 parsedFrom30
theorem mappedFrom29 : rowsFrom29.map markedData = dataFrom29 := by
  simp only [rowsFrom29, dataFrom29, List.map_append, mapped29, mappedFrom30]
theorem cleanFrom29 : linesFrom29.all clean = true := by
  simp only [linesFrom29, List.all_append, clean29, cleanFrom30, Bool.and_self]

def linesFrom28 : List String := lines28 ++ linesFrom29
def rowsFrom28 : List RawRow := rows28 ++ rowsFrom29
def dataFrom28 : List DataRow := data28 ++ dataFrom29
theorem parsedFrom28 : linesFrom28.mapM (fun s => parseRow s.toList) = some rowsFrom28 :=
  parse_append _ _ _ _ parsed28 parsedFrom29
theorem mappedFrom28 : rowsFrom28.map markedData = dataFrom28 := by
  simp only [rowsFrom28, dataFrom28, List.map_append, mapped28, mappedFrom29]
theorem cleanFrom28 : linesFrom28.all clean = true := by
  simp only [linesFrom28, List.all_append, clean28, cleanFrom29, Bool.and_self]

def linesFrom27 : List String := lines27 ++ linesFrom28
def rowsFrom27 : List RawRow := rows27 ++ rowsFrom28
def dataFrom27 : List DataRow := data27 ++ dataFrom28
theorem parsedFrom27 : linesFrom27.mapM (fun s => parseRow s.toList) = some rowsFrom27 :=
  parse_append _ _ _ _ parsed27 parsedFrom28
theorem mappedFrom27 : rowsFrom27.map markedData = dataFrom27 := by
  simp only [rowsFrom27, dataFrom27, List.map_append, mapped27, mappedFrom28]
theorem cleanFrom27 : linesFrom27.all clean = true := by
  simp only [linesFrom27, List.all_append, clean27, cleanFrom28, Bool.and_self]

def linesFrom26 : List String := lines26 ++ linesFrom27
def rowsFrom26 : List RawRow := rows26 ++ rowsFrom27
def dataFrom26 : List DataRow := data26 ++ dataFrom27
theorem parsedFrom26 : linesFrom26.mapM (fun s => parseRow s.toList) = some rowsFrom26 :=
  parse_append _ _ _ _ parsed26 parsedFrom27
theorem mappedFrom26 : rowsFrom26.map markedData = dataFrom26 := by
  simp only [rowsFrom26, dataFrom26, List.map_append, mapped26, mappedFrom27]
theorem cleanFrom26 : linesFrom26.all clean = true := by
  simp only [linesFrom26, List.all_append, clean26, cleanFrom27, Bool.and_self]

def linesFrom25 : List String := lines25 ++ linesFrom26
def rowsFrom25 : List RawRow := rows25 ++ rowsFrom26
def dataFrom25 : List DataRow := data25 ++ dataFrom26
theorem parsedFrom25 : linesFrom25.mapM (fun s => parseRow s.toList) = some rowsFrom25 :=
  parse_append _ _ _ _ parsed25 parsedFrom26
theorem mappedFrom25 : rowsFrom25.map markedData = dataFrom25 := by
  simp only [rowsFrom25, dataFrom25, List.map_append, mapped25, mappedFrom26]
theorem cleanFrom25 : linesFrom25.all clean = true := by
  simp only [linesFrom25, List.all_append, clean25, cleanFrom26, Bool.and_self]

def linesFrom24 : List String := lines24 ++ linesFrom25
def rowsFrom24 : List RawRow := rows24 ++ rowsFrom25
def dataFrom24 : List DataRow := data24 ++ dataFrom25
theorem parsedFrom24 : linesFrom24.mapM (fun s => parseRow s.toList) = some rowsFrom24 :=
  parse_append _ _ _ _ parsed24 parsedFrom25
theorem mappedFrom24 : rowsFrom24.map markedData = dataFrom24 := by
  simp only [rowsFrom24, dataFrom24, List.map_append, mapped24, mappedFrom25]
theorem cleanFrom24 : linesFrom24.all clean = true := by
  simp only [linesFrom24, List.all_append, clean24, cleanFrom25, Bool.and_self]

def linesFrom23 : List String := lines23 ++ linesFrom24
def rowsFrom23 : List RawRow := rows23 ++ rowsFrom24
def dataFrom23 : List DataRow := data23 ++ dataFrom24
theorem parsedFrom23 : linesFrom23.mapM (fun s => parseRow s.toList) = some rowsFrom23 :=
  parse_append _ _ _ _ parsed23 parsedFrom24
theorem mappedFrom23 : rowsFrom23.map markedData = dataFrom23 := by
  simp only [rowsFrom23, dataFrom23, List.map_append, mapped23, mappedFrom24]
theorem cleanFrom23 : linesFrom23.all clean = true := by
  simp only [linesFrom23, List.all_append, clean23, cleanFrom24, Bool.and_self]

def linesFrom22 : List String := lines22 ++ linesFrom23
def rowsFrom22 : List RawRow := rows22 ++ rowsFrom23
def dataFrom22 : List DataRow := data22 ++ dataFrom23
theorem parsedFrom22 : linesFrom22.mapM (fun s => parseRow s.toList) = some rowsFrom22 :=
  parse_append _ _ _ _ parsed22 parsedFrom23
theorem mappedFrom22 : rowsFrom22.map markedData = dataFrom22 := by
  simp only [rowsFrom22, dataFrom22, List.map_append, mapped22, mappedFrom23]
theorem cleanFrom22 : linesFrom22.all clean = true := by
  simp only [linesFrom22, List.all_append, clean22, cleanFrom23, Bool.and_self]

def linesFrom21 : List String := lines21 ++ linesFrom22
def rowsFrom21 : List RawRow := rows21 ++ rowsFrom22
def dataFrom21 : List DataRow := data21 ++ dataFrom22
theorem parsedFrom21 : linesFrom21.mapM (fun s => parseRow s.toList) = some rowsFrom21 :=
  parse_append _ _ _ _ parsed21 parsedFrom22
theorem mappedFrom21 : rowsFrom21.map markedData = dataFrom21 := by
  simp only [rowsFrom21, dataFrom21, List.map_append, mapped21, mappedFrom22]
theorem cleanFrom21 : linesFrom21.all clean = true := by
  simp only [linesFrom21, List.all_append, clean21, cleanFrom22, Bool.and_self]

def linesFrom20 : List String := lines20 ++ linesFrom21
def rowsFrom20 : List RawRow := rows20 ++ rowsFrom21
def dataFrom20 : List DataRow := data20 ++ dataFrom21
theorem parsedFrom20 : linesFrom20.mapM (fun s => parseRow s.toList) = some rowsFrom20 :=
  parse_append _ _ _ _ parsed20 parsedFrom21
theorem mappedFrom20 : rowsFrom20.map markedData = dataFrom20 := by
  simp only [rowsFrom20, dataFrom20, List.map_append, mapped20, mappedFrom21]
theorem cleanFrom20 : linesFrom20.all clean = true := by
  simp only [linesFrom20, List.all_append, clean20, cleanFrom21, Bool.and_self]

def linesFrom19 : List String := lines19 ++ linesFrom20
def rowsFrom19 : List RawRow := rows19 ++ rowsFrom20
def dataFrom19 : List DataRow := data19 ++ dataFrom20
theorem parsedFrom19 : linesFrom19.mapM (fun s => parseRow s.toList) = some rowsFrom19 :=
  parse_append _ _ _ _ parsed19 parsedFrom20
theorem mappedFrom19 : rowsFrom19.map markedData = dataFrom19 := by
  simp only [rowsFrom19, dataFrom19, List.map_append, mapped19, mappedFrom20]
theorem cleanFrom19 : linesFrom19.all clean = true := by
  simp only [linesFrom19, List.all_append, clean19, cleanFrom20, Bool.and_self]

def linesFrom18 : List String := lines18 ++ linesFrom19
def rowsFrom18 : List RawRow := rows18 ++ rowsFrom19
def dataFrom18 : List DataRow := data18 ++ dataFrom19
theorem parsedFrom18 : linesFrom18.mapM (fun s => parseRow s.toList) = some rowsFrom18 :=
  parse_append _ _ _ _ parsed18 parsedFrom19
theorem mappedFrom18 : rowsFrom18.map markedData = dataFrom18 := by
  simp only [rowsFrom18, dataFrom18, List.map_append, mapped18, mappedFrom19]
theorem cleanFrom18 : linesFrom18.all clean = true := by
  simp only [linesFrom18, List.all_append, clean18, cleanFrom19, Bool.and_self]

def linesFrom17 : List String := lines17 ++ linesFrom18
def rowsFrom17 : List RawRow := rows17 ++ rowsFrom18
def dataFrom17 : List DataRow := data17 ++ dataFrom18
theorem parsedFrom17 : linesFrom17.mapM (fun s => parseRow s.toList) = some rowsFrom17 :=
  parse_append _ _ _ _ parsed17 parsedFrom18
theorem mappedFrom17 : rowsFrom17.map markedData = dataFrom17 := by
  simp only [rowsFrom17, dataFrom17, List.map_append, mapped17, mappedFrom18]
theorem cleanFrom17 : linesFrom17.all clean = true := by
  simp only [linesFrom17, List.all_append, clean17, cleanFrom18, Bool.and_self]

def linesFrom16 : List String := lines16 ++ linesFrom17
def rowsFrom16 : List RawRow := rows16 ++ rowsFrom17
def dataFrom16 : List DataRow := data16 ++ dataFrom17
theorem parsedFrom16 : linesFrom16.mapM (fun s => parseRow s.toList) = some rowsFrom16 :=
  parse_append _ _ _ _ parsed16 parsedFrom17
theorem mappedFrom16 : rowsFrom16.map markedData = dataFrom16 := by
  simp only [rowsFrom16, dataFrom16, List.map_append, mapped16, mappedFrom17]
theorem cleanFrom16 : linesFrom16.all clean = true := by
  simp only [linesFrom16, List.all_append, clean16, cleanFrom17, Bool.and_self]

def linesFrom15 : List String := lines15 ++ linesFrom16
def rowsFrom15 : List RawRow := rows15 ++ rowsFrom16
def dataFrom15 : List DataRow := data15 ++ dataFrom16
theorem parsedFrom15 : linesFrom15.mapM (fun s => parseRow s.toList) = some rowsFrom15 :=
  parse_append _ _ _ _ parsed15 parsedFrom16
theorem mappedFrom15 : rowsFrom15.map markedData = dataFrom15 := by
  simp only [rowsFrom15, dataFrom15, List.map_append, mapped15, mappedFrom16]
theorem cleanFrom15 : linesFrom15.all clean = true := by
  simp only [linesFrom15, List.all_append, clean15, cleanFrom16, Bool.and_self]

def linesFrom14 : List String := lines14 ++ linesFrom15
def rowsFrom14 : List RawRow := rows14 ++ rowsFrom15
def dataFrom14 : List DataRow := data14 ++ dataFrom15
theorem parsedFrom14 : linesFrom14.mapM (fun s => parseRow s.toList) = some rowsFrom14 :=
  parse_append _ _ _ _ parsed14 parsedFrom15
theorem mappedFrom14 : rowsFrom14.map markedData = dataFrom14 := by
  simp only [rowsFrom14, dataFrom14, List.map_append, mapped14, mappedFrom15]
theorem cleanFrom14 : linesFrom14.all clean = true := by
  simp only [linesFrom14, List.all_append, clean14, cleanFrom15, Bool.and_self]

def linesFrom13 : List String := lines13 ++ linesFrom14
def rowsFrom13 : List RawRow := rows13 ++ rowsFrom14
def dataFrom13 : List DataRow := data13 ++ dataFrom14
theorem parsedFrom13 : linesFrom13.mapM (fun s => parseRow s.toList) = some rowsFrom13 :=
  parse_append _ _ _ _ parsed13 parsedFrom14
theorem mappedFrom13 : rowsFrom13.map markedData = dataFrom13 := by
  simp only [rowsFrom13, dataFrom13, List.map_append, mapped13, mappedFrom14]
theorem cleanFrom13 : linesFrom13.all clean = true := by
  simp only [linesFrom13, List.all_append, clean13, cleanFrom14, Bool.and_self]

def linesFrom12 : List String := lines12 ++ linesFrom13
def rowsFrom12 : List RawRow := rows12 ++ rowsFrom13
def dataFrom12 : List DataRow := data12 ++ dataFrom13
theorem parsedFrom12 : linesFrom12.mapM (fun s => parseRow s.toList) = some rowsFrom12 :=
  parse_append _ _ _ _ parsed12 parsedFrom13
theorem mappedFrom12 : rowsFrom12.map markedData = dataFrom12 := by
  simp only [rowsFrom12, dataFrom12, List.map_append, mapped12, mappedFrom13]
theorem cleanFrom12 : linesFrom12.all clean = true := by
  simp only [linesFrom12, List.all_append, clean12, cleanFrom13, Bool.and_self]

def linesFrom11 : List String := lines11 ++ linesFrom12
def rowsFrom11 : List RawRow := rows11 ++ rowsFrom12
def dataFrom11 : List DataRow := data11 ++ dataFrom12
theorem parsedFrom11 : linesFrom11.mapM (fun s => parseRow s.toList) = some rowsFrom11 :=
  parse_append _ _ _ _ parsed11 parsedFrom12
theorem mappedFrom11 : rowsFrom11.map markedData = dataFrom11 := by
  simp only [rowsFrom11, dataFrom11, List.map_append, mapped11, mappedFrom12]
theorem cleanFrom11 : linesFrom11.all clean = true := by
  simp only [linesFrom11, List.all_append, clean11, cleanFrom12, Bool.and_self]

def linesFrom10 : List String := lines10 ++ linesFrom11
def rowsFrom10 : List RawRow := rows10 ++ rowsFrom11
def dataFrom10 : List DataRow := data10 ++ dataFrom11
theorem parsedFrom10 : linesFrom10.mapM (fun s => parseRow s.toList) = some rowsFrom10 :=
  parse_append _ _ _ _ parsed10 parsedFrom11
theorem mappedFrom10 : rowsFrom10.map markedData = dataFrom10 := by
  simp only [rowsFrom10, dataFrom10, List.map_append, mapped10, mappedFrom11]
theorem cleanFrom10 : linesFrom10.all clean = true := by
  simp only [linesFrom10, List.all_append, clean10, cleanFrom11, Bool.and_self]

def linesFrom9 : List String := lines9 ++ linesFrom10
def rowsFrom9 : List RawRow := rows9 ++ rowsFrom10
def dataFrom9 : List DataRow := data9 ++ dataFrom10
theorem parsedFrom9 : linesFrom9.mapM (fun s => parseRow s.toList) = some rowsFrom9 :=
  parse_append _ _ _ _ parsed9 parsedFrom10
theorem mappedFrom9 : rowsFrom9.map markedData = dataFrom9 := by
  simp only [rowsFrom9, dataFrom9, List.map_append, mapped9, mappedFrom10]
theorem cleanFrom9 : linesFrom9.all clean = true := by
  simp only [linesFrom9, List.all_append, clean9, cleanFrom10, Bool.and_self]

def linesFrom8 : List String := lines8 ++ linesFrom9
def rowsFrom8 : List RawRow := rows8 ++ rowsFrom9
def dataFrom8 : List DataRow := data8 ++ dataFrom9
theorem parsedFrom8 : linesFrom8.mapM (fun s => parseRow s.toList) = some rowsFrom8 :=
  parse_append _ _ _ _ parsed8 parsedFrom9
theorem mappedFrom8 : rowsFrom8.map markedData = dataFrom8 := by
  simp only [rowsFrom8, dataFrom8, List.map_append, mapped8, mappedFrom9]
theorem cleanFrom8 : linesFrom8.all clean = true := by
  simp only [linesFrom8, List.all_append, clean8, cleanFrom9, Bool.and_self]

def linesFrom7 : List String := lines7 ++ linesFrom8
def rowsFrom7 : List RawRow := rows7 ++ rowsFrom8
def dataFrom7 : List DataRow := data7 ++ dataFrom8
theorem parsedFrom7 : linesFrom7.mapM (fun s => parseRow s.toList) = some rowsFrom7 :=
  parse_append _ _ _ _ parsed7 parsedFrom8
theorem mappedFrom7 : rowsFrom7.map markedData = dataFrom7 := by
  simp only [rowsFrom7, dataFrom7, List.map_append, mapped7, mappedFrom8]
theorem cleanFrom7 : linesFrom7.all clean = true := by
  simp only [linesFrom7, List.all_append, clean7, cleanFrom8, Bool.and_self]

def linesFrom6 : List String := lines6 ++ linesFrom7
def rowsFrom6 : List RawRow := rows6 ++ rowsFrom7
def dataFrom6 : List DataRow := data6 ++ dataFrom7
theorem parsedFrom6 : linesFrom6.mapM (fun s => parseRow s.toList) = some rowsFrom6 :=
  parse_append _ _ _ _ parsed6 parsedFrom7
theorem mappedFrom6 : rowsFrom6.map markedData = dataFrom6 := by
  simp only [rowsFrom6, dataFrom6, List.map_append, mapped6, mappedFrom7]
theorem cleanFrom6 : linesFrom6.all clean = true := by
  simp only [linesFrom6, List.all_append, clean6, cleanFrom7, Bool.and_self]

def linesFrom5 : List String := lines5 ++ linesFrom6
def rowsFrom5 : List RawRow := rows5 ++ rowsFrom6
def dataFrom5 : List DataRow := data5 ++ dataFrom6
theorem parsedFrom5 : linesFrom5.mapM (fun s => parseRow s.toList) = some rowsFrom5 :=
  parse_append _ _ _ _ parsed5 parsedFrom6
theorem mappedFrom5 : rowsFrom5.map markedData = dataFrom5 := by
  simp only [rowsFrom5, dataFrom5, List.map_append, mapped5, mappedFrom6]
theorem cleanFrom5 : linesFrom5.all clean = true := by
  simp only [linesFrom5, List.all_append, clean5, cleanFrom6, Bool.and_self]

def linesFrom4 : List String := lines4 ++ linesFrom5
def rowsFrom4 : List RawRow := rows4 ++ rowsFrom5
def dataFrom4 : List DataRow := data4 ++ dataFrom5
theorem parsedFrom4 : linesFrom4.mapM (fun s => parseRow s.toList) = some rowsFrom4 :=
  parse_append _ _ _ _ parsed4 parsedFrom5
theorem mappedFrom4 : rowsFrom4.map markedData = dataFrom4 := by
  simp only [rowsFrom4, dataFrom4, List.map_append, mapped4, mappedFrom5]
theorem cleanFrom4 : linesFrom4.all clean = true := by
  simp only [linesFrom4, List.all_append, clean4, cleanFrom5, Bool.and_self]

def linesFrom3 : List String := lines3 ++ linesFrom4
def rowsFrom3 : List RawRow := rows3 ++ rowsFrom4
def dataFrom3 : List DataRow := data3 ++ dataFrom4
theorem parsedFrom3 : linesFrom3.mapM (fun s => parseRow s.toList) = some rowsFrom3 :=
  parse_append _ _ _ _ parsed3 parsedFrom4
theorem mappedFrom3 : rowsFrom3.map markedData = dataFrom3 := by
  simp only [rowsFrom3, dataFrom3, List.map_append, mapped3, mappedFrom4]
theorem cleanFrom3 : linesFrom3.all clean = true := by
  simp only [linesFrom3, List.all_append, clean3, cleanFrom4, Bool.and_self]

def linesFrom2 : List String := lines2 ++ linesFrom3
def rowsFrom2 : List RawRow := rows2 ++ rowsFrom3
def dataFrom2 : List DataRow := data2 ++ dataFrom3
theorem parsedFrom2 : linesFrom2.mapM (fun s => parseRow s.toList) = some rowsFrom2 :=
  parse_append _ _ _ _ parsed2 parsedFrom3
theorem mappedFrom2 : rowsFrom2.map markedData = dataFrom2 := by
  simp only [rowsFrom2, dataFrom2, List.map_append, mapped2, mappedFrom3]
theorem cleanFrom2 : linesFrom2.all clean = true := by
  simp only [linesFrom2, List.all_append, clean2, cleanFrom3, Bool.and_self]

def linesFrom1 : List String := lines1 ++ linesFrom2
def rowsFrom1 : List RawRow := rows1 ++ rowsFrom2
def dataFrom1 : List DataRow := data1 ++ dataFrom2
theorem parsedFrom1 : linesFrom1.mapM (fun s => parseRow s.toList) = some rowsFrom1 :=
  parse_append _ _ _ _ parsed1 parsedFrom2
theorem mappedFrom1 : rowsFrom1.map markedData = dataFrom1 := by
  simp only [rowsFrom1, dataFrom1, List.map_append, mapped1, mappedFrom2]
theorem cleanFrom1 : linesFrom1.all clean = true := by
  simp only [linesFrom1, List.all_append, clean1, cleanFrom2, Bool.and_self]

def linesFrom0 : List String := lines0 ++ linesFrom1
def rowsFrom0 : List RawRow := rows0 ++ rowsFrom1
def dataFrom0 : List DataRow := data0 ++ dataFrom1
theorem parsedFrom0 : linesFrom0.mapM (fun s => parseRow s.toList) = some rowsFrom0 :=
  parse_append _ _ _ _ parsed0 parsedFrom1
theorem mappedFrom0 : rowsFrom0.map markedData = dataFrom0 := by
  simp only [rowsFrom0, dataFrom0, List.map_append, mapped0, mappedFrom1]
theorem cleanFrom0 : linesFrom0.all clean = true := by
  simp only [linesFrom0, List.all_append, clean0, cleanFrom1, Bool.and_self]

/-- The segmented rows satisfy ordering, bounds and the single-event mask. -/
theorem rows_valid : wellFormed rowsFrom0 = true := by decide

/-- Numeric arrays and the concatenated row data agree exactly. -/
theorem numeric_data : rowsFrom0.map markedData = targetData.toList := by
  rw [mappedFrom0]
  rfl

/-- The only outstanding premise is equality of the embedded file with
these checked text lines. This is not proved by the generator hash. -/
theorem literal_binding
    (htext : literal = String.ofList (linesChars (header ++ linesFrom0))) :
    Shared.PNP.Record285.parse = some rowsFrom0 ∧
      rowsFrom0.map markedData = targetData.toList :=
  ⟨parse_of_lines linesFrom0 rowsFrom0 cleanFrom0 parsedFrom0 htext, numeric_data⟩

end Shared.PNP.Record285.TextCertificate
