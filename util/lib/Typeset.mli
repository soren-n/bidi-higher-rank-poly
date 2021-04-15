type attr =
  { pad : bool
  ; fix : bool
  }

type eDSL =
  | UNull
  | UText of string
  | UFix of eDSL
  | UGrp of eDSL
  | USeq of eDSL
  | UNest of eDSL
  | UPack of eDSL
  | ULine of eDSL * eDSL
  | UComp of eDSL * eDSL * attr

val null : eDSL
val text : string -> eDSL
val fix : eDSL -> eDSL
val seq : eDSL -> eDSL
val grp : eDSL -> eDSL
val nest : eDSL -> eDSL
val pack : eDSL -> eDSL

val (~$) : string -> eDSL
val (</>) : eDSL -> eDSL -> eDSL
val (<&>) : eDSL -> eDSL -> eDSL
val (<+>) : eDSL -> eDSL -> eDSL
val (<!&>) : eDSL -> eDSL -> eDSL
val (<!+>) : eDSL -> eDSL -> eDSL
val (<//>) : eDSL -> eDSL -> eDSL

type doc =
  | REOD
  | REmpty of doc
  | RBreak of doc_obj * doc
  | RLine of doc_obj
and doc_obj =
  | RText of string
  | RFix of doc_obj_fix
  | RGrp of doc_obj
  | RSeq of doc_obj
  | RNest of doc_obj
  | RPack of int * doc_obj
  | RComp of doc_obj * doc_obj * bool
and doc_obj_fix =
  | RFText of string
  | RFComp of doc_obj_fix * doc_obj_fix * bool

val compile : eDSL -> (doc -> 'a) -> 'a
val render : doc -> int -> int -> (string -> 'a) -> 'a
val print : doc -> (string -> 'a) -> 'a
