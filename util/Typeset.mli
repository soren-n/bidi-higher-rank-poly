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

type doc =
  | SEOD
  | SLine of doc_obj
  | SEmpty of doc
  | SBreak of doc_obj * doc
and doc_obj =
  | SNull
  | SText of string
  | SFix of doc_obj_fix
  | SGrp of doc_obj
  | SSeq of doc_obj
  | SNest of doc_obj
  | SMark of int * doc_obj
  | SMove of int * doc_obj
  | SComp of doc_obj * doc_obj * bool
and doc_obj_fix =
  | SFNull
  | SFText of string
  | SFMark of int * doc_obj_fix
  | SFMove of int * doc_obj_fix
  | SFComp of doc_obj_fix * doc_obj_fix * bool

val compile : eDSL -> (doc -> 'a) -> 'a
val render : doc -> int -> int -> (string -> 'a) -> 'a
