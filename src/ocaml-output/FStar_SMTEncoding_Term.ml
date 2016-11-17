
open Prims

type sort =
| Bool_sort
| Int_sort
| String_sort
| Ref_sort
| Term_sort
| Fuel_sort
| Array of (sort * sort)
| Arrow of (sort * sort)
| Sort of Prims.string


let is_Bool_sort = (fun _discr_ -> (match (_discr_) with
| Bool_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int_sort = (fun _discr_ -> (match (_discr_) with
| Int_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_String_sort = (fun _discr_ -> (match (_discr_) with
| String_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Ref_sort = (fun _discr_ -> (match (_discr_) with
| Ref_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Term_sort = (fun _discr_ -> (match (_discr_) with
| Term_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Fuel_sort = (fun _discr_ -> (match (_discr_) with
| Fuel_sort (_) -> begin
true
end
| _ -> begin
false
end))


let is_Array = (fun _discr_ -> (match (_discr_) with
| Array (_) -> begin
true
end
| _ -> begin
false
end))


let is_Arrow = (fun _discr_ -> (match (_discr_) with
| Arrow (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sort = (fun _discr_ -> (match (_discr_) with
| Sort (_) -> begin
true
end
| _ -> begin
false
end))


let ___Array____0 = (fun projectee -> (match (projectee) with
| Array (_84_10) -> begin
_84_10
end))


let ___Arrow____0 = (fun projectee -> (match (projectee) with
| Arrow (_84_13) -> begin
_84_13
end))


let ___Sort____0 = (fun projectee -> (match (projectee) with
| Sort (_84_16) -> begin
_84_16
end))


let rec strSort : sort  ->  Prims.string = (fun x -> (match (x) with
| Bool_sort -> begin
"Bool"
end
| Int_sort -> begin
"Int"
end
| Term_sort -> begin
"Term"
end
| String_sort -> begin
"FString"
end
| Ref_sort -> begin
"Ref"
end
| Fuel_sort -> begin
"Fuel"
end
| Array (s1, s2) -> begin
(let _180_52 = (strSort s1)
in (let _180_51 = (strSort s2)
in (FStar_Util.format2 "(Array %s %s)" _180_52 _180_51)))
end
| Arrow (s1, s2) -> begin
(let _180_54 = (strSort s1)
in (let _180_53 = (strSort s2)
in (FStar_Util.format2 "(%s -> %s)" _180_54 _180_53)))
end
| Sort (s) -> begin
s
end))


type op =
| True
| False
| Not
| And
| Or
| Imp
| Iff
| Eq
| LT
| LTE
| GT
| GTE
| Add
| Sub
| Div
| Mul
| Minus
| Mod
| ITE
| Var of Prims.string


let is_True = (fun _discr_ -> (match (_discr_) with
| True (_) -> begin
true
end
| _ -> begin
false
end))


let is_False = (fun _discr_ -> (match (_discr_) with
| False (_) -> begin
true
end
| _ -> begin
false
end))


let is_Not = (fun _discr_ -> (match (_discr_) with
| Not (_) -> begin
true
end
| _ -> begin
false
end))


let is_And = (fun _discr_ -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))


let is_Or = (fun _discr_ -> (match (_discr_) with
| Or (_) -> begin
true
end
| _ -> begin
false
end))


let is_Imp = (fun _discr_ -> (match (_discr_) with
| Imp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Iff = (fun _discr_ -> (match (_discr_) with
| Iff (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eq = (fun _discr_ -> (match (_discr_) with
| Eq (_) -> begin
true
end
| _ -> begin
false
end))


let is_LT = (fun _discr_ -> (match (_discr_) with
| LT (_) -> begin
true
end
| _ -> begin
false
end))


let is_LTE = (fun _discr_ -> (match (_discr_) with
| LTE (_) -> begin
true
end
| _ -> begin
false
end))


let is_GT = (fun _discr_ -> (match (_discr_) with
| GT (_) -> begin
true
end
| _ -> begin
false
end))


let is_GTE = (fun _discr_ -> (match (_discr_) with
| GTE (_) -> begin
true
end
| _ -> begin
false
end))


let is_Add = (fun _discr_ -> (match (_discr_) with
| Add (_) -> begin
true
end
| _ -> begin
false
end))


let is_Sub = (fun _discr_ -> (match (_discr_) with
| Sub (_) -> begin
true
end
| _ -> begin
false
end))


let is_Div = (fun _discr_ -> (match (_discr_) with
| Div (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mul = (fun _discr_ -> (match (_discr_) with
| Mul (_) -> begin
true
end
| _ -> begin
false
end))


let is_Minus = (fun _discr_ -> (match (_discr_) with
| Minus (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mod = (fun _discr_ -> (match (_discr_) with
| Mod (_) -> begin
true
end
| _ -> begin
false
end))


let is_ITE = (fun _discr_ -> (match (_discr_) with
| ITE (_) -> begin
true
end
| _ -> begin
false
end))


let is_Var = (fun _discr_ -> (match (_discr_) with
| Var (_) -> begin
true
end
| _ -> begin
false
end))


let ___Var____0 = (fun projectee -> (match (projectee) with
| Var (_84_36) -> begin
_84_36
end))


type qop =
| Forall
| Exists


let is_Forall = (fun _discr_ -> (match (_discr_) with
| Forall (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exists = (fun _discr_ -> (match (_discr_) with
| Exists (_) -> begin
true
end
| _ -> begin
false
end))


type term' =
| Integer of Prims.string
| BoundV of Prims.int
| FreeV of fv
| App of (op * term Prims.list)
| Quant of (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)
| Labeled of (term * Prims.string * FStar_Range.range)
| LblPos of (term * Prims.string) 
 and term =
{tm : term'; freevars : fvs FStar_Syntax_Syntax.memo; rng : FStar_Range.range} 
 and pat =
term 
 and fv =
(Prims.string * sort) 
 and fvs =
fv Prims.list


let is_Integer = (fun _discr_ -> (match (_discr_) with
| Integer (_) -> begin
true
end
| _ -> begin
false
end))


let is_BoundV = (fun _discr_ -> (match (_discr_) with
| BoundV (_) -> begin
true
end
| _ -> begin
false
end))


let is_FreeV = (fun _discr_ -> (match (_discr_) with
| FreeV (_) -> begin
true
end
| _ -> begin
false
end))


let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))


let is_Quant = (fun _discr_ -> (match (_discr_) with
| Quant (_) -> begin
true
end
| _ -> begin
false
end))


let is_Labeled = (fun _discr_ -> (match (_discr_) with
| Labeled (_) -> begin
true
end
| _ -> begin
false
end))


let is_LblPos = (fun _discr_ -> (match (_discr_) with
| LblPos (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkterm : term  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkterm"))))


let ___Integer____0 = (fun projectee -> (match (projectee) with
| Integer (_84_42) -> begin
_84_42
end))


let ___BoundV____0 = (fun projectee -> (match (projectee) with
| BoundV (_84_45) -> begin
_84_45
end))


let ___FreeV____0 = (fun projectee -> (match (projectee) with
| FreeV (_84_48) -> begin
_84_48
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_84_51) -> begin
_84_51
end))


let ___Quant____0 = (fun projectee -> (match (projectee) with
| Quant (_84_54) -> begin
_84_54
end))


let ___Labeled____0 = (fun projectee -> (match (projectee) with
| Labeled (_84_57) -> begin
_84_57
end))


let ___LblPos____0 = (fun projectee -> (match (projectee) with
| LblPos (_84_60) -> begin
_84_60
end))


type caption =
Prims.string Prims.option


type binders =
(Prims.string * sort) Prims.list


type projector =
(Prims.string * sort)


type constructor_t =
(Prims.string * projector Prims.list * sort * Prims.int * Prims.bool)


type constructors =
constructor_t Prims.list


type decl =
| DefPrelude
| DeclFun of (Prims.string * sort Prims.list * sort * caption)
| DefineFun of (Prims.string * sort Prims.list * sort * term * caption)
| Assume of (term * caption * Prims.string Prims.option)
| Caption of Prims.string
| Eval of term
| Echo of Prims.string
| Push
| Pop
| CheckSat
| GetUnsatCore
| SetOption of (Prims.string * Prims.string)


let is_DefPrelude = (fun _discr_ -> (match (_discr_) with
| DefPrelude (_) -> begin
true
end
| _ -> begin
false
end))


let is_DeclFun = (fun _discr_ -> (match (_discr_) with
| DeclFun (_) -> begin
true
end
| _ -> begin
false
end))


let is_DefineFun = (fun _discr_ -> (match (_discr_) with
| DefineFun (_) -> begin
true
end
| _ -> begin
false
end))


let is_Assume = (fun _discr_ -> (match (_discr_) with
| Assume (_) -> begin
true
end
| _ -> begin
false
end))


let is_Caption = (fun _discr_ -> (match (_discr_) with
| Caption (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eval = (fun _discr_ -> (match (_discr_) with
| Eval (_) -> begin
true
end
| _ -> begin
false
end))


let is_Echo = (fun _discr_ -> (match (_discr_) with
| Echo (_) -> begin
true
end
| _ -> begin
false
end))


let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))


let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))


let is_CheckSat = (fun _discr_ -> (match (_discr_) with
| CheckSat (_) -> begin
true
end
| _ -> begin
false
end))


let is_GetUnsatCore = (fun _discr_ -> (match (_discr_) with
| GetUnsatCore (_) -> begin
true
end
| _ -> begin
false
end))


let is_SetOption = (fun _discr_ -> (match (_discr_) with
| SetOption (_) -> begin
true
end
| _ -> begin
false
end))


let ___DeclFun____0 = (fun projectee -> (match (projectee) with
| DeclFun (_84_64) -> begin
_84_64
end))


let ___DefineFun____0 = (fun projectee -> (match (projectee) with
| DefineFun (_84_67) -> begin
_84_67
end))


let ___Assume____0 = (fun projectee -> (match (projectee) with
| Assume (_84_70) -> begin
_84_70
end))


let ___Caption____0 = (fun projectee -> (match (projectee) with
| Caption (_84_73) -> begin
_84_73
end))


let ___Eval____0 = (fun projectee -> (match (projectee) with
| Eval (_84_76) -> begin
_84_76
end))


let ___Echo____0 = (fun projectee -> (match (projectee) with
| Echo (_84_79) -> begin
_84_79
end))


let ___SetOption____0 = (fun projectee -> (match (projectee) with
| SetOption (_84_82) -> begin
_84_82
end))


type decls_t =
decl Prims.list


type error_label =
(fv * Prims.string * FStar_Range.range)


type error_labels =
error_label Prims.list


let fv_eq : fv  ->  fv  ->  Prims.bool = (fun x y -> ((Prims.fst x) = (Prims.fst y)))


let fv_sort = (fun x -> (Prims.snd x))


let freevar_eq : term  ->  term  ->  Prims.bool = (fun x y -> (match (((x.tm), (y.tm))) with
| (FreeV (x), FreeV (y)) -> begin
(fv_eq x y)
end
| _84_94 -> begin
false
end))


let freevar_sort : term  ->  sort = (fun _84_1 -> (match (_84_1) with
| {tm = FreeV (x); freevars = _84_99; rng = _84_97} -> begin
(fv_sort x)
end
| _84_104 -> begin
(FStar_All.failwith "impossible")
end))


let fv_of_term : term  ->  fv = (fun _84_2 -> (match (_84_2) with
| {tm = FreeV (fv); freevars = _84_109; rng = _84_107} -> begin
fv
end
| _84_114 -> begin
(FStar_All.failwith "impossible")
end))


let rec freevars : term  ->  fv Prims.list = (fun t -> (match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
[]
end
| FreeV (fv) -> begin
(fv)::[]
end
| App (_84_125, tms) -> begin
(FStar_List.collect freevars tms)
end
| (Quant (_, _, _, _, t)) | (Labeled (t, _, _)) | (LblPos (t, _)) -> begin
(freevars t)
end))


let free_variables : term  ->  fvs = (fun t -> (match ((FStar_ST.read t.freevars)) with
| Some (b) -> begin
b
end
| None -> begin
(

let fvs = (let _180_318 = (freevars t)
in (FStar_Util.remove_dups fv_eq _180_318))
in (

let _84_155 = (FStar_ST.op_Colon_Equals t.freevars (Some (fvs)))
in fvs))
end))


let qop_to_string : qop  ->  Prims.string = (fun _84_3 -> (match (_84_3) with
| Forall -> begin
"forall"
end
| Exists -> begin
"exists"
end))


let op_to_string : op  ->  Prims.string = (fun _84_4 -> (match (_84_4) with
| True -> begin
"true"
end
| False -> begin
"false"
end
| Not -> begin
"not"
end
| And -> begin
"and"
end
| Or -> begin
"or"
end
| Imp -> begin
"implies"
end
| Iff -> begin
"iff"
end
| Eq -> begin
"="
end
| LT -> begin
"<"
end
| LTE -> begin
"<="
end
| GT -> begin
">"
end
| GTE -> begin
">="
end
| Add -> begin
"+"
end
| Sub -> begin
"-"
end
| Div -> begin
"div"
end
| Mul -> begin
"*"
end
| Minus -> begin
"-"
end
| Mod -> begin
"mod"
end
| ITE -> begin
"ite"
end
| Var (s) -> begin
s
end))


let weightToSmt : Prims.int Prims.option  ->  Prims.string = (fun _84_5 -> (match (_84_5) with
| None -> begin
""
end
| Some (i) -> begin
(let _180_325 = (FStar_Util.string_of_int i)
in (FStar_Util.format1 ":weight %s\n" _180_325))
end))


let rec hash_of_term' : term'  ->  Prims.string = (fun t -> (match (t) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _180_329 = (FStar_Util.string_of_int i)
in (Prims.strcat "@" _180_329))
end
| FreeV (x) -> begin
(let _180_331 = (let _180_330 = (strSort (Prims.snd x))
in (Prims.strcat ":" _180_330))
in (Prims.strcat (Prims.fst x) _180_331))
end
| App (op, tms) -> begin
(let _180_335 = (let _180_334 = (let _180_333 = (let _180_332 = (FStar_List.map hash_of_term tms)
in (FStar_All.pipe_right _180_332 (FStar_String.concat " ")))
in (Prims.strcat _180_333 ")"))
in (Prims.strcat (op_to_string op) _180_334))
in (Prims.strcat "(" _180_335))
end
| Labeled (t, r1, r2) -> begin
(let _180_338 = (hash_of_term t)
in (let _180_337 = (let _180_336 = (FStar_Range.string_of_range r2)
in (Prims.strcat r1 _180_336))
in (Prims.strcat _180_338 _180_337)))
end
| LblPos (t, r) -> begin
(let _180_340 = (let _180_339 = (hash_of_term t)
in (Prims.strcat _180_339 (Prims.strcat " :lblpos " (Prims.strcat r ")"))))
in (Prims.strcat "(! " _180_340))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(let _180_357 = (let _180_356 = (let _180_355 = (let _180_354 = (let _180_341 = (FStar_List.map strSort sorts)
in (FStar_All.pipe_right _180_341 (FStar_String.concat " ")))
in (let _180_353 = (let _180_352 = (let _180_351 = (hash_of_term body)
in (let _180_350 = (let _180_349 = (let _180_348 = (weightToSmt wopt)
in (let _180_347 = (let _180_346 = (let _180_345 = (let _180_344 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _180_343 = (FStar_List.map hash_of_term pats)
in (FStar_All.pipe_right _180_343 (FStar_String.concat " "))))))
in (FStar_All.pipe_right _180_344 (FStar_String.concat "; ")))
in (Prims.strcat _180_345 "))"))
in (Prims.strcat " " _180_346))
in (Prims.strcat _180_348 _180_347)))
in (Prims.strcat " " _180_349))
in (Prims.strcat _180_351 _180_350)))
in (Prims.strcat ")(! " _180_352))
in (Prims.strcat _180_354 _180_353)))
in (Prims.strcat " (" _180_355))
in (Prims.strcat (qop_to_string qop) _180_356))
in (Prims.strcat "(" _180_357))
end))
and hash_of_term : term  ->  Prims.string = (fun tm -> (hash_of_term' tm.tm))


let mk : term'  ->  FStar_Range.range  ->  term = (fun t r -> (let _180_363 = (FStar_Util.mk_ref None)
in {tm = t; freevars = _180_363; rng = r}))


let mkTrue : FStar_Range.range  ->  term = (fun r -> (mk (App (((True), ([])))) r))


let mkFalse : FStar_Range.range  ->  term = (fun r -> (mk (App (((False), ([])))) r))


let mkInteger : Prims.string  ->  FStar_Range.range  ->  term = (fun i r -> (let _180_373 = (let _180_372 = (FStar_Util.ensure_decimal i)
in Integer (_180_372))
in (mk _180_373 r)))


let mkInteger' : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _180_378 = (FStar_Util.string_of_int i)
in (mkInteger _180_378 r)))


let mkBoundV : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (mk (BoundV (i)) r))


let mkFreeV : (Prims.string * sort)  ->  FStar_Range.range  ->  term = (fun x r -> (mk (FreeV (x)) r))


let mkApp' : (op * term Prims.list)  ->  FStar_Range.range  ->  term = (fun f r -> (mk (App (f)) r))


let mkApp : (Prims.string * term Prims.list)  ->  FStar_Range.range  ->  term = (fun _84_231 r -> (match (_84_231) with
| (s, args) -> begin
(mk (App (((Var (s)), (args)))) r)
end))


let mkNot : term  ->  FStar_Range.range  ->  term = (fun t r -> (match (t.tm) with
| App (True, _84_237) -> begin
(mkFalse r)
end
| App (False, _84_242) -> begin
(mkTrue r)
end
| _84_246 -> begin
(mkApp' ((Not), ((t)::[])) r)
end))


let mkAnd : (term * term)  ->  FStar_Range.range  ->  term = (fun _84_249 r -> (match (_84_249) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| (App (True, _84_253), _84_257) -> begin
t2
end
| (_84_260, App (True, _84_263)) -> begin
t1
end
| ((App (False, _), _)) | ((_, App (False, _))) -> begin
(mkFalse r)
end
| (App (And, ts1), App (And, ts2)) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ts2))) r)
end
| (_84_293, App (And, ts2)) -> begin
(mkApp' ((And), ((t1)::ts2)) r)
end
| (App (And, ts1), _84_304) -> begin
(mkApp' ((And), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _84_307 -> begin
(mkApp' ((And), ((t1)::(t2)::[])) r)
end)
end))


let mkOr : (term * term)  ->  FStar_Range.range  ->  term = (fun _84_310 r -> (match (_84_310) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((App (True, _), _)) | ((_, App (True, _))) -> begin
(mkTrue r)
end
| (App (False, _84_330), _84_334) -> begin
t2
end
| (_84_337, App (False, _84_340)) -> begin
t1
end
| (App (Or, ts1), App (Or, ts2)) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ts2))) r)
end
| (_84_354, App (Or, ts2)) -> begin
(mkApp' ((Or), ((t1)::ts2)) r)
end
| (App (Or, ts1), _84_365) -> begin
(mkApp' ((Or), ((FStar_List.append ts1 ((t2)::[])))) r)
end
| _84_368 -> begin
(mkApp' ((Or), ((t1)::(t2)::[])) r)
end)
end))


let mkImp : (term * term)  ->  FStar_Range.range  ->  term = (fun _84_371 r -> (match (_84_371) with
| (t1, t2) -> begin
(match (((t1.tm), (t2.tm))) with
| ((_, App (True, _))) | ((App (False, _), _)) -> begin
(mkTrue r)
end
| (App (True, _84_391), _84_395) -> begin
t2
end
| (_84_398, App (Imp, (t1')::(t2')::[])) -> begin
(let _180_413 = (let _180_412 = (let _180_411 = (mkAnd ((t1), (t1')) r)
in (_180_411)::(t2')::[])
in ((Imp), (_180_412)))
in (mkApp' _180_413 r))
end
| _84_407 -> begin
(mkApp' ((Imp), ((t1)::(t2)::[])) r)
end)
end))


let mk_bin_op : op  ->  (term * term)  ->  FStar_Range.range  ->  term = (fun op _84_411 r -> (match (_84_411) with
| (t1, t2) -> begin
(mkApp' ((op), ((t1)::(t2)::[])) r)
end))


let mkMinus : term  ->  FStar_Range.range  ->  term = (fun t r -> (mkApp' ((Minus), ((t)::[])) r))


let mkIff : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Iff)


let mkEq : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Eq)


let mkLT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LT)


let mkLTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op LTE)


let mkGT : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GT)


let mkGTE : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op GTE)


let mkAdd : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Add)


let mkSub : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Sub)


let mkDiv : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Div)


let mkMul : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mul)


let mkMod : (term * term)  ->  FStar_Range.range  ->  term = (mk_bin_op Mod)


let mkITE : (term * term * term)  ->  FStar_Range.range  ->  term = (fun _84_418 r -> (match (_84_418) with
| (t1, t2, t3) -> begin
(match (((t2.tm), (t3.tm))) with
| (App (True, _84_422), App (True, _84_427)) -> begin
(mkTrue r)
end
| (App (True, _84_433), _84_437) -> begin
(let _180_451 = (let _180_450 = (mkNot t1 t1.rng)
in ((_180_450), (t3)))
in (mkImp _180_451 r))
end
| (_84_440, App (True, _84_443)) -> begin
(mkImp ((t1), (t2)) r)
end
| (_84_448, _84_450) -> begin
(mkApp' ((ITE), ((t1)::(t2)::(t3)::[])) r)
end)
end))


let mkCases : term Prims.list  ->  FStar_Range.range  ->  term = (fun t r -> (match (t) with
| [] -> begin
(FStar_All.failwith "Impos")
end
| (hd)::tl -> begin
(FStar_List.fold_left (fun out t -> (mkAnd ((out), (t)) r)) hd tl)
end))


let mkQuant : (qop * pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _84_465 r -> (match (_84_465) with
| (qop, pats, wopt, vars, body) -> begin
if ((FStar_List.length vars) = (Prims.parse_int "0")) then begin
body
end else begin
(match (body.tm) with
| App (True, _84_469) -> begin
body
end
| _84_473 -> begin
(mk (Quant (((qop), (pats), (wopt), (vars), (body)))) r)
end)
end
end))


let abstr : fv Prims.list  ->  term  ->  term = (fun fvs t -> (

let nvars = (FStar_List.length fvs)
in (

let index_of = (fun fv -> (match ((FStar_Util.try_find_index (fv_eq fv) fvs)) with
| None -> begin
None
end
| Some (i) -> begin
Some ((nvars - (i + (Prims.parse_int "1"))))
end))
in (

let rec aux = (fun ix t -> (match ((FStar_ST.read t.freevars)) with
| Some ([]) -> begin
t
end
| _84_488 -> begin
(match (t.tm) with
| (Integer (_)) | (BoundV (_)) -> begin
t
end
| FreeV (x) -> begin
(match ((index_of x)) with
| None -> begin
t
end
| Some (i) -> begin
(mkBoundV (i + ix) t.rng)
end)
end
| App (op, tms) -> begin
(let _180_473 = (let _180_472 = (FStar_List.map (aux ix) tms)
in ((op), (_180_472)))
in (mkApp' _180_473 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _180_476 = (let _180_475 = (let _180_474 = (aux ix t)
in ((_180_474), (r1), (r2)))
in Labeled (_180_475))
in (mk _180_476 t.rng))
end
| LblPos (t, r) -> begin
(let _180_479 = (let _180_478 = (let _180_477 = (aux ix t)
in ((_180_477), (r)))
in LblPos (_180_478))
in (mk _180_479 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let n = (FStar_List.length vars)
in (let _180_482 = (let _180_481 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux (ix + n)))))
in (let _180_480 = (aux (ix + n) body)
in ((qop), (_180_481), (wopt), (vars), (_180_480))))
in (mkQuant _180_482 t.rng)))
end)
end))
in (aux (Prims.parse_int "0") t)))))


let inst : term Prims.list  ->  term  ->  term = (fun tms t -> (

let tms = (FStar_List.rev tms)
in (

let n = (FStar_List.length tms)
in (

let rec aux = (fun shift t -> (match (t.tm) with
| (Integer (_)) | (FreeV (_)) -> begin
t
end
| BoundV (i) -> begin
if (((Prims.parse_int "0") <= (i - shift)) && ((i - shift) < n)) then begin
(FStar_List.nth tms (i - shift))
end else begin
t
end
end
| App (op, tms) -> begin
(let _180_492 = (let _180_491 = (FStar_List.map (aux shift) tms)
in ((op), (_180_491)))
in (mkApp' _180_492 t.rng))
end
| Labeled (t, r1, r2) -> begin
(let _180_495 = (let _180_494 = (let _180_493 = (aux shift t)
in ((_180_493), (r1), (r2)))
in Labeled (_180_494))
in (mk _180_495 t.rng))
end
| LblPos (t, r) -> begin
(let _180_498 = (let _180_497 = (let _180_496 = (aux shift t)
in ((_180_496), (r)))
in LblPos (_180_497))
in (mk _180_498 t.rng))
end
| Quant (qop, pats, wopt, vars, body) -> begin
(

let m = (FStar_List.length vars)
in (

let shift = (shift + m)
in (let _180_501 = (let _180_500 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (aux shift))))
in (let _180_499 = (aux shift body)
in ((qop), (_180_500), (wopt), (vars), (_180_499))))
in (mkQuant _180_501 t.rng))))
end))
in (aux (Prims.parse_int "0") t)))))


let mkQuant' : (qop * term Prims.list Prims.list * Prims.int Prims.option * fv Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _84_563 -> (match (_84_563) with
| (qop, pats, wopt, vars, body) -> begin
(let _180_512 = (let _180_511 = (FStar_All.pipe_right pats (FStar_List.map (FStar_List.map (abstr vars))))
in (let _180_510 = (FStar_List.map fv_sort vars)
in (let _180_509 = (abstr vars body)
in ((qop), (_180_511), (wopt), (_180_510), (_180_509)))))
in (mkQuant _180_512))
end))


let mkForall'' : (pat Prims.list Prims.list * Prims.int Prims.option * sort Prims.list * term)  ->  FStar_Range.range  ->  term = (fun _84_568 r -> (match (_84_568) with
| (pats, wopt, sorts, body) -> begin
(mkQuant ((Forall), (pats), (wopt), (sorts), (body)) r)
end))


let mkForall' : (pat Prims.list Prims.list * Prims.int Prims.option * fvs * term)  ->  FStar_Range.range  ->  term = (fun _84_574 r -> (match (_84_574) with
| (pats, wopt, vars, body) -> begin
(mkQuant' ((Forall), (pats), (wopt), (vars), (body)) r)
end))


let mkForall : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _84_579 r -> (match (_84_579) with
| (pats, vars, body) -> begin
(mkQuant' ((Forall), (pats), (None), (vars), (body)) r)
end))


let mkExists : (pat Prims.list Prims.list * fvs * term)  ->  FStar_Range.range  ->  term = (fun _84_584 r -> (match (_84_584) with
| (pats, vars, body) -> begin
(mkQuant' ((Exists), (pats), (None), (vars), (body)) r)
end))


let norng : FStar_Range.range = FStar_Range.dummyRange


let mkDefineFun : (Prims.string * (Prims.string * sort) Prims.list * sort * term * caption)  ->  decl = (fun _84_591 -> (match (_84_591) with
| (nm, vars, s, tm, c) -> begin
(let _180_533 = (let _180_532 = (FStar_List.map fv_sort vars)
in (let _180_531 = (abstr vars tm)
in ((nm), (_180_532), (s), (_180_531), (c))))
in DefineFun (_180_533))
end))


let constr_id_of_sort : sort  ->  Prims.string = (fun sort -> (let _180_536 = (strSort sort)
in (FStar_Util.format1 "%s_constr_id" _180_536)))


let fresh_token : (Prims.string * sort)  ->  Prims.int  ->  decl = (fun _84_595 id -> (match (_84_595) with
| (tok_name, sort) -> begin
(

let a_name = (Prims.strcat "fresh_token_" tok_name)
in (let _180_549 = (let _180_548 = (let _180_547 = (let _180_546 = (mkInteger' id norng)
in (let _180_545 = (let _180_544 = (let _180_543 = (constr_id_of_sort sort)
in (let _180_542 = (let _180_541 = (mkApp ((tok_name), ([])) norng)
in (_180_541)::[])
in ((_180_543), (_180_542))))
in (mkApp _180_544 norng))
in ((_180_546), (_180_545))))
in (mkEq _180_547 norng))
in ((_180_548), (Some ("fresh token")), (Some (a_name))))
in Assume (_180_549)))
end))


let fresh_constructor : (Prims.string * sort Prims.list * sort * Prims.int)  ->  decl = (fun _84_602 -> (match (_84_602) with
| (name, arg_sorts, sort, id) -> begin
(

let id = (FStar_Util.string_of_int id)
in (

let bvars = (FStar_All.pipe_right arg_sorts (FStar_List.mapi (fun i s -> (let _180_556 = (let _180_555 = (let _180_554 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _180_554))
in ((_180_555), (s)))
in (mkFreeV _180_556 norng)))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (

let cid_app = (let _180_558 = (let _180_557 = (constr_id_of_sort sort)
in ((_180_557), ((capp)::[])))
in (mkApp _180_558 norng))
in (

let a_name = (Prims.strcat "constructor_distinct_" name)
in (let _180_564 = (let _180_563 = (let _180_562 = (let _180_561 = (let _180_560 = (let _180_559 = (mkInteger id norng)
in ((_180_559), (cid_app)))
in (mkEq _180_560 norng))
in ((((capp)::[])::[]), (bvar_names), (_180_561)))
in (mkForall _180_562 norng))
in ((_180_563), (Some ("Constructor distinct")), (Some (a_name))))
in Assume (_180_564))))))))
end))


let injective_constructor : (Prims.string * (Prims.string * sort) Prims.list * sort)  ->  decls_t = (fun _84_614 -> (match (_84_614) with
| (name, projectors, sort) -> begin
(

let n_bvars = (FStar_List.length projectors)
in (

let bvar_name = (fun i -> (let _180_569 = (FStar_Util.string_of_int i)
in (Prims.strcat "x_" _180_569)))
in (

let bvar_index = (fun i -> (n_bvars - (i + (Prims.parse_int "1"))))
in (

let bvar = (fun i s -> (let _180_581 = (let _180_580 = (bvar_name i)
in ((_180_580), (s)))
in (mkFreeV _180_581)))
in (

let bvars = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _84_627 -> (match (_84_627) with
| (_84_625, s) -> begin
(bvar i s norng)
end))))
in (

let bvar_names = (FStar_List.map fv_of_term bvars)
in (

let capp = (mkApp ((name), (bvars)) norng)
in (let _180_594 = (FStar_All.pipe_right projectors (FStar_List.mapi (fun i _84_634 -> (match (_84_634) with
| (name, s) -> begin
(

let cproj_app = (mkApp ((name), ((capp)::[])) norng)
in (

let proj_name = DeclFun (((name), ((sort)::[]), (s), (Some ("Projector"))))
in (

let a_name = (Prims.strcat "projection_inverse_" name)
in (let _180_593 = (let _180_592 = (let _180_591 = (let _180_590 = (let _180_589 = (let _180_588 = (let _180_587 = (let _180_586 = (bvar i s norng)
in ((cproj_app), (_180_586)))
in (mkEq _180_587 norng))
in ((((capp)::[])::[]), (bvar_names), (_180_588)))
in (mkForall _180_589 norng))
in ((_180_590), (Some ("Projection inverse")), (Some (a_name))))
in Assume (_180_591))
in (_180_592)::[])
in (proj_name)::_180_593))))
end))))
in (FStar_All.pipe_right _180_594 FStar_List.flatten)))))))))
end))


let constructor_to_decl : constructor_t  ->  decls_t = (fun _84_643 -> (match (_84_643) with
| (name, projectors, sort, id, injective) -> begin
(

let injective = (injective || true)
in (

let cdecl = (let _180_598 = (let _180_597 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_180_597), (sort), (Some ("Constructor"))))
in DeclFun (_180_598))
in (

let cid = (let _180_600 = (let _180_599 = (FStar_All.pipe_right projectors (FStar_List.map Prims.snd))
in ((name), (_180_599), (sort), (id)))
in (fresh_constructor _180_600))
in (

let disc = (

let disc_name = (Prims.strcat "is-" name)
in (

let xfv = (("x"), (sort))
in (

let xx = (mkFreeV xfv norng)
in (

let disc_eq = (let _180_606 = (let _180_605 = (let _180_602 = (let _180_601 = (constr_id_of_sort sort)
in ((_180_601), ((xx)::[])))
in (mkApp _180_602 norng))
in (let _180_604 = (let _180_603 = (FStar_Util.string_of_int id)
in (mkInteger _180_603 norng))
in ((_180_605), (_180_604))))
in (mkEq _180_606 norng))
in (

let proj_terms = (FStar_All.pipe_right projectors (FStar_List.map (fun _84_653 -> (match (_84_653) with
| (proj, s) -> begin
(mkApp ((proj), ((xx)::[])) norng)
end))))
in (

let disc_inv_body = (let _180_609 = (let _180_608 = (mkApp ((name), (proj_terms)) norng)
in ((xx), (_180_608)))
in (mkEq _180_609 norng))
in (

let disc_ax = (mkAnd ((disc_eq), (disc_inv_body)) norng)
in (mkDefineFun ((disc_name), ((xfv)::[]), (Bool_sort), (disc_ax), (Some ("Discriminator definition")))))))))))
in (

let projs = if injective then begin
(injective_constructor ((name), (projectors), (sort)))
end else begin
[]
end
in (let _180_616 = (let _180_611 = (let _180_610 = (FStar_Util.format1 "<start constructor %s>" name)
in Caption (_180_610))
in (_180_611)::(cdecl)::(cid)::projs)
in (let _180_615 = (let _180_614 = (let _180_613 = (let _180_612 = (FStar_Util.format1 "</end constructor %s>" name)
in Caption (_180_612))
in (_180_613)::[])
in (FStar_List.append ((disc)::[]) _180_614))
in (FStar_List.append _180_616 _180_615))))))))
end))


let name_binders_inner : (Prims.string * sort) Prims.list  ->  Prims.int  ->  sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list * Prims.int) = (fun outer_names start sorts -> (

let _84_677 = (FStar_All.pipe_right sorts (FStar_List.fold_left (fun _84_665 s -> (match (_84_665) with
| (names, binders, n) -> begin
(

let prefix = (match (s) with
| Term_sort -> begin
"@x"
end
| _84_669 -> begin
"@u"
end)
in (

let nm = (let _180_625 = (FStar_Util.string_of_int n)
in (Prims.strcat prefix _180_625))
in (

let names = (((nm), (s)))::names
in (

let b = (let _180_626 = (strSort s)
in (FStar_Util.format2 "(%s %s)" nm _180_626))
in ((names), ((b)::binders), ((n + (Prims.parse_int "1"))))))))
end)) ((outer_names), ([]), (start))))
in (match (_84_677) with
| (names, binders, n) -> begin
((names), ((FStar_List.rev binders)), (n))
end)))


let name_binders : sort Prims.list  ->  ((Prims.string * sort) Prims.list * Prims.string Prims.list) = (fun sorts -> (

let _84_682 = (name_binders_inner [] (Prims.parse_int "0") sorts)
in (match (_84_682) with
| (names, binders, n) -> begin
(((FStar_List.rev names)), (binders))
end)))


let termToSmt : term  ->  Prims.string = (fun t -> (

let remove_guard_free = (fun pats -> (FStar_All.pipe_right pats (FStar_List.map (fun ps -> (FStar_All.pipe_right ps (FStar_List.map (fun tm -> (match (tm.tm) with
| App (Var ("Prims.guard_free"), ({tm = BoundV (_84_695); freevars = _84_693; rng = _84_691})::[]) -> begin
tm
end
| App (Var ("Prims.guard_free"), (p)::[]) -> begin
p
end
| _84_708 -> begin
tm
end))))))))
in (

let rec aux' = (fun n names t -> (match (t.tm) with
| Integer (i) -> begin
i
end
| BoundV (i) -> begin
(let _180_644 = (FStar_List.nth names i)
in (FStar_All.pipe_right _180_644 Prims.fst))
end
| FreeV (x) -> begin
(Prims.fst x)
end
| App (op, []) -> begin
(op_to_string op)
end
| App (op, tms) -> begin
(let _180_646 = (let _180_645 = (FStar_List.map (aux n names) tms)
in (FStar_All.pipe_right _180_645 (FStar_String.concat "\n")))
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _180_646))
end
| Labeled (t, _84_730, _84_732) -> begin
(aux n names t)
end
| LblPos (t, s) -> begin
(let _180_647 = (aux n names t)
in (FStar_Util.format2 "(! %s :lblpos %s)" _180_647 s))
end
| Quant (qop, pats, wopt, sorts, body) -> begin
(

let _84_749 = (name_binders_inner names n sorts)
in (match (_84_749) with
| (names, binders, n) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_String.concat " "))
in (

let pats = (remove_guard_free pats)
in (

let pats_str = (match (pats) with
| (([])::[]) | ([]) -> begin
""
end
| _84_756 -> begin
(let _180_653 = (FStar_All.pipe_right pats (FStar_List.map (fun pats -> (let _180_652 = (let _180_651 = (FStar_List.map (fun p -> (let _180_650 = (aux n names p)
in (FStar_Util.format1 "%s" _180_650))) pats)
in (FStar_String.concat " " _180_651))
in (FStar_Util.format1 "\n:pattern (%s)" _180_652)))))
in (FStar_All.pipe_right _180_653 (FStar_String.concat "\n")))
end)
in (match (((pats), (wopt))) with
| ((([])::[], None)) | (([], None)) -> begin
(let _180_654 = (aux n names body)
in (FStar_Util.format3 "(%s (%s)\n %s);;no pats\n" (qop_to_string qop) binders _180_654))
end
| _84_768 -> begin
(let _180_656 = (aux n names body)
in (let _180_655 = (weightToSmt wopt)
in (FStar_Util.format5 "(%s (%s)\n (! %s\n %s %s))" (qop_to_string qop) binders _180_656 _180_655 pats_str)))
end))))
end))
end))
and aux = (fun n names t -> (

let s = (aux' n names t)
in if (t.rng <> norng) then begin
(let _180_661 = (FStar_Range.string_of_range t.rng)
in (let _180_660 = (FStar_Range.string_of_use_range t.rng)
in (FStar_Util.format3 "\n;; def=%s; use=%s\n%s\n" _180_661 _180_660 s)))
end else begin
s
end))
in (aux (Prims.parse_int "0") [] t))))


let caption_to_string : Prims.string Prims.option  ->  Prims.string = (fun _84_6 -> (match (_84_6) with
| None -> begin
""
end
| Some (c) -> begin
(

let _84_786 = (match ((FStar_Util.splitlines c)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::[] -> begin
((hd), (""))
end
| (hd)::_84_781 -> begin
((hd), ("..."))
end)
in (match (_84_786) with
| (hd, suffix) -> begin
(FStar_Util.format2 ";;;;;;;;;;;;;;;;%s%s\n" hd suffix)
end))
end))


let rec declToSmt : Prims.string  ->  decl  ->  Prims.string = (fun z3options decl -> (

let escape = (fun s -> (FStar_Util.replace_char s '\'' '_'))
in (match (decl) with
| DefPrelude -> begin
(mkPrelude z3options)
end
| Caption (c) -> begin
(let _180_672 = (FStar_All.pipe_right (FStar_Util.splitlines c) (fun _84_7 -> (match (_84_7) with
| [] -> begin
""
end
| (h)::t -> begin
h
end)))
in (FStar_Util.format1 "\n; %s" _180_672))
end
| DeclFun (f, argsorts, retsort, c) -> begin
(

let l = (FStar_List.map strSort argsorts)
in (let _180_674 = (caption_to_string c)
in (let _180_673 = (strSort retsort)
in (FStar_Util.format4 "%s(declare-fun %s (%s) %s)" _180_674 f (FStar_String.concat " " l) _180_673))))
end
| DefineFun (f, arg_sorts, retsort, body, c) -> begin
(

let _84_815 = (name_binders arg_sorts)
in (match (_84_815) with
| (names, binders) -> begin
(

let body = (let _180_676 = (FStar_List.map (fun x -> (mkFreeV x norng)) names)
in (inst _180_676 body))
in (let _180_679 = (caption_to_string c)
in (let _180_678 = (strSort retsort)
in (let _180_677 = (termToSmt body)
in (FStar_Util.format5 "%s(define-fun %s (%s) %s\n %s)" _180_679 f (FStar_String.concat " " binders) _180_678 _180_677)))))
end))
end
| Assume (t, c, Some (n)) -> begin
(let _180_681 = (caption_to_string c)
in (let _180_680 = (termToSmt t)
in (FStar_Util.format3 "%s(assert (!\n%s\n:named %s))" _180_681 _180_680 (escape n))))
end
| Assume (t, c, None) -> begin
(let _180_683 = (caption_to_string c)
in (let _180_682 = (termToSmt t)
in (FStar_Util.format2 "%s(assert %s)" _180_683 _180_682)))
end
| Eval (t) -> begin
(let _180_684 = (termToSmt t)
in (FStar_Util.format1 "(eval %s)" _180_684))
end
| Echo (s) -> begin
(FStar_Util.format1 "(echo \"%s\")" s)
end
| CheckSat -> begin
"(check-sat)"
end
| GetUnsatCore -> begin
"(echo \"<unsat-core>\")\n(get-unsat-core)\n(echo \"</unsat-core>\")"
end
| Push -> begin
"(push)"
end
| Pop -> begin
"(pop)"
end
| SetOption (s, v) -> begin
(FStar_Util.format2 "(set-option :%s %s)" s v)
end)))
and mkPrelude : Prims.string  ->  Prims.string = (fun z3options -> (

let basic = (Prims.strcat z3options "(declare-sort Ref)\n(declare-fun Ref_constr_id (Ref) Int)\n\n(declare-sort FString)\n(declare-fun FString_constr_id (FString) Int)\n\n(declare-sort Term)\n(declare-fun Term_constr_id (Term) Int)\n(declare-datatypes () ((Fuel \n(ZFuel) \n(SFuel (prec Fuel)))))\n(declare-fun MaxIFuel () Fuel)\n(declare-fun MaxFuel () Fuel)\n(declare-fun PreType (Term) Term)\n(declare-fun Valid (Term) Bool)\n(declare-fun HasTypeFuel (Fuel Term Term) Bool)\n(define-fun HasTypeZ ((x Term) (t Term)) Bool\n(HasTypeFuel ZFuel x t))\n(define-fun HasType ((x Term) (t Term)) Bool\n(HasTypeFuel MaxIFuel x t))\n;;fuel irrelevance\n(assert (forall ((f Fuel) (x Term) (t Term))\n(! (= (HasTypeFuel (SFuel f) x t)\n(HasTypeZ x t))\n:pattern ((HasTypeFuel (SFuel f) x t)))))\n(define-fun  IsTyped ((x Term)) Bool\n(exists ((t Term)) (HasTypeZ x t)))\n(declare-fun ApplyTF (Term Fuel) Term)\n(declare-fun ApplyTT (Term Term) Term)\n(declare-fun Rank (Term) Int)\n(declare-fun Closure (Term) Term)\n(declare-fun ConsTerm (Term Term) Term)\n(declare-fun ConsFuel (Fuel Term) Term)\n(declare-fun Precedes (Term Term) Term)\n(define-fun Reify ((x Term)) Term x)\n(assert (forall ((t Term))\n(! (implies (exists ((e Term)) (HasType e t))\n(Valid t))\n:pattern ((Valid t)))))\n(assert (forall ((t1 Term) (t2 Term))\n(! (iff (Valid (Precedes t1 t2)) \n(< (Rank t1) (Rank t2)))\n:pattern ((Precedes t1 t2)))))\n(define-fun Prims.precedes ((a Term) (b Term) (t1 Term) (t2 Term)) Term\n(Precedes t1 t2))\n(declare-fun Range_const () Term)\n")
in (

let constrs = ((("FString_const"), (((("FString_const_proj_0"), (Int_sort)))::[]), (String_sort), ((Prims.parse_int "0")), (true)))::((("Tm_type"), ([]), (Term_sort), ((Prims.parse_int "2")), (true)))::((("Tm_arrow"), (((("Tm_arrow_id"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "3")), (false)))::((("Tm_uvar"), (((("Tm_uvar_fst"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "5")), (true)))::((("Tm_unit"), ([]), (Term_sort), ((Prims.parse_int "6")), (true)))::((("BoxInt"), (((("BoxInt_proj_0"), (Int_sort)))::[]), (Term_sort), ((Prims.parse_int "7")), (true)))::((("BoxBool"), (((("BoxBool_proj_0"), (Bool_sort)))::[]), (Term_sort), ((Prims.parse_int "8")), (true)))::((("BoxString"), (((("BoxString_proj_0"), (String_sort)))::[]), (Term_sort), ((Prims.parse_int "9")), (true)))::((("BoxRef"), (((("BoxRef_proj_0"), (Ref_sort)))::[]), (Term_sort), ((Prims.parse_int "10")), (true)))::((("LexCons"), (((("LexCons_0"), (Term_sort)))::((("LexCons_1"), (Term_sort)))::[]), (Term_sort), ((Prims.parse_int "11")), (true)))::[]
in (

let bcons = (let _180_687 = (let _180_686 = (FStar_All.pipe_right constrs (FStar_List.collect constructor_to_decl))
in (FStar_All.pipe_right _180_686 (FStar_List.map (declToSmt z3options))))
in (FStar_All.pipe_right _180_687 (FStar_String.concat "\n")))
in (

let lex_ordering = "\n(define-fun is-Prims.LexCons ((t Term)) Bool \n(is-LexCons t))\n(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))\n(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))\n(or (Valid (Precedes x1 y1))\n(and (= x1 y1)\n(Valid (Precedes x2 y2)))))))\n"
in (Prims.strcat basic (Prims.strcat bcons lex_ordering)))))))


let mk_Range_const : term = (mkApp (("Range_const"), ([])) norng)


let mk_Term_type : term = (mkApp (("Tm_type"), ([])) norng)


let mk_Term_app : term  ->  term  ->  FStar_Range.range  ->  term = (fun t1 t2 r -> (mkApp (("Tm_app"), ((t1)::(t2)::[])) r))


let mk_Term_uvar : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _180_700 = (let _180_699 = (let _180_698 = (mkInteger' i norng)
in (_180_698)::[])
in (("Tm_uvar"), (_180_699)))
in (mkApp _180_700 r)))


let mk_Term_unit : term = (mkApp (("Tm_unit"), ([])) norng)


let boxInt : term  ->  term = (fun t -> (mkApp (("BoxInt"), ((t)::[])) t.rng))


let unboxInt : term  ->  term = (fun t -> (mkApp (("BoxInt_proj_0"), ((t)::[])) t.rng))


let boxBool : term  ->  term = (fun t -> (mkApp (("BoxBool"), ((t)::[])) t.rng))


let unboxBool : term  ->  term = (fun t -> (mkApp (("BoxBool_proj_0"), ((t)::[])) t.rng))


let boxString : term  ->  term = (fun t -> (mkApp (("BoxString"), ((t)::[])) t.rng))


let unboxString : term  ->  term = (fun t -> (mkApp (("BoxString_proj_0"), ((t)::[])) t.rng))


let boxRef : term  ->  term = (fun t -> (mkApp (("BoxRef"), ((t)::[])) t.rng))


let unboxRef : term  ->  term = (fun t -> (mkApp (("BoxRef_proj_0"), ((t)::[])) t.rng))


let boxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(boxInt t)
end
| Bool_sort -> begin
(boxBool t)
end
| String_sort -> begin
(boxString t)
end
| Ref_sort -> begin
(boxRef t)
end
| _84_866 -> begin
(Prims.raise FStar_Util.Impos)
end))


let unboxTerm : sort  ->  term  ->  term = (fun sort t -> (match (sort) with
| Int_sort -> begin
(unboxInt t)
end
| Bool_sort -> begin
(unboxBool t)
end
| String_sort -> begin
(unboxString t)
end
| Ref_sort -> begin
(unboxRef t)
end
| _84_874 -> begin
(Prims.raise FStar_Util.Impos)
end))


let mk_PreType : term  ->  term = (fun t -> (mkApp (("PreType"), ((t)::[])) t.rng))


let mk_Valid : term  ->  term = (fun t -> (match (t.tm) with
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Equality"), (_84_888)::(t1)::(t2)::[]); freevars = _84_882; rng = _84_880})::[]) -> begin
(mkEq ((t1), (t2)) t.rng)
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_disEquality"), (_84_907)::(t1)::(t2)::[]); freevars = _84_901; rng = _84_899})::[]) -> begin
(let _180_729 = (mkEq ((t1), (t2)) norng)
in (mkNot _180_729 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThanOrEqual"), (t1)::(t2)::[]); freevars = _84_920; rng = _84_918})::[]) -> begin
(let _180_732 = (let _180_731 = (unboxInt t1)
in (let _180_730 = (unboxInt t2)
in ((_180_731), (_180_730))))
in (mkLTE _180_732 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_LessThan"), (t1)::(t2)::[]); freevars = _84_937; rng = _84_935})::[]) -> begin
(let _180_735 = (let _180_734 = (unboxInt t1)
in (let _180_733 = (unboxInt t2)
in ((_180_734), (_180_733))))
in (mkLT _180_735 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThanOrEqual"), (t1)::(t2)::[]); freevars = _84_954; rng = _84_952})::[]) -> begin
(let _180_738 = (let _180_737 = (unboxInt t1)
in (let _180_736 = (unboxInt t2)
in ((_180_737), (_180_736))))
in (mkGTE _180_738 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_GreaterThan"), (t1)::(t2)::[]); freevars = _84_971; rng = _84_969})::[]) -> begin
(let _180_741 = (let _180_740 = (unboxInt t1)
in (let _180_739 = (unboxInt t2)
in ((_180_740), (_180_739))))
in (mkGT _180_741 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_AmpAmp"), (t1)::(t2)::[]); freevars = _84_988; rng = _84_986})::[]) -> begin
(let _180_744 = (let _180_743 = (unboxBool t1)
in (let _180_742 = (unboxBool t2)
in ((_180_743), (_180_742))))
in (mkAnd _180_744 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_BarBar"), (t1)::(t2)::[]); freevars = _84_1005; rng = _84_1003})::[]) -> begin
(let _180_747 = (let _180_746 = (unboxBool t1)
in (let _180_745 = (unboxBool t2)
in ((_180_746), (_180_745))))
in (mkOr _180_747 t.rng))
end
| App (Var ("Prims.b2t"), ({tm = App (Var ("Prims.op_Negation"), (t)::[]); freevars = _84_1022; rng = _84_1020})::[]) -> begin
(let _180_748 = (unboxBool t)
in (mkNot _180_748 t.rng))
end
| App (Var ("Prims.b2t"), (t1)::[]) -> begin
(

let _84_1039 = (unboxBool t1)
in {tm = _84_1039.tm; freevars = _84_1039.freevars; rng = t.rng})
end
| _84_1042 -> begin
(mkApp (("Valid"), ((t)::[])) t.rng)
end))


let mk_HasType : term  ->  term  ->  term = (fun v t -> (mkApp (("HasType"), ((v)::(t)::[])) t.rng))


let mk_HasTypeZ : term  ->  term  ->  term = (fun v t -> (mkApp (("HasTypeZ"), ((v)::(t)::[])) t.rng))


let mk_IsTyped : term  ->  term = (fun v -> (mkApp (("IsTyped"), ((v)::[])) norng))


let mk_HasTypeFuel : term  ->  term  ->  term  ->  term = (fun f v t -> if (FStar_Options.unthrottle_inductives ()) then begin
(mk_HasType v t)
end else begin
(mkApp (("HasTypeFuel"), ((f)::(v)::(t)::[])) t.rng)
end)


let mk_HasTypeWithFuel : term Prims.option  ->  term  ->  term  ->  term = (fun f v t -> (match (f) with
| None -> begin
(mk_HasType v t)
end
| Some (f) -> begin
(mk_HasTypeFuel f v t)
end))


let mk_Destruct : term  ->  FStar_Range.range  ->  term = (fun v -> (mkApp (("Destruct"), ((v)::[]))))


let mk_Rank : term  ->  FStar_Range.range  ->  term = (fun x -> (mkApp (("Rank"), ((x)::[]))))


let mk_tester : Prims.string  ->  term  ->  term = (fun n t -> (mkApp (((Prims.strcat "is-" n)), ((t)::[])) t.rng))


let mk_ApplyTF : term  ->  term  ->  term = (fun t t' -> (mkApp (("ApplyTF"), ((t)::(t')::[])) t.rng))


let mk_ApplyTT : term  ->  term  ->  FStar_Range.range  ->  term = (fun t t' r -> (mkApp (("ApplyTT"), ((t)::(t')::[])) r))


let mk_String_const : Prims.int  ->  FStar_Range.range  ->  term = (fun i r -> (let _180_803 = (let _180_802 = (let _180_801 = (mkInteger' i norng)
in (_180_801)::[])
in (("FString_const"), (_180_802)))
in (mkApp _180_803 r)))


let mk_Precedes : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (let _180_810 = (mkApp (("Precedes"), ((x1)::(x2)::[])) r)
in (FStar_All.pipe_right _180_810 mk_Valid)))


let mk_LexCons : term  ->  term  ->  FStar_Range.range  ->  term = (fun x1 x2 r -> (mkApp (("LexCons"), ((x1)::(x2)::[])) r))


let rec n_fuel : Prims.int  ->  term = (fun n -> if (n = (Prims.parse_int "0")) then begin
(mkApp (("ZFuel"), ([])) norng)
end else begin
(let _180_821 = (let _180_820 = (let _180_819 = (n_fuel (n - (Prims.parse_int "1")))
in (_180_819)::[])
in (("SFuel"), (_180_820)))
in (mkApp _180_821 norng))
end)


let fuel_2 : term = (n_fuel (Prims.parse_int "2"))


let fuel_100 : term = (n_fuel (Prims.parse_int "100"))


let mk_and_opt : term Prims.option  ->  term Prims.option  ->  FStar_Range.range  ->  term Prims.option = (fun p1 p2 r -> (match (((p1), (p2))) with
| (Some (p1), Some (p2)) -> begin
(let _180_828 = (mkAnd ((p1), (p2)) r)
in Some (_180_828))
end
| ((Some (p), None)) | ((None, Some (p))) -> begin
Some (p)
end
| (None, None) -> begin
None
end))


let mk_and_opt_l : term Prims.option Prims.list  ->  FStar_Range.range  ->  term Prims.option = (fun pl r -> (FStar_List.fold_right (fun p out -> (mk_and_opt p out r)) pl None))


let mk_and_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _180_841 = (mkTrue r)
in (FStar_List.fold_right (fun p1 p2 -> (mkAnd ((p1), (p2)) r)) l _180_841)))


let mk_or_l : term Prims.list  ->  FStar_Range.range  ->  term = (fun l r -> (let _180_848 = (mkFalse r)
in (FStar_List.fold_right (fun p1 p2 -> (mkOr ((p1), (p2)) r)) l _180_848)))


let mk_haseq : term  ->  term = (fun t -> (let _180_851 = (mkApp (("Prims.hasEq"), ((t)::[])) t.rng)
in (mk_Valid _180_851)))


let rec print_smt_term : term  ->  Prims.string = (fun t -> (match (t.tm) with
| Integer (n) -> begin
(FStar_Util.format1 "(Integer %s)" n)
end
| BoundV (n) -> begin
(let _180_856 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "(BoundV %s)" _180_856))
end
| FreeV (fv) -> begin
(FStar_Util.format1 "(FreeV %s)" (Prims.fst fv))
end
| App (op, l) -> begin
(let _180_857 = (print_smt_term_list l)
in (FStar_Util.format2 "(%s %s)" (op_to_string op) _180_857))
end
| Labeled (t, r1, r2) -> begin
(let _180_858 = (print_smt_term t)
in (FStar_Util.format2 "(Labeled \'%s\' %s)" r1 _180_858))
end
| LblPos (t, s) -> begin
(let _180_859 = (print_smt_term t)
in (FStar_Util.format2 "(LblPos %s %s)" s _180_859))
end
| Quant (qop, l, _84_1129, _84_1131, t) -> begin
(let _180_861 = (print_smt_term_list_list l)
in (let _180_860 = (print_smt_term t)
in (FStar_Util.format3 "(%s %s %s)" (qop_to_string qop) _180_861 _180_860)))
end))
and print_smt_term_list : term Prims.list  ->  Prims.string = (fun l -> (let _180_863 = (FStar_List.map print_smt_term l)
in (FStar_All.pipe_right _180_863 (FStar_String.concat " "))))
and print_smt_term_list_list : term Prims.list Prims.list  ->  Prims.string = (fun l -> (FStar_List.fold_left (fun s l -> (let _180_869 = (let _180_868 = (let _180_867 = (print_smt_term_list l)
in (Prims.strcat _180_867 " ] "))
in (Prims.strcat "; [ " _180_868))
in (Prims.strcat s _180_869))) "" l))




