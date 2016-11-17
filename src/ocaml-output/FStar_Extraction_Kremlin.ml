
open Prims

type decl =
| DGlobal of (flag Prims.list * lident * typ * expr)
| DFunction of (cc Prims.option * flag Prims.list * typ * lident * binder Prims.list * expr)
| DTypeAlias of (lident * Prims.int * typ)
| DTypeFlat of (lident * Prims.int * fields_t)
| DExternal of (cc Prims.option * lident * typ)
| DTypeVariant of (lident * Prims.int * branches_t) 
 and cc =
| StdCall
| CDecl
| FastCall 
 and flag =
| Private 
 and expr =
| EBound of var
| EQualified of lident
| EConstant of constant
| EUnit
| EApp of (expr * expr Prims.list)
| ELet of (binder * expr * expr)
| EIfThenElse of (expr * expr * expr)
| ESequence of expr Prims.list
| EAssign of (expr * expr)
| EBufCreate of (expr * expr)
| EBufRead of (expr * expr)
| EBufWrite of (expr * expr * expr)
| EBufSub of (expr * expr)
| EBufBlit of (expr * expr * expr * expr * expr)
| EMatch of (expr * branches)
| EOp of (op * width)
| ECast of (expr * typ)
| EPushFrame
| EPopFrame
| EBool of Prims.bool
| EAny
| EAbort
| EReturn of expr
| EFlat of (typ * (ident * expr) Prims.list)
| EField of (typ * expr * ident)
| EWhile of (expr * expr)
| EBufCreateL of expr Prims.list
| ETuple of expr Prims.list
| ECons of (typ * ident * expr Prims.list)
| EBufFill of (expr * expr * expr) 
 and op =
| Add
| AddW
| Sub
| SubW
| Div
| DivW
| Mult
| MultW
| Mod
| BOr
| BAnd
| BXor
| BShiftL
| BShiftR
| BNot
| Eq
| Neq
| Lt
| Lte
| Gt
| Gte
| And
| Or
| Xor
| Not 
 and pattern =
| PUnit
| PBool of Prims.bool
| PVar of binder
| PCons of (ident * pattern Prims.list)
| PTuple of pattern Prims.list
| PRecord of (ident * pattern) Prims.list 
 and width =
| UInt8
| UInt16
| UInt32
| UInt64
| Int8
| Int16
| Int32
| Int64
| Bool
| Int
| UInt 
 and binder =
{name : ident; typ : typ; mut : Prims.bool} 
 and typ =
| TInt of width
| TBuf of typ
| TUnit
| TQualified of lident
| TBool
| TAny
| TArrow of (typ * typ)
| TZ
| TBound of Prims.int
| TApp of (lident * typ Prims.list)
| TTuple of typ Prims.list 
 and program =
decl Prims.list 
 and fields_t =
(ident * (typ * Prims.bool)) Prims.list 
 and branches_t =
(ident * fields_t) Prims.list 
 and branches =
branch Prims.list 
 and branch =
(pattern * expr) 
 and constant =
(width * Prims.string) 
 and var =
Prims.int 
 and ident =
Prims.string 
 and lident =
(ident Prims.list * ident)


let is_DGlobal = (fun _discr_ -> (match (_discr_) with
| DGlobal (_) -> begin
true
end
| _ -> begin
false
end))


let is_DFunction = (fun _discr_ -> (match (_discr_) with
| DFunction (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeAlias = (fun _discr_ -> (match (_discr_) with
| DTypeAlias (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeFlat = (fun _discr_ -> (match (_discr_) with
| DTypeFlat (_) -> begin
true
end
| _ -> begin
false
end))


let is_DExternal = (fun _discr_ -> (match (_discr_) with
| DExternal (_) -> begin
true
end
| _ -> begin
false
end))


let is_DTypeVariant = (fun _discr_ -> (match (_discr_) with
| DTypeVariant (_) -> begin
true
end
| _ -> begin
false
end))


let is_StdCall = (fun _discr_ -> (match (_discr_) with
| StdCall (_) -> begin
true
end
| _ -> begin
false
end))


let is_CDecl = (fun _discr_ -> (match (_discr_) with
| CDecl (_) -> begin
true
end
| _ -> begin
false
end))


let is_FastCall = (fun _discr_ -> (match (_discr_) with
| FastCall (_) -> begin
true
end
| _ -> begin
false
end))


let is_Private = (fun _discr_ -> (match (_discr_) with
| Private (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBound = (fun _discr_ -> (match (_discr_) with
| EBound (_) -> begin
true
end
| _ -> begin
false
end))


let is_EQualified = (fun _discr_ -> (match (_discr_) with
| EQualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_EConstant = (fun _discr_ -> (match (_discr_) with
| EConstant (_) -> begin
true
end
| _ -> begin
false
end))


let is_EUnit = (fun _discr_ -> (match (_discr_) with
| EUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_EApp = (fun _discr_ -> (match (_discr_) with
| EApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_ELet = (fun _discr_ -> (match (_discr_) with
| ELet (_) -> begin
true
end
| _ -> begin
false
end))


let is_EIfThenElse = (fun _discr_ -> (match (_discr_) with
| EIfThenElse (_) -> begin
true
end
| _ -> begin
false
end))


let is_ESequence = (fun _discr_ -> (match (_discr_) with
| ESequence (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAssign = (fun _discr_ -> (match (_discr_) with
| EAssign (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufCreate = (fun _discr_ -> (match (_discr_) with
| EBufCreate (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufRead = (fun _discr_ -> (match (_discr_) with
| EBufRead (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufWrite = (fun _discr_ -> (match (_discr_) with
| EBufWrite (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufSub = (fun _discr_ -> (match (_discr_) with
| EBufSub (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufBlit = (fun _discr_ -> (match (_discr_) with
| EBufBlit (_) -> begin
true
end
| _ -> begin
false
end))


let is_EMatch = (fun _discr_ -> (match (_discr_) with
| EMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_EOp = (fun _discr_ -> (match (_discr_) with
| EOp (_) -> begin
true
end
| _ -> begin
false
end))


let is_ECast = (fun _discr_ -> (match (_discr_) with
| ECast (_) -> begin
true
end
| _ -> begin
false
end))


let is_EPushFrame = (fun _discr_ -> (match (_discr_) with
| EPushFrame (_) -> begin
true
end
| _ -> begin
false
end))


let is_EPopFrame = (fun _discr_ -> (match (_discr_) with
| EPopFrame (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBool = (fun _discr_ -> (match (_discr_) with
| EBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAny = (fun _discr_ -> (match (_discr_) with
| EAny (_) -> begin
true
end
| _ -> begin
false
end))


let is_EAbort = (fun _discr_ -> (match (_discr_) with
| EAbort (_) -> begin
true
end
| _ -> begin
false
end))


let is_EReturn = (fun _discr_ -> (match (_discr_) with
| EReturn (_) -> begin
true
end
| _ -> begin
false
end))


let is_EFlat = (fun _discr_ -> (match (_discr_) with
| EFlat (_) -> begin
true
end
| _ -> begin
false
end))


let is_EField = (fun _discr_ -> (match (_discr_) with
| EField (_) -> begin
true
end
| _ -> begin
false
end))


let is_EWhile = (fun _discr_ -> (match (_discr_) with
| EWhile (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufCreateL = (fun _discr_ -> (match (_discr_) with
| EBufCreateL (_) -> begin
true
end
| _ -> begin
false
end))


let is_ETuple = (fun _discr_ -> (match (_discr_) with
| ETuple (_) -> begin
true
end
| _ -> begin
false
end))


let is_ECons = (fun _discr_ -> (match (_discr_) with
| ECons (_) -> begin
true
end
| _ -> begin
false
end))


let is_EBufFill = (fun _discr_ -> (match (_discr_) with
| EBufFill (_) -> begin
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


let is_AddW = (fun _discr_ -> (match (_discr_) with
| AddW (_) -> begin
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


let is_SubW = (fun _discr_ -> (match (_discr_) with
| SubW (_) -> begin
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


let is_DivW = (fun _discr_ -> (match (_discr_) with
| DivW (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mult = (fun _discr_ -> (match (_discr_) with
| Mult (_) -> begin
true
end
| _ -> begin
false
end))


let is_MultW = (fun _discr_ -> (match (_discr_) with
| MultW (_) -> begin
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


let is_BOr = (fun _discr_ -> (match (_discr_) with
| BOr (_) -> begin
true
end
| _ -> begin
false
end))


let is_BAnd = (fun _discr_ -> (match (_discr_) with
| BAnd (_) -> begin
true
end
| _ -> begin
false
end))


let is_BXor = (fun _discr_ -> (match (_discr_) with
| BXor (_) -> begin
true
end
| _ -> begin
false
end))


let is_BShiftL = (fun _discr_ -> (match (_discr_) with
| BShiftL (_) -> begin
true
end
| _ -> begin
false
end))


let is_BShiftR = (fun _discr_ -> (match (_discr_) with
| BShiftR (_) -> begin
true
end
| _ -> begin
false
end))


let is_BNot = (fun _discr_ -> (match (_discr_) with
| BNot (_) -> begin
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


let is_Neq = (fun _discr_ -> (match (_discr_) with
| Neq (_) -> begin
true
end
| _ -> begin
false
end))


let is_Lt = (fun _discr_ -> (match (_discr_) with
| Lt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Lte = (fun _discr_ -> (match (_discr_) with
| Lte (_) -> begin
true
end
| _ -> begin
false
end))


let is_Gt = (fun _discr_ -> (match (_discr_) with
| Gt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Gte = (fun _discr_ -> (match (_discr_) with
| Gte (_) -> begin
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


let is_Xor = (fun _discr_ -> (match (_discr_) with
| Xor (_) -> begin
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


let is_PUnit = (fun _discr_ -> (match (_discr_) with
| PUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_PBool = (fun _discr_ -> (match (_discr_) with
| PBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_PVar = (fun _discr_ -> (match (_discr_) with
| PVar (_) -> begin
true
end
| _ -> begin
false
end))


let is_PCons = (fun _discr_ -> (match (_discr_) with
| PCons (_) -> begin
true
end
| _ -> begin
false
end))


let is_PTuple = (fun _discr_ -> (match (_discr_) with
| PTuple (_) -> begin
true
end
| _ -> begin
false
end))


let is_PRecord = (fun _discr_ -> (match (_discr_) with
| PRecord (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt8 = (fun _discr_ -> (match (_discr_) with
| UInt8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt16 = (fun _discr_ -> (match (_discr_) with
| UInt16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt32 = (fun _discr_ -> (match (_discr_) with
| UInt32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt64 = (fun _discr_ -> (match (_discr_) with
| UInt64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int8 = (fun _discr_ -> (match (_discr_) with
| Int8 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int16 = (fun _discr_ -> (match (_discr_) with
| Int16 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int32 = (fun _discr_ -> (match (_discr_) with
| Int32 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int64 = (fun _discr_ -> (match (_discr_) with
| Int64 (_) -> begin
true
end
| _ -> begin
false
end))


let is_Bool = (fun _discr_ -> (match (_discr_) with
| Bool (_) -> begin
true
end
| _ -> begin
false
end))


let is_Int = (fun _discr_ -> (match (_discr_) with
| Int (_) -> begin
true
end
| _ -> begin
false
end))


let is_UInt = (fun _discr_ -> (match (_discr_) with
| UInt (_) -> begin
true
end
| _ -> begin
false
end))


let is_Mkbinder : binder  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbinder"))))


let is_TInt = (fun _discr_ -> (match (_discr_) with
| TInt (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBuf = (fun _discr_ -> (match (_discr_) with
| TBuf (_) -> begin
true
end
| _ -> begin
false
end))


let is_TUnit = (fun _discr_ -> (match (_discr_) with
| TUnit (_) -> begin
true
end
| _ -> begin
false
end))


let is_TQualified = (fun _discr_ -> (match (_discr_) with
| TQualified (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBool = (fun _discr_ -> (match (_discr_) with
| TBool (_) -> begin
true
end
| _ -> begin
false
end))


let is_TAny = (fun _discr_ -> (match (_discr_) with
| TAny (_) -> begin
true
end
| _ -> begin
false
end))


let is_TArrow = (fun _discr_ -> (match (_discr_) with
| TArrow (_) -> begin
true
end
| _ -> begin
false
end))


let is_TZ = (fun _discr_ -> (match (_discr_) with
| TZ (_) -> begin
true
end
| _ -> begin
false
end))


let is_TBound = (fun _discr_ -> (match (_discr_) with
| TBound (_) -> begin
true
end
| _ -> begin
false
end))


let is_TApp = (fun _discr_ -> (match (_discr_) with
| TApp (_) -> begin
true
end
| _ -> begin
false
end))


let is_TTuple = (fun _discr_ -> (match (_discr_) with
| TTuple (_) -> begin
true
end
| _ -> begin
false
end))


let ___DGlobal____0 = (fun projectee -> (match (projectee) with
| DGlobal (_82_14) -> begin
_82_14
end))


let ___DFunction____0 = (fun projectee -> (match (projectee) with
| DFunction (_82_17) -> begin
_82_17
end))


let ___DTypeAlias____0 = (fun projectee -> (match (projectee) with
| DTypeAlias (_82_20) -> begin
_82_20
end))


let ___DTypeFlat____0 = (fun projectee -> (match (projectee) with
| DTypeFlat (_82_23) -> begin
_82_23
end))


let ___DExternal____0 = (fun projectee -> (match (projectee) with
| DExternal (_82_26) -> begin
_82_26
end))


let ___DTypeVariant____0 = (fun projectee -> (match (projectee) with
| DTypeVariant (_82_29) -> begin
_82_29
end))


let ___EBound____0 = (fun projectee -> (match (projectee) with
| EBound (_82_32) -> begin
_82_32
end))


let ___EQualified____0 = (fun projectee -> (match (projectee) with
| EQualified (_82_35) -> begin
_82_35
end))


let ___EConstant____0 = (fun projectee -> (match (projectee) with
| EConstant (_82_38) -> begin
_82_38
end))


let ___EApp____0 = (fun projectee -> (match (projectee) with
| EApp (_82_41) -> begin
_82_41
end))


let ___ELet____0 = (fun projectee -> (match (projectee) with
| ELet (_82_44) -> begin
_82_44
end))


let ___EIfThenElse____0 = (fun projectee -> (match (projectee) with
| EIfThenElse (_82_47) -> begin
_82_47
end))


let ___ESequence____0 = (fun projectee -> (match (projectee) with
| ESequence (_82_50) -> begin
_82_50
end))


let ___EAssign____0 = (fun projectee -> (match (projectee) with
| EAssign (_82_53) -> begin
_82_53
end))


let ___EBufCreate____0 = (fun projectee -> (match (projectee) with
| EBufCreate (_82_56) -> begin
_82_56
end))


let ___EBufRead____0 = (fun projectee -> (match (projectee) with
| EBufRead (_82_59) -> begin
_82_59
end))


let ___EBufWrite____0 = (fun projectee -> (match (projectee) with
| EBufWrite (_82_62) -> begin
_82_62
end))


let ___EBufSub____0 = (fun projectee -> (match (projectee) with
| EBufSub (_82_65) -> begin
_82_65
end))


let ___EBufBlit____0 = (fun projectee -> (match (projectee) with
| EBufBlit (_82_68) -> begin
_82_68
end))


let ___EMatch____0 = (fun projectee -> (match (projectee) with
| EMatch (_82_71) -> begin
_82_71
end))


let ___EOp____0 = (fun projectee -> (match (projectee) with
| EOp (_82_74) -> begin
_82_74
end))


let ___ECast____0 = (fun projectee -> (match (projectee) with
| ECast (_82_77) -> begin
_82_77
end))


let ___EBool____0 = (fun projectee -> (match (projectee) with
| EBool (_82_80) -> begin
_82_80
end))


let ___EReturn____0 = (fun projectee -> (match (projectee) with
| EReturn (_82_83) -> begin
_82_83
end))


let ___EFlat____0 = (fun projectee -> (match (projectee) with
| EFlat (_82_86) -> begin
_82_86
end))


let ___EField____0 = (fun projectee -> (match (projectee) with
| EField (_82_89) -> begin
_82_89
end))


let ___EWhile____0 = (fun projectee -> (match (projectee) with
| EWhile (_82_92) -> begin
_82_92
end))


let ___EBufCreateL____0 = (fun projectee -> (match (projectee) with
| EBufCreateL (_82_95) -> begin
_82_95
end))


let ___ETuple____0 = (fun projectee -> (match (projectee) with
| ETuple (_82_98) -> begin
_82_98
end))


let ___ECons____0 = (fun projectee -> (match (projectee) with
| ECons (_82_101) -> begin
_82_101
end))


let ___EBufFill____0 = (fun projectee -> (match (projectee) with
| EBufFill (_82_104) -> begin
_82_104
end))


let ___PBool____0 = (fun projectee -> (match (projectee) with
| PBool (_82_107) -> begin
_82_107
end))


let ___PVar____0 = (fun projectee -> (match (projectee) with
| PVar (_82_110) -> begin
_82_110
end))


let ___PCons____0 = (fun projectee -> (match (projectee) with
| PCons (_82_113) -> begin
_82_113
end))


let ___PTuple____0 = (fun projectee -> (match (projectee) with
| PTuple (_82_116) -> begin
_82_116
end))


let ___PRecord____0 = (fun projectee -> (match (projectee) with
| PRecord (_82_119) -> begin
_82_119
end))


let ___TInt____0 = (fun projectee -> (match (projectee) with
| TInt (_82_123) -> begin
_82_123
end))


let ___TBuf____0 = (fun projectee -> (match (projectee) with
| TBuf (_82_126) -> begin
_82_126
end))


let ___TQualified____0 = (fun projectee -> (match (projectee) with
| TQualified (_82_129) -> begin
_82_129
end))


let ___TArrow____0 = (fun projectee -> (match (projectee) with
| TArrow (_82_132) -> begin
_82_132
end))


let ___TBound____0 = (fun projectee -> (match (projectee) with
| TBound (_82_135) -> begin
_82_135
end))


let ___TApp____0 = (fun projectee -> (match (projectee) with
| TApp (_82_138) -> begin
_82_138
end))


let ___TTuple____0 = (fun projectee -> (match (projectee) with
| TTuple (_82_141) -> begin
_82_141
end))


type version =
Prims.int


let current_version : version = (Prims.parse_int "18")


type file =
(Prims.string * program)


type binary_format =
(version * file Prims.list)


let fst3 = (fun _82_147 -> (match (_82_147) with
| (x, _82_144, _82_146) -> begin
x
end))


let snd3 = (fun _82_153 -> (match (_82_153) with
| (_82_149, x, _82_152) -> begin
x
end))


let thd3 = (fun _82_159 -> (match (_82_159) with
| (_82_155, _82_157, x) -> begin
x
end))


let mk_width : Prims.string  ->  width Prims.option = (fun _82_1 -> (match (_82_1) with
| "UInt8" -> begin
Some (UInt8)
end
| "UInt16" -> begin
Some (UInt16)
end
| "UInt32" -> begin
Some (UInt32)
end
| "UInt64" -> begin
Some (UInt64)
end
| "Int8" -> begin
Some (Int8)
end
| "Int16" -> begin
Some (Int16)
end
| "Int32" -> begin
Some (Int32)
end
| "Int64" -> begin
Some (Int64)
end
| _82_170 -> begin
None
end))


let mk_bool_op : Prims.string  ->  op Prims.option = (fun _82_2 -> (match (_82_2) with
| "op_Negation" -> begin
Some (Not)
end
| "op_AmpAmp" -> begin
Some (And)
end
| "op_BarBar" -> begin
Some (Or)
end
| "op_Equality" -> begin
Some (Eq)
end
| "op_disEquality" -> begin
Some (Neq)
end
| _82_178 -> begin
None
end))


let is_bool_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_bool_op op) <> None))


let mk_op : Prims.string  ->  op Prims.option = (fun _82_3 -> (match (_82_3) with
| ("add") | ("op_Plus_Hat") -> begin
Some (Add)
end
| ("add_mod") | ("op_Plus_Percent_Hat") -> begin
Some (AddW)
end
| ("sub") | ("op_Subtraction_Hat") -> begin
Some (Sub)
end
| ("sub_mod") | ("op_Subtraction_Percent_Hat") -> begin
Some (SubW)
end
| ("mul") | ("op_Star_Hat") -> begin
Some (Mult)
end
| ("mul_mod") | ("op_Star_Percent_Hat") -> begin
Some (MultW)
end
| ("div") | ("op_Slash_Hat") -> begin
Some (Div)
end
| ("div_mod") | ("op_Slash_Percent_Hat") -> begin
Some (DivW)
end
| ("rem") | ("op_Percent_Hat") -> begin
Some (Mod)
end
| ("logor") | ("op_Bar_Hat") -> begin
Some (BOr)
end
| ("logxor") | ("op_Hat_Hat") -> begin
Some (BXor)
end
| ("logand") | ("op_Amp_Hat") -> begin
Some (BAnd)
end
| "lognot" -> begin
Some (BNot)
end
| ("shift_right") | ("op_Greater_Greater_Hat") -> begin
Some (BShiftR)
end
| ("shift_left") | ("op_Less_Less_Hat") -> begin
Some (BShiftL)
end
| ("eq") | ("op_Equals_Hat") -> begin
Some (Eq)
end
| ("op_Greater_Hat") | ("gt") -> begin
Some (Gt)
end
| ("op_Greater_Equals_Hat") | ("gte") -> begin
Some (Gte)
end
| ("op_Less_Hat") | ("lt") -> begin
Some (Lt)
end
| ("op_Less_Equals_Hat") | ("lte") -> begin
Some (Lte)
end
| _82_221 -> begin
None
end))


let is_op : Prims.string  ->  Prims.bool = (fun op -> ((mk_op op) <> None))


let is_machine_int : Prims.string  ->  Prims.bool = (fun m -> ((mk_width m) <> None))


type env =
{names : name Prims.list; names_t : Prims.string Prims.list; module_name : Prims.string Prims.list} 
 and name =
{pretty : Prims.string; mut : Prims.bool}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let is_Mkname : name  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkname"))))


let empty : Prims.string Prims.list  ->  env = (fun module_name -> {names = []; names_t = []; module_name = module_name})


let extend : env  ->  Prims.string  ->  Prims.bool  ->  env = (fun env x is_mut -> (

let _82_235 = env
in {names = ({pretty = x; mut = is_mut})::env.names; names_t = _82_235.names_t; module_name = _82_235.module_name}))


let extend_t : env  ->  Prims.string  ->  env = (fun env x -> (

let _82_239 = env
in {names = _82_239.names; names_t = (x)::env.names_t; module_name = _82_239.module_name}))


let find_name : env  ->  Prims.string  ->  name = (fun env x -> (match ((FStar_List.tryFind (fun name -> (name.pretty = x)) env.names)) with
| Some (name) -> begin
name
end
| None -> begin
(FStar_All.failwith "internal error: name not found")
end))


let is_mutable : env  ->  Prims.string  ->  Prims.bool = (fun env x -> (let _178_716 = (find_name env x)
in _178_716.mut))


let find : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name.pretty = x)) env.names)
end)
with
| _82_255 -> begin
(let _178_724 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _178_724))
end)


let find_t : env  ->  Prims.string  ->  Prims.int = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.index (fun name -> (name = x)) env.names_t)
end)
with
| _82_265 -> begin
(let _178_732 = (FStar_Util.format1 "Internal error: name not found %s\n" x)
in (FStar_All.failwith _178_732))
end)


let add_binders = (fun env binders -> (FStar_List.fold_left (fun env _82_278 -> (match (_82_278) with
| ((name, _82_274), _82_277) -> begin
(extend env name false)
end)) env binders))


let rec translate : FStar_Extraction_ML_Syntax.mllib  ->  file Prims.list = (fun _82_280 -> (match (_82_280) with
| FStar_Extraction_ML_Syntax.MLLib (modules) -> begin
(FStar_List.filter_map (fun m -> (

let m_name = (

let _82_289 = m
in (match (_82_289) with
| ((prefix, final), _82_286, _82_288) -> begin
(FStar_String.concat "." (FStar_List.append prefix ((final)::[])))
end))
in try
(match (()) with
| () -> begin
(

let _82_299 = (FStar_Util.print1 "Attempting to translate module %s\n" m_name)
in (let _178_765 = (translate_module m)
in Some (_178_765)))
end)
with
| e -> begin
(

let _82_295 = (let _178_767 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Unable to translate module: %s because:\n  %s\n" m_name _178_767))
in None)
end)) modules)
end))
and translate_module : ((Prims.string Prims.list * Prims.string) * (FStar_Extraction_ML_Syntax.mlsig * FStar_Extraction_ML_Syntax.mlmodule) Prims.option * FStar_Extraction_ML_Syntax.mllib)  ->  file = (fun _82_305 -> (match (_82_305) with
| (module_name, modul, _82_304) -> begin
(

let module_name = (FStar_List.append (Prims.fst module_name) (((Prims.snd module_name))::[]))
in (

let program = (match (modul) with
| Some (_signature, decls) -> begin
(FStar_List.filter_map (translate_decl (empty module_name)) decls)
end
| _82_312 -> begin
(FStar_All.failwith "Unexpected standalone interface or nested modules")
end)
in (((FStar_String.concat "_" module_name)), (program))))
end))
and translate_decl : env  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  decl Prims.option = (fun env d -> (match (d) with
| (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) | (FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t0); FStar_Extraction_ML_Syntax.mllb_add_unit = _; FStar_Extraction_ML_Syntax.mllb_def = {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Coerce ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (args, body); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, _, _); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}; FStar_Extraction_ML_Syntax.print_typ = _})::[])) -> begin
(

let assumed = (FStar_Util.for_some (fun _82_4 -> (match (_82_4) with
| FStar_Extraction_ML_Syntax.Assumed -> begin
true
end
| _82_378 -> begin
false
end)) flags)
in (

let flags = if (FStar_Util.for_some (fun _82_5 -> (match (_82_5) with
| FStar_Extraction_ML_Syntax.Private -> begin
true
end
| _82_383 -> begin
false
end)) flags) then begin
(Private)::[]
end else begin
[]
end
in (

let env = if (flavor = FStar_Extraction_ML_Syntax.Rec) then begin
(extend env name false)
end else begin
env
end
in (

let rec find_return_type = (fun _82_6 -> (match (_82_6) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_82_389, _82_391, t) -> begin
(find_return_type t)
end
| t -> begin
t
end))
in (

let t = (let _178_775 = (find_return_type t0)
in (translate_type env _178_775))
in (

let binders = (translate_binders env args)
in (

let env = (add_binders env args)
in (

let name = ((env.module_name), (name))
in if assumed then begin
(let _178_778 = (let _178_777 = (let _178_776 = (translate_type env t0)
in ((None), (name), (_178_776)))
in DExternal (_178_777))
in Some (_178_778))
end else begin
try
(match (()) with
| () -> begin
(

let body = (translate_expr env body)
in Some (DFunction (((None), (flags), (t), (name), (binders), (body)))))
end)
with
| e -> begin
(

let _82_404 = (let _178_781 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: writing a stub for %s (%s)\n" (Prims.snd name) _178_781))
in Some (DFunction (((None), (flags), (t), (name), (binders), (EAbort)))))
end
end))))))))
end
| FStar_Extraction_ML_Syntax.MLM_Let (flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_422); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], t); FStar_Extraction_ML_Syntax.mllb_add_unit = _82_415; FStar_Extraction_ML_Syntax.mllb_def = expr; FStar_Extraction_ML_Syntax.print_typ = _82_412})::[]) -> begin
(

let flags = if (FStar_Util.for_some (fun _82_7 -> (match (_82_7) with
| FStar_Extraction_ML_Syntax.Private -> begin
true
end
| _82_431 -> begin
false
end)) flags) then begin
(Private)::[]
end else begin
[]
end
in (

let t = (translate_type env t)
in (

let name = ((env.module_name), (name))
in try
(match (()) with
| () -> begin
(

let expr = (translate_expr env expr)
in Some (DGlobal (((flags), (name), (t), (expr)))))
end)
with
| e -> begin
(

let _82_439 = (let _178_785 = (FStar_Util.print_exn e)
in (FStar_Util.print2 "Warning: not translating definition for %s (%s)\n" (Prims.snd name) _178_785))
in Some (DGlobal (((flags), (name), (t), (EAny)))))
end)))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_82_445, _82_447, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_459); FStar_Extraction_ML_Syntax.mllb_tysc = ts; FStar_Extraction_ML_Syntax.mllb_add_unit = _82_455; FStar_Extraction_ML_Syntax.mllb_def = _82_453; FStar_Extraction_ML_Syntax.print_typ = _82_451})::_82_449) -> begin
(

let _82_465 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in (

let _82_472 = (match (ts) with
| Some (idents, t) -> begin
(let _178_788 = (let _178_786 = (FStar_List.map Prims.fst idents)
in (FStar_String.concat ", " _178_786))
in (let _178_787 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) t)
in (FStar_Util.print2 "Type scheme is: forall %s. %s\n" _178_788 _178_787)))
end
| None -> begin
()
end)
in None))
end
| FStar_Extraction_ML_Syntax.MLM_Let (_82_475) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Extraction_ML_Syntax.MLM_Loc (_82_478) -> begin
None
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((assumed, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _82_495 -> (match (_82_495) with
| (name, _82_494) -> begin
(extend_t env name)
end)) env args)
in if assumed then begin
None
end else begin
(let _178_793 = (let _178_792 = (let _178_791 = (translate_type env t)
in ((name), ((FStar_List.length args)), (_178_791)))
in DTypeAlias (_178_792))
in Some (_178_793))
end))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_498, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_Record (fields))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _82_513 -> (match (_82_513) with
| (name, _82_512) -> begin
(extend_t env name)
end)) env args)
in (let _178_801 = (let _178_800 = (let _178_799 = (FStar_List.map (fun _82_517 -> (match (_82_517) with
| (f, t) -> begin
(let _178_798 = (let _178_797 = (translate_type env t)
in ((_178_797), (false)))
in ((f), (_178_798)))
end)) fields)
in ((name), ((FStar_List.length args)), (_178_799)))
in DTypeFlat (_178_800))
in Some (_178_801))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_519, name, _mangled_name, args, Some (FStar_Extraction_ML_Syntax.MLTD_DType (branches))))::[]) -> begin
(

let name = ((env.module_name), (name))
in (

let env = (FStar_List.fold_left (fun env _82_534 -> (match (_82_534) with
| (name, _82_533) -> begin
(extend_t env name)
end)) env args)
in (let _178_816 = (let _178_815 = (let _178_814 = (FStar_List.mapi (fun i _82_539 -> (match (_82_539) with
| (cons, ts) -> begin
(let _178_813 = (FStar_List.mapi (fun j t -> (let _178_812 = (let _178_809 = (FStar_Util.string_of_int i)
in (let _178_808 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "x%s%s" _178_809 _178_808)))
in (let _178_811 = (let _178_810 = (translate_type env t)
in ((_178_810), (false)))
in ((_178_812), (_178_811))))) ts)
in ((cons), (_178_813)))
end)) branches)
in ((name), ((FStar_List.length args)), (_178_814)))
in DTypeVariant (_178_815))
in Some (_178_816))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (((_82_545, name, _mangled_name, _82_549, _82_551))::_82_543) -> begin
(

let _82_555 = (FStar_Util.print1 "Warning: not translating definition for %s (and possibly others)\n" name)
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Ty ([]) -> begin
(

let _82_559 = (FStar_Util.print_string "Impossible!! Empty block of mutually recursive type declarations")
in None)
end
| FStar_Extraction_ML_Syntax.MLM_Top (_82_562) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Top]")
end
| FStar_Extraction_ML_Syntax.MLM_Exn (_82_565) -> begin
(FStar_All.failwith "todo: translate_decl [MLM_Exn]")
end))
and translate_type : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| (FStar_Extraction_ML_Syntax.MLTY_Tuple ([])) | (FStar_Extraction_ML_Syntax.MLTY_Top) -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Var (name, _82_574) -> begin
(let _178_819 = (find_t env name)
in TBound (_178_819))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _82_579, t2) -> begin
(let _178_822 = (let _178_821 = (translate_type env t1)
in (let _178_820 = (translate_type env t2)
in ((_178_821), (_178_820))))
in TArrow (_178_822))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.unit") -> begin
TUnit
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Prims.bool") -> begin
TBool
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt8.t") -> begin
TInt (UInt8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt16.t") -> begin
TInt (UInt16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt32.t") -> begin
TInt (UInt32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.UInt64.t") -> begin
TInt (UInt64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int8.t") -> begin
TInt (Int8)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int16.t") -> begin
TInt (Int16)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int32.t") -> begin
TInt (Int32)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Int64.t") -> begin
TInt (Int64)
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((arg)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.buffer") -> begin
(let _178_823 = (translate_type env arg)
in TBuf (_178_823))
end
| FStar_Extraction_ML_Syntax.MLTY_Named ((_82_629)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Ghost.erased") -> begin
TAny
end
| FStar_Extraction_ML_Syntax.MLTY_Named ([], (path, type_name)) -> begin
TQualified (((path), (type_name)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (("Prims")::[], t)) when (FStar_Util.starts_with t "tuple") -> begin
(let _178_824 = (FStar_List.map (translate_type env) args)
in TTuple (_178_824))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, (path, type_name)) -> begin
(let _178_826 = (let _178_825 = (FStar_List.map (translate_type env) args)
in ((((path), (type_name))), (_178_825)))
in TApp (_178_826))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(let _178_827 = (FStar_List.map (translate_type env) ts)
in TTuple (_178_827))
end))
and translate_binders : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list  ->  binder Prims.list = (fun env args -> (FStar_List.map (translate_binder env) args))
and translate_binder : env  ->  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)  ->  binder = (fun env _82_663 -> (match (_82_663) with
| ((name, _82_660), typ) -> begin
(let _178_832 = (translate_type env typ)
in {name = name; typ = _178_832; mut = false})
end))
and translate_expr : env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  expr = (fun env e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Tuple ([]) -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(translate_constant c)
end
| FStar_Extraction_ML_Syntax.MLE_Var (name, _82_672) -> begin
(let _178_835 = (find env name)
in EBound (_178_835))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op) when ((is_machine_int m) && (is_op op)) -> begin
(let _178_838 = (let _178_837 = (FStar_Util.must (mk_op op))
in (let _178_836 = (FStar_Util.must (mk_width m))
in ((_178_837), (_178_836))))
in EOp (_178_838))
end
| FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op) when (is_bool_op op) -> begin
(let _178_840 = (let _178_839 = (FStar_Util.must (mk_bool_op op))
in ((_178_839), (Bool)))
in EOp (_178_840))
end
| FStar_Extraction_ML_Syntax.MLE_Name (n) -> begin
EQualified (n)
end
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, flags, ({FStar_Extraction_ML_Syntax.mllb_name = (name, _82_699); FStar_Extraction_ML_Syntax.mllb_tysc = Some ([], typ); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = body; FStar_Extraction_ML_Syntax.print_typ = print})::[]), continuation) -> begin
(

let is_mut = (FStar_Util.for_some (fun _82_8 -> (match (_82_8) with
| FStar_Extraction_ML_Syntax.Mutable -> begin
true
end
| _82_710 -> begin
false
end)) flags)
in (

let _82_734 = if is_mut then begin
(let _178_845 = (match (typ) with
| FStar_Extraction_ML_Syntax.MLTY_Named ((t)::[], p) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.stackref") -> begin
t
end
| _82_718 -> begin
(let _178_843 = (let _178_842 = (FStar_Extraction_ML_Code.string_of_mlty (([]), ("")) typ)
in (FStar_Util.format1 "unexpected: bad desugaring of Mutable (typ is %s)" _178_842))
in (FStar_All.failwith _178_843))
end)
in (let _178_844 = (match (body) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_App (_82_724, (body)::[]); FStar_Extraction_ML_Syntax.mlty = _82_722; FStar_Extraction_ML_Syntax.loc = _82_720} -> begin
body
end
| _82_731 -> begin
(FStar_All.failwith "unexpected: bad desugaring of Mutable")
end)
in ((_178_845), (_178_844))))
end else begin
((typ), (body))
end
in (match (_82_734) with
| (typ, body) -> begin
(

let binder = (let _178_846 = (translate_type env typ)
in {name = name; typ = _178_846; mut = is_mut})
in (

let body = (translate_expr env body)
in (

let env = (extend env name is_mut)
in (

let continuation = (translate_expr env continuation)
in ELet (((binder), (body), (continuation)))))))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (expr, branches) -> begin
(let _178_849 = (let _178_848 = (translate_expr env expr)
in (let _178_847 = (translate_branches env branches)
in ((_178_848), (_178_847))))
in EMatch (_178_849))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_746; FStar_Extraction_ML_Syntax.loc = _82_744}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _82_756); FStar_Extraction_ML_Syntax.mlty = _82_753; FStar_Extraction_ML_Syntax.loc = _82_751})::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Bang") && (is_mutable env v)) -> begin
(let _178_850 = (find env v)
in EBound (_178_850))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_766; FStar_Extraction_ML_Syntax.loc = _82_764}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (v, _82_777); FStar_Extraction_ML_Syntax.mlty = _82_774; FStar_Extraction_ML_Syntax.loc = _82_772})::(e)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.op_Colon_Equals") && (is_mutable env v)) -> begin
(let _178_854 = (let _178_853 = (let _178_851 = (find env v)
in EBound (_178_851))
in (let _178_852 = (translate_expr env e)
in ((_178_853), (_178_852))))
in EAssign (_178_854))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_787; FStar_Extraction_ML_Syntax.loc = _82_785}, (e1)::(e2)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.index") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Access")) -> begin
(let _178_857 = (let _178_856 = (translate_expr env e1)
in (let _178_855 = (translate_expr env e2)
in ((_178_856), (_178_855))))
in EBufRead (_178_857))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_799; FStar_Extraction_ML_Syntax.loc = _82_797}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.create") -> begin
(let _178_860 = (let _178_859 = (translate_expr env e1)
in (let _178_858 = (translate_expr env e2)
in ((_178_859), (_178_858))))
in EBufCreate (_178_860))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_811; FStar_Extraction_ML_Syntax.loc = _82_809}, (e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.createL") -> begin
(

let rec list_elements = (fun acc e2 -> (match (e2.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Cons"), (hd)::(tl)::[]) -> begin
(list_elements ((hd)::acc) tl)
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((("Prims")::[], "Nil"), []) -> begin
(FStar_List.rev acc)
end
| _82_839 -> begin
(FStar_All.failwith "Argument of FStar.Buffer.createL is not a string literal!")
end))
in (

let list_elements = (list_elements [])
in (let _178_867 = (let _178_866 = (list_elements e2)
in (FStar_List.map (translate_expr env) _178_866))
in EBufCreateL (_178_867))))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_844; FStar_Extraction_ML_Syntax.loc = _82_842}, (e1)::(e2)::(_e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.sub") -> begin
(let _178_870 = (let _178_869 = (translate_expr env e1)
in (let _178_868 = (translate_expr env e2)
in ((_178_869), (_178_868))))
in EBufSub (_178_870))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_857; FStar_Extraction_ML_Syntax.loc = _82_855}, (e1)::(e2)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.offset") -> begin
(let _178_873 = (let _178_872 = (translate_expr env e1)
in (let _178_871 = (translate_expr env e2)
in ((_178_872), (_178_871))))
in EBufSub (_178_873))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_869; FStar_Extraction_ML_Syntax.loc = _82_867}, (e1)::(e2)::(e3)::[]) when (((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.upd") || ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.op_Array_Assignment")) -> begin
(let _178_877 = (let _178_876 = (translate_expr env e1)
in (let _178_875 = (translate_expr env e2)
in (let _178_874 = (translate_expr env e3)
in ((_178_876), (_178_875), (_178_874)))))
in EBufWrite (_178_877))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_882; FStar_Extraction_ML_Syntax.loc = _82_880}, (_82_887)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.push_frame") -> begin
EPushFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_894; FStar_Extraction_ML_Syntax.loc = _82_892}, (_82_899)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.pop_frame") -> begin
EPopFrame
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_906; FStar_Extraction_ML_Syntax.loc = _82_904}, (e1)::(e2)::(e3)::(e4)::(e5)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.blit") -> begin
(let _178_883 = (let _178_882 = (translate_expr env e1)
in (let _178_881 = (translate_expr env e2)
in (let _178_880 = (translate_expr env e3)
in (let _178_879 = (translate_expr env e4)
in (let _178_878 = (translate_expr env e5)
in ((_178_882), (_178_881), (_178_880), (_178_879), (_178_878)))))))
in EBufBlit (_178_883))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_921; FStar_Extraction_ML_Syntax.loc = _82_919}, (e1)::(e2)::(e3)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.Buffer.fill") -> begin
(let _178_887 = (let _178_886 = (translate_expr env e1)
in (let _178_885 = (translate_expr env e2)
in (let _178_884 = (translate_expr env e3)
in ((_178_886), (_178_885), (_178_884)))))
in EBufFill (_178_887))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_934; FStar_Extraction_ML_Syntax.loc = _82_932}, (_82_939)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.ST.get") -> begin
ECast (((EConstant (((UInt8), ("0")))), (TAny)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _82_946; FStar_Extraction_ML_Syntax.loc = _82_944}, (e)::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "Obj.repr") -> begin
(let _178_889 = (let _178_888 = (translate_expr env e)
in ((_178_888), (TAny)))
in ECast (_178_889))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], op); FStar_Extraction_ML_Syntax.mlty = _82_957; FStar_Extraction_ML_Syntax.loc = _82_955}, args) when ((is_machine_int m) && (is_op op)) -> begin
(let _178_891 = (FStar_Util.must (mk_width m))
in (let _178_890 = (FStar_Util.must (mk_op op))
in (mk_op_app env _178_891 _178_890 args)))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("Prims")::[], op); FStar_Extraction_ML_Syntax.mlty = _82_971; FStar_Extraction_ML_Syntax.loc = _82_969}, args) when (is_bool_op op) -> begin
(let _178_892 = (FStar_Util.must (mk_bool_op op))
in (mk_op_app env Bool _178_892 args))
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "int_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) | (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::(m)::[], "uint_to_t"); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Int (c, None)); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _})::[])) when (is_machine_int m) -> begin
(let _178_894 = (let _178_893 = (FStar_Util.must (mk_width m))
in ((_178_893), (c)))
in EConstant (_178_894))
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (("FStar")::("Int")::("Cast")::[], c); FStar_Extraction_ML_Syntax.mlty = _82_1030; FStar_Extraction_ML_Syntax.loc = _82_1028}, (arg)::[]) -> begin
(

let is_known_type = ((((((((FStar_Util.starts_with c "uint8") || (FStar_Util.starts_with c "uint16")) || (FStar_Util.starts_with c "uint32")) || (FStar_Util.starts_with c "uint64")) || (FStar_Util.starts_with c "int8")) || (FStar_Util.starts_with c "int16")) || (FStar_Util.starts_with c "int32")) || (FStar_Util.starts_with c "int64"))
in if ((FStar_Util.ends_with c "uint64") && is_known_type) then begin
(let _178_896 = (let _178_895 = (translate_expr env arg)
in ((_178_895), (TInt (UInt64))))
in ECast (_178_896))
end else begin
if ((FStar_Util.ends_with c "uint32") && is_known_type) then begin
(let _178_898 = (let _178_897 = (translate_expr env arg)
in ((_178_897), (TInt (UInt32))))
in ECast (_178_898))
end else begin
if ((FStar_Util.ends_with c "uint16") && is_known_type) then begin
(let _178_900 = (let _178_899 = (translate_expr env arg)
in ((_178_899), (TInt (UInt16))))
in ECast (_178_900))
end else begin
if ((FStar_Util.ends_with c "uint8") && is_known_type) then begin
(let _178_902 = (let _178_901 = (translate_expr env arg)
in ((_178_901), (TInt (UInt8))))
in ECast (_178_902))
end else begin
if ((FStar_Util.ends_with c "int64") && is_known_type) then begin
(let _178_904 = (let _178_903 = (translate_expr env arg)
in ((_178_903), (TInt (Int64))))
in ECast (_178_904))
end else begin
if ((FStar_Util.ends_with c "int32") && is_known_type) then begin
(let _178_906 = (let _178_905 = (translate_expr env arg)
in ((_178_905), (TInt (Int32))))
in ECast (_178_906))
end else begin
if ((FStar_Util.ends_with c "int16") && is_known_type) then begin
(let _178_908 = (let _178_907 = (translate_expr env arg)
in ((_178_907), (TInt (Int16))))
in ECast (_178_908))
end else begin
if ((FStar_Util.ends_with c "int8") && is_known_type) then begin
(let _178_910 = (let _178_909 = (translate_expr env arg)
in ((_178_909), (TInt (Int8))))
in ECast (_178_910))
end else begin
(let _178_913 = (let _178_912 = (let _178_911 = (translate_expr env arg)
in (_178_911)::[])
in ((EQualified (((("FStar")::("Int")::("Cast")::[]), (c)))), (_178_912)))
in EApp (_178_913))
end
end
end
end
end
end
end
end)
end
| FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (path, function_name); FStar_Extraction_ML_Syntax.mlty = _82_1047; FStar_Extraction_ML_Syntax.loc = _82_1045}, args) -> begin
(let _178_915 = (let _178_914 = (FStar_List.map (translate_expr env) args)
in ((EQualified (((path), (function_name)))), (_178_914)))
in EApp (_178_915))
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t_from, t_to) -> begin
(let _178_918 = (let _178_917 = (translate_expr env e)
in (let _178_916 = (translate_type env t_to)
in ((_178_917), (_178_916))))
in ECast (_178_918))
end
| FStar_Extraction_ML_Syntax.MLE_Record (_82_1062, fields) -> begin
(let _178_923 = (let _178_922 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _178_921 = (FStar_List.map (fun _82_1068 -> (match (_82_1068) with
| (field, expr) -> begin
(let _178_920 = (translate_expr env expr)
in ((field), (_178_920)))
end)) fields)
in ((_178_922), (_178_921))))
in EFlat (_178_923))
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, path) -> begin
(let _178_926 = (let _178_925 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _178_924 = (translate_expr env e)
in ((_178_925), (_178_924), ((Prims.snd path)))))
in EField (_178_926))
end
| FStar_Extraction_ML_Syntax.MLE_Let (_82_1074) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Let]")
end
| FStar_Extraction_ML_Syntax.MLE_App (head, _82_1078) -> begin
(let _178_928 = (let _178_927 = (FStar_Extraction_ML_Code.string_of_mlexpr (([]), ("")) head)
in (FStar_Util.format1 "todo: translate_expr [MLE_App] (head is: %s)" _178_927))
in (FStar_All.failwith _178_928))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (seqs) -> begin
(let _178_929 = (FStar_List.map (translate_expr env) seqs)
in ESequence (_178_929))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let _178_930 = (FStar_List.map (translate_expr env) es)
in ETuple (_178_930))
end
| FStar_Extraction_ML_Syntax.MLE_CTor ((_82_1086, cons), es) -> begin
(let _178_933 = (let _178_932 = (assert_lid env e.FStar_Extraction_ML_Syntax.mlty)
in (let _178_931 = (FStar_List.map (translate_expr env) es)
in ((_178_932), (cons), (_178_931))))
in ECons (_178_933))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (_82_1093) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Fun]")
end
| FStar_Extraction_ML_Syntax.MLE_If (_82_1096) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_If]")
end
| FStar_Extraction_ML_Syntax.MLE_Raise (_82_1099) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Raise]")
end
| FStar_Extraction_ML_Syntax.MLE_Try (_82_1102) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Try]")
end
| FStar_Extraction_ML_Syntax.MLE_Coerce (_82_1105) -> begin
(FStar_All.failwith "todo: translate_expr [MLE_Coerce]")
end))
and assert_lid : env  ->  FStar_Extraction_ML_Syntax.mlty  ->  typ = (fun env t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (ts, lid) -> begin
(let _178_937 = (let _178_936 = (FStar_List.map (translate_type env) ts)
in ((lid), (_178_936)))
in TApp (_178_937))
end
| _82_1114 -> begin
(FStar_All.failwith "invalid argument: assert_lid")
end))
and translate_branches : env  ->  FStar_Extraction_ML_Syntax.mlbranch Prims.list  ->  branches = (fun env branches -> (FStar_List.map (translate_branch env) branches))
and translate_branch : env  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  (pattern * expr) = (fun env _82_1121 -> (match (_82_1121) with
| (pat, guard, expr) -> begin
if (guard = None) then begin
(

let _82_1124 = (translate_pat env pat)
in (match (_82_1124) with
| (env, pat) -> begin
(let _178_942 = (translate_expr env expr)
in ((pat), (_178_942)))
end))
end else begin
(FStar_All.failwith "todo: translate_branch")
end
end))
and translate_pat : env  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  (env * pattern) = (fun env p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Unit) -> begin
((env), (PUnit))
end
| FStar_Extraction_ML_Syntax.MLP_Const (FStar_Extraction_ML_Syntax.MLC_Bool (b)) -> begin
((env), (PBool (b)))
end
| FStar_Extraction_ML_Syntax.MLP_Var (name, _82_1134) -> begin
(

let env = (extend env name false)
in ((env), (PVar ({name = name; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(

let env = (extend env "_" false)
in ((env), (PVar ({name = "_"; typ = TAny; mut = false}))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor ((_82_1141, cons), ps) -> begin
(

let _82_1156 = (FStar_List.fold_left (fun _82_1149 p -> (match (_82_1149) with
| (env, acc) -> begin
(

let _82_1153 = (translate_pat env p)
in (match (_82_1153) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_82_1156) with
| (env, ps) -> begin
((env), (PCons (((cons), ((FStar_List.rev ps))))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Record (_82_1158, ps) -> begin
(

let _82_1173 = (FStar_List.fold_left (fun _82_1164 _82_1167 -> (match (((_82_1164), (_82_1167))) with
| ((env, acc), (field, p)) -> begin
(

let _82_1170 = (translate_pat env p)
in (match (_82_1170) with
| (env, p) -> begin
((env), ((((field), (p)))::acc))
end))
end)) ((env), ([])) ps)
in (match (_82_1173) with
| (env, ps) -> begin
((env), (PRecord ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let _82_1185 = (FStar_List.fold_left (fun _82_1178 p -> (match (_82_1178) with
| (env, acc) -> begin
(

let _82_1182 = (translate_pat env p)
in (match (_82_1182) with
| (env, p) -> begin
((env), ((p)::acc))
end))
end)) ((env), ([])) ps)
in (match (_82_1185) with
| (env, ps) -> begin
((env), (PTuple ((FStar_List.rev ps))))
end))
end
| FStar_Extraction_ML_Syntax.MLP_Const (_82_1187) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Const]")
end
| FStar_Extraction_ML_Syntax.MLP_Branch (_82_1190) -> begin
(FStar_All.failwith "todo: translate_pat [MLP_Branch]")
end))
and translate_constant : FStar_Extraction_ML_Syntax.mlconstant  ->  expr = (fun c -> (match (c) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
EUnit
end
| FStar_Extraction_ML_Syntax.MLC_Bool (b) -> begin
EBool (b)
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_82_1198)) -> begin
(FStar_All.failwith "impossible: machine integer not desugared to a function call")
end
| FStar_Extraction_ML_Syntax.MLC_Float (_82_1203) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Float]")
end
| FStar_Extraction_ML_Syntax.MLC_Char (_82_1206) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Char]")
end
| FStar_Extraction_ML_Syntax.MLC_String (_82_1209) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_String]")
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (_82_1212) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Bytes]")
end
| FStar_Extraction_ML_Syntax.MLC_Int (_82_1215, None) -> begin
(FStar_All.failwith "todo: translate_expr [MLC_Int]")
end))
and mk_op_app : env  ->  width  ->  op  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.list  ->  expr = (fun env w op args -> (let _178_957 = (let _178_956 = (FStar_List.map (translate_expr env) args)
in ((EOp (((op), (w)))), (_178_956)))
in EApp (_178_957)))




