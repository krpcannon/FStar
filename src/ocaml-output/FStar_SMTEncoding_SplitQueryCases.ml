
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _183_14 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_183_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_87_7) -> begin
(let _183_19 = (let _183_16 = (let _183_15 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (_183_15)))
in (FStar_SMTEncoding_Util.mkAnd _183_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _183_19 (fun x -> (let _183_18 = (FStar_SMTEncoding_Util.mkITE ((g), (t), (x)))
in (f _183_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_87_18) -> begin
(let _183_20 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_183_20), (negs), (t)))
end
| _87_21 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_87_27) -> begin
(let _183_31 = (let _183_30 = (let _183_29 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (_183_29)))
in (FStar_SMTEncoding_Util.mkAnd _183_30))
in ((true), (l), (_183_31)))
end
| _87_30 -> begin
(

let _87_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_87_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _183_34 = (let _183_33 = (FStar_SMTEncoding_Util.mkImp ((negs), (t)))
in (_183_33)::l)
in (is_ite_all_the_way n rest negs' _183_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _183_61 = (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x)))
in (f _183_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_87_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _87_59, _87_61, _87_63, _87_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _183_69 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _183_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _87_71) -> begin
(

let _87_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (_87_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _183_78 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _183_78)))), (l), (negs))))
end))
end
| _87_80 -> begin
((false), ((((fun _87_81 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _87_86) -> begin
(

let _87_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue [])
in (match (_87_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _87_94 -> begin
((false), ((((fun _87_95 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_87_100) -> begin
hd
end
| _87_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _183_117 = (let _183_116 = (let _183_115 = (let _183_114 = (f t)
in (FStar_SMTEncoding_Util.mkNot _183_114))
in ((_183_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_183_116))
in (check _183_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _183_138 = (let _183_137 = (let _183_136 = (let _183_135 = (let _183_134 = (FStar_SMTEncoding_Util.mkNot negs)
in (f _183_134))
in (FStar_SMTEncoding_Util.mkNot _183_135))
in ((_183_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_183_137))
in (check _183_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _87_118, _87_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _87_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _87_130 check -> (match (_87_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




