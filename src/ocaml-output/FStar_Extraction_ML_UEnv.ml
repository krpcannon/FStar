
open Prims

type ty_or_exp_b =
((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty), (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool)) FStar_Util.either


type binding =
| Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b)
| Fv of (FStar_Syntax_Syntax.fv * ty_or_exp_b)


let is_Bv = (fun _discr_ -> (match (_discr_) with
| Bv (_) -> begin
true
end
| _ -> begin
false
end))


let is_Fv = (fun _discr_ -> (match (_discr_) with
| Fv (_) -> begin
true
end
| _ -> begin
false
end))


let ___Bv____0 = (fun projectee -> (match (projectee) with
| Bv (_74_6) -> begin
_74_6
end))


let ___Fv____0 = (fun projectee -> (match (projectee) with
| Fv (_74_9) -> begin
_74_9
end))


type env =
{tcenv : FStar_TypeChecker_Env.env; gamma : binding Prims.list; tydefs : (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * FStar_Extraction_ML_Syntax.mltydecl) Prims.list; currentModule : FStar_Extraction_ML_Syntax.mlpath}


let is_Mkenv : env  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv"))))


let debug : env  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun g f -> (

let c = (FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule)
in if (FStar_Options.debug_at_level c (FStar_Options.Other ("Extraction"))) then begin
(f ())
end else begin
()
end))


let mkFvvar : FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.fv = (fun l t -> (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None))


let erasedContent : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.ml_unit_ty


let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun t -> if (t = FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
true
end else begin
(match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Named (_74_22, (("FStar")::("Ghost")::[], "erased")) -> begin
true
end
| _74_31 -> begin
false
end)
end)


let unknownType : FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Top


let prependTick = (fun _74_34 -> (match (_74_34) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
((x), (n))
end else begin
(((Prims.strcat "\'A" x)), (n))
end
end))


let removeTick = (fun _74_37 -> (match (_74_37) with
| (x, n) -> begin
if (FStar_Util.starts_with x "\'") then begin
(let _170_59 = (FStar_Util.substring_from x (Prims.parse_int "1"))
in ((_170_59), (n)))
end else begin
((x), (n))
end
end))


let convRange : FStar_Range.range  ->  Prims.int = (fun r -> (Prims.parse_int "0"))


let convIdent : FStar_Ident.ident  ->  (Prims.string * Prims.int) = (fun id -> ((id.FStar_Ident.idText), ((Prims.parse_int "0"))))


let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (let _170_66 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (prependTick _170_66)))


let bv_as_ml_termvar : FStar_Syntax_Syntax.bv  ->  (Prims.string * Prims.int) = (fun x -> (let _170_69 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in (removeTick _170_69)))


let rec lookup_ty_local : binding Prims.list  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun gamma b -> (match (gamma) with
| (Bv (b', FStar_Util.Inl (mli, mlt)))::tl -> begin
if (FStar_Syntax_Syntax.bv_eq b b') then begin
mlt
end else begin
(lookup_ty_local tl b)
end
end
| (Bv (b', FStar_Util.Inr (_74_56)))::tl -> begin
if (FStar_Syntax_Syntax.bv_eq b b') then begin
(FStar_All.failwith (Prims.strcat "Type/Expr clash: " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end else begin
(lookup_ty_local tl b)
end
end
| (_74_63)::tl -> begin
(lookup_ty_local tl b)
end
| [] -> begin
(FStar_All.failwith (Prims.strcat "extraction: unbound type var " b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText))
end))


let tyscheme_of_td = (fun _74_74 -> (match (_74_74) with
| (_74_67, _74_69, _74_71, vars, body_opt) -> begin
(match (body_opt) with
| Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (t)) -> begin
Some (((vars), (t)))
end
| _74_79 -> begin
None
end)
end))


let lookup_ty_const : env  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme Prims.option = (fun env _74_83 -> (match (_74_83) with
| (module_name, ty_name) -> begin
(FStar_Util.find_map env.tydefs (fun _74_86 -> (match (_74_86) with
| (m, tds) -> begin
if (module_name = m) then begin
(FStar_Util.find_map tds (fun td -> (

let _74_97 = td
in (match (_74_97) with
| (_74_89, n, _74_92, _74_94, _74_96) -> begin
if (n = ty_name) then begin
(tyscheme_of_td td)
end else begin
None
end
end))))
end else begin
None
end
end)))
end))


let module_name_of_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (FStar_All.pipe_right fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ns (FStar_List.map (fun i -> i.FStar_Ident.idText))))


let maybe_mangle_type_projector : env  ->  FStar_Syntax_Syntax.fv  ->  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) Prims.option = (fun env fv -> (

let mname = (module_name_of_fv fv)
in (

let ty_name = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.ident.FStar_Ident.idText
in (FStar_Util.find_map env.tydefs (fun _74_106 -> (match (_74_106) with
| (m, tds) -> begin
(FStar_Util.find_map tds (fun _74_115 -> (match (_74_115) with
| (_74_108, n, mangle_opt, _74_112, _74_114) -> begin
if (m = mname) then begin
if (n = ty_name) then begin
(match (mangle_opt) with
| None -> begin
Some (((m), (n)))
end
| Some (mangled) -> begin
(

let _74_122 = (FStar_Util.prefix m)
in (match (_74_122) with
| (modul, _74_121) -> begin
Some (((modul), (mangled)))
end))
end)
end else begin
None
end
end else begin
None
end
end)))
end))))))


let lookup_tyvar : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bt -> (lookup_ty_local g.gamma bt))


let lookup_fv_by_lid : env  ->  FStar_Ident.lident  ->  ty_or_exp_b = (fun g lid -> (

let x = (FStar_Util.find_map g.gamma (fun _74_1 -> (match (_74_1) with
| Fv (fv', x) when (FStar_Syntax_Syntax.fv_eq_lid fv' lid) -> begin
Some (x)
end
| _74_133 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _170_99 = (FStar_Util.format1 "free Variable %s not found\n" lid.FStar_Ident.nsstr)
in (FStar_All.failwith _170_99))
end
| Some (y) -> begin
y
end)))


let lookup_fv : env  ->  FStar_Syntax_Syntax.fv  ->  ty_or_exp_b = (fun g fv -> (

let x = (FStar_Util.find_map g.gamma (fun _74_2 -> (match (_74_2) with
| Fv (fv', t) when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
Some (t)
end
| _74_146 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _170_107 = (let _170_106 = (FStar_Range.string_of_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p)
in (let _170_105 = (FStar_Syntax_Print.lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format2 "(%s) free Variable %s not found\n" _170_106 _170_105)))
in (FStar_All.failwith _170_107))
end
| Some (y) -> begin
y
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  ty_or_exp_b = (fun g bv -> (

let x = (FStar_Util.find_map g.gamma (fun _74_3 -> (match (_74_3) with
| Bv (bv', r) when (FStar_Syntax_Syntax.bv_eq bv bv') -> begin
Some (r)
end
| _74_159 -> begin
None
end)))
in (match (x) with
| None -> begin
(let _170_115 = (let _170_114 = (FStar_Range.string_of_range bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)
in (let _170_113 = (FStar_Syntax_Print.bv_to_string bv)
in (FStar_Util.format2 "(%s) bound Variable %s not found\n" _170_114 _170_113)))
in (FStar_All.failwith _170_115))
end
| Some (y) -> begin
y
end)))


let lookup : env  ->  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g x -> (match (x) with
| FStar_Util.Inl (x) -> begin
(let _170_120 = (lookup_bv g x)
in ((_170_120), (None)))
end
| FStar_Util.Inr (x) -> begin
(let _170_121 = (lookup_fv g x)
in ((_170_121), (x.FStar_Syntax_Syntax.fv_qual)))
end))


let lookup_term : env  ->  FStar_Syntax_Syntax.term  ->  (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option) = (fun g t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(lookup g (FStar_Util.Inl (x)))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(lookup g (FStar_Util.Inr (x)))
end
| _74_177 -> begin
(FStar_All.failwith "Impossible: lookup_term for a non-name")
end))


let extend_ty : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty Prims.option  ->  env = (fun g a mapped_to -> (

let ml_a = (bv_as_ml_tyvar a)
in (

let mapped_to = (match (mapped_to) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Var (ml_a)
end
| Some (t) -> begin
t
end)
in (

let gamma = (Bv (((a), (FStar_Util.Inl (((ml_a), (mapped_to)))))))::g.gamma
in (

let tcenv = (FStar_TypeChecker_Env.push_bv g.tcenv a)
in (

let _74_188 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _74_188.tydefs; currentModule = _74_188.currentModule}))))))


let extend_bv : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec mk_unit -> (

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _74_200 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mlx = (let _170_144 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLE_Var (_170_144))
in (

let mlx = if mk_unit then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mlx)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
end
end
in (

let gamma = (Bv (((x), (FStar_Util.Inr (((mlx), (t_x), (is_rec)))))))::g.gamma
in (

let tcenv = (let _170_145 = (FStar_Syntax_Syntax.binders_of_list ((x)::[]))
in (FStar_TypeChecker_Env.push_binders g.tcenv _170_145))
in (

let _74_206 = g
in {tcenv = tcenv; gamma = gamma; tydefs = _74_206.tydefs; currentModule = _74_206.currentModule})))))))


let rec mltyFvars : FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlident Prims.list = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(x)::[]
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) -> begin
(let _170_149 = (mltyFvars t1)
in (let _170_148 = (mltyFvars t2)
in (FStar_List.append _170_149 _170_148)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, path) -> begin
(FStar_List.collect mltyFvars args)
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (ts) -> begin
(FStar_List.collect mltyFvars ts)
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
[]
end))


let rec subsetMlidents : FStar_Extraction_ML_Syntax.mlident Prims.list  ->  FStar_Extraction_ML_Syntax.mlident Prims.list  ->  Prims.bool = (fun la lb -> (match (la) with
| (h)::tla -> begin
((FStar_List.contains h lb) && (subsetMlidents tla lb))
end
| [] -> begin
true
end))


let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool = (fun tys -> (let _170_156 = (mltyFvars (Prims.snd tys))
in (subsetMlidents _170_156 (Prims.fst tys))))


let extend_fv' : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x y t_x add_unit is_rec -> if (tySchemeIsClosed t_x) then begin
(

let ml_ty = (match (t_x) with
| ([], t) -> begin
t
end
| _74_240 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end)
in (

let mly = FStar_Extraction_ML_Syntax.MLE_Name ((

let _74_244 = y
in (match (_74_244) with
| (ns, i) -> begin
((ns), ((FStar_Extraction_ML_Syntax.avoid_keyword i)))
end)))
in (

let mly = if add_unit then begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_App ((((FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top mly)), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))))
end else begin
(FStar_Extraction_ML_Syntax.with_ty ml_ty mly)
end
in (

let gamma = (Fv (((x), (FStar_Util.Inr (((mly), (t_x), (is_rec)))))))::g.gamma
in (

let _74_248 = g
in {tcenv = _74_248.tcenv; gamma = gamma; tydefs = _74_248.tydefs; currentModule = _74_248.currentModule})))))
end else begin
(FStar_All.failwith "freevars found")
end)


let extend_fv : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  env = (fun g x t_x add_unit is_rec -> (

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (extend_fv' g x mlp t_x add_unit is_rec)))


let extend_lb : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.typ  ->  FStar_Extraction_ML_Syntax.mltyscheme  ->  Prims.bool  ->  Prims.bool  ->  (env * FStar_Extraction_ML_Syntax.mlident) = (fun g l t t_x add_unit is_rec -> (match (l) with
| FStar_Util.Inl (x) -> begin
(let _170_192 = (extend_bv g x t_x add_unit is_rec false)
in (let _170_191 = (bv_as_ml_termvar x)
in ((_170_192), (_170_191))))
end
| FStar_Util.Inr (f) -> begin
(

let _74_268 = (FStar_Extraction_ML_Syntax.mlpath_of_lident f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_74_268) with
| (p, y) -> begin
(let _170_193 = (extend_fv' g f ((p), (y)) t_x add_unit is_rec)
in ((_170_193), ((((FStar_Extraction_ML_Syntax.avoid_keyword y)), ((Prims.parse_int "0"))))))
end))
end))


let extend_tydef : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  env = (fun g fv td -> (

let m = (module_name_of_fv fv)
in (

let _74_273 = g
in {tcenv = _74_273.tcenv; gamma = _74_273.gamma; tydefs = (((m), (td)))::g.tydefs; currentModule = _74_273.currentModule})))


let emptyMlPath : (Prims.string Prims.list * Prims.string) = (([]), (""))


let mkContext : FStar_TypeChecker_Env.env  ->  env = (fun e -> (

let env = {tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath}
in (

let a = (("\'a"), ((~- ((Prims.parse_int "1")))))
in (

let failwith_ty = (((a)::[]), (FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.MLTY_Named ((([]), (((("Prims")::[]), ("string")))))), (FStar_Extraction_ML_Syntax.E_IMPURE), (FStar_Extraction_ML_Syntax.MLTY_Var (a))))))
in (let _170_204 = (let _170_203 = (let _170_202 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_170_202))
in (extend_lb env _170_203 FStar_Syntax_Syntax.tun failwith_ty false false))
in (FStar_All.pipe_right _170_204 Prims.fst))))))


let monad_op_name : FStar_Syntax_Syntax.eff_decl  ->  Prims.string  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed nm -> (

let _74_283 = ((ed.FStar_Syntax_Syntax.mname.FStar_Ident.ns), (ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident))
in (match (_74_283) with
| (module_name, eff_name) -> begin
(

let mangled_name = (Prims.strcat FStar_Ident.reserved_prefix (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat "_" nm)))
in (

let mangled_lid = (FStar_Ident.lid_of_ids (FStar_List.append module_name (((FStar_Ident.id_of_text mangled_name))::[])))
in (

let ml_name = (FStar_Extraction_ML_Syntax.mlpath_of_lident mangled_lid)
in (

let lid = (FStar_All.pipe_right (FStar_List.append (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname) (((FStar_Ident.id_of_text nm))::[])) FStar_Ident.lid_of_ids)
in ((ml_name), (lid))))))
end)))


let action_name : FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.action  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed a -> (monad_op_name ed a.FStar_Syntax_Syntax.action_name.FStar_Ident.ident.FStar_Ident.idText))


let bind_name : FStar_Syntax_Syntax.eff_decl  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "bind"))


let return_name : FStar_Syntax_Syntax.eff_decl  ->  ((Prims.string Prims.list * Prims.string) * FStar_Ident.lident) = (fun ed -> (monad_op_name ed "return"))




