
open Prims

exception Un_extractable


let is_Un_extractable = (fun _discr_ -> (match (_discr_) with
| Un_extractable (_) -> begin
true
end
| _ -> begin
false
end))


let type_leq : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let type_leq_c : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option) = (fun g t1 t2 -> (FStar_Extraction_ML_Util.type_leq_c (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2))


let erasableType : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g t -> (FStar_Extraction_ML_Util.erasableType (FStar_Extraction_ML_Util.udelta_unfold g) t))


let eraseTypeDeep : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t -> (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold g) t))


let fail = (fun r msg -> (

let _80_18 = (let _176_29 = (let _176_28 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" _176_28 msg))
in (FStar_All.pipe_left FStar_Util.print_string _176_29))
in (FStar_All.failwith msg)))


let err_uninst = (fun env t _80_24 -> (match (_80_24) with
| (vars, ty) -> begin
(let _176_37 = (let _176_36 = (FStar_Syntax_Print.term_to_string t)
in (let _176_35 = (let _176_33 = (FStar_All.pipe_right vars (FStar_List.map Prims.fst))
in (FStar_All.pipe_right _176_33 (FStar_String.concat ", ")))
in (let _176_34 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated" _176_36 _176_35 _176_34))))
in (fail t.FStar_Syntax_Syntax.pos _176_37))
end))


let err_ill_typed_application = (fun env t args ty -> (let _176_47 = (let _176_46 = (FStar_Syntax_Print.term_to_string t)
in (let _176_45 = (let _176_43 = (FStar_All.pipe_right args (FStar_List.map (fun _80_32 -> (match (_80_32) with
| (x, _80_31) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _176_43 (FStar_String.concat " ")))
in (let _176_44 = (FStar_Extraction_ML_Code.string_of_mlty env.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n" _176_46 _176_45 _176_44))))
in (fail t.FStar_Syntax_Syntax.pos _176_47)))


let err_value_restriction = (fun t -> (let _176_51 = (let _176_50 = (FStar_Syntax_Print.tag_of_term t)
in (let _176_49 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Refusing to generalize because of the value restriction: (%s) %s" _176_50 _176_49)))
in (fail t.FStar_Syntax_Syntax.pos _176_51)))


let err_unexpected_eff = (fun t f0 f1 -> (let _176_56 = (let _176_55 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format3 "for expression %s, Expected effect %s; got effect %s" _176_55 (FStar_Extraction_ML_Util.eff_to_string f0) (FStar_Extraction_ML_Util.eff_to_string f1)))
in (fail t.FStar_Syntax_Syntax.pos _176_56)))


let effect_as_etag : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.e_tag = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (

let rec delta_norm_eff = (fun g l -> (match ((FStar_Util.smap_try_find cache l.FStar_Ident.str)) with
| Some (l) -> begin
l
end
| None -> begin
(

let res = (match ((FStar_TypeChecker_Env.lookup_effect_abbrev g.FStar_Extraction_ML_UEnv.tcenv ((FStar_Syntax_Syntax.U_zero)::[]) l)) with
| None -> begin
l
end
| Some (_80_46, c) -> begin
(delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c))
end)
in (

let _80_51 = (FStar_Util.smap_add cache l.FStar_Ident.str res)
in res))
end))
in (fun g l -> (

let l = (delta_norm_eff g l)
in if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
FStar_Extraction_ML_Syntax.E_GHOST
end else begin
FStar_Extraction_ML_Syntax.E_IMPURE
end
end))))


type level_t =
| Term_level
| Type_level
| Kind_level


let is_Term_level = (fun _discr_ -> (match (_discr_) with
| Term_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Type_level = (fun _discr_ -> (match (_discr_) with
| Type_level (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kind_level = (fun _discr_ -> (match (_discr_) with
| Kind_level (_) -> begin
true
end
| _ -> begin
false
end))


let predecessor = (fun t _80_1 -> (match (_80_1) with
| Term_level -> begin
Term_level
end
| Type_level -> begin
Term_level
end
| Kind_level -> begin
Type_level
end))


let rec level : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  level_t = (fun env t -> (

let predecessor = (fun l -> (predecessor t l))
in (

let t = (FStar_Syntax_Subst.compress t)
in (

let _80_68 = (FStar_Extraction_ML_UEnv.debug env (fun _80_66 -> (let _176_78 = (FStar_Syntax_Print.term_to_string t)
in (let _176_77 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.print2 "level %s (%s)\n" _176_78 _176_77)))))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_80_71) -> begin
(let _176_83 = (let _176_82 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: %s" _176_82))
in (FStar_All.failwith _176_83))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_constant (_80_75) -> begin
Term_level
end
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _80_83; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (_80_80); FStar_Syntax_Syntax.fv_qual = _80_78}) -> begin
(

let t' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Iota))::[]) env.FStar_Extraction_ML_UEnv.tcenv t)
in (

let _80_88 = (FStar_Extraction_ML_UEnv.debug env (fun _80_87 -> (match (()) with
| () -> begin
(let _176_86 = (FStar_Syntax_Print.term_to_string t)
in (let _176_85 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Normalized %s to %s\n" _176_86 _176_85)))
end)))
in (level env t')))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (FStar_TypeChecker_Env.is_type_constructor env.FStar_Extraction_ML_UEnv.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) then begin
Type_level
end else begin
(let _176_87 = (level env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (FStar_All.pipe_left predecessor _176_87))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (_, t)) | (FStar_Syntax_Syntax.Tm_bvar ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) | (FStar_Syntax_Syntax.Tm_name ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t})) -> begin
(let _176_88 = (level env t)
in (FStar_All.pipe_left predecessor _176_88))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _80_111, _80_113) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_type (_80_117) -> begin
Kind_level
end
| FStar_Syntax_Syntax.Tm_uinst (t, _80_121) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_refine (x, _80_126) -> begin
(match ((level env x.FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((level env (FStar_Syntax_Util.comp_result c))) with
| Term_level -> begin
Type_level
end
| l -> begin
l
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _80_140) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_let (_80_144, body) -> begin
(level env body)
end
| FStar_Syntax_Syntax.Tm_match (_80_149, branches) -> begin
(match (branches) with
| ((_80_156, _80_158, e))::_80_154 -> begin
(level env e)
end
| _80_163 -> begin
(FStar_All.failwith "Empty branches")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, _80_166) -> begin
(level env t)
end
| FStar_Syntax_Syntax.Tm_app (head, _80_171) -> begin
(level env head)
end)))))


let is_type : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((level env t)) with
| Term_level -> begin
false
end
| _80_178 -> begin
true
end))


let is_type_binder = (fun env x -> (match ((level env (Prims.fst x).FStar_Syntax_Syntax.sort)) with
| Term_level -> begin
(FStar_All.failwith "Impossible: Binder is a term")
end
| Type_level -> begin
false
end
| Kind_level -> begin
true
end))


let is_constructor : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _176_97 = (FStar_Syntax_Subst.compress t)
in _176_97.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _80_204 -> begin
false
end))


let rec is_fstar_value : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _176_100 = (FStar_Syntax_Subst.compress t)
in _176_100.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
if (is_constructor head) then begin
(FStar_All.pipe_right args (FStar_List.for_all (fun _80_225 -> (match (_80_225) with
| (te, _80_224) -> begin
(is_fstar_value te)
end))))
end else begin
false
end
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(is_fstar_value t)
end
| _80_238 -> begin
false
end))


let rec is_ml_value : FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.bool = (fun e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Const (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) | (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Fun (_)) -> begin
true
end
| (FStar_Extraction_ML_Syntax.MLE_CTor (_, exps)) | (FStar_Extraction_ML_Syntax.MLE_Tuple (exps)) -> begin
(FStar_Util.for_all is_ml_value exps)
end
| FStar_Extraction_ML_Syntax.MLE_Record (_80_259, fields) -> begin
(FStar_Util.for_all (fun _80_266 -> (match (_80_266) with
| (_80_264, e) -> begin
(is_ml_value e)
end)) fields)
end
| _80_268 -> begin
false
end))


let normalize_abs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t0 -> (

let rec aux = (fun bs t copt -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs', body, copt) -> begin
(aux (FStar_List.append bs bs') body copt)
end
| _80_281 -> begin
(

let e' = (FStar_Syntax_Util.unascribe t)
in if (FStar_Syntax_Util.is_fun e') then begin
(aux bs e' copt)
end else begin
(FStar_Syntax_Util.abs bs e' copt)
end)
end)))
in (aux [] t0 None)))


let unit_binder : FStar_Syntax_Syntax.binder = (let _176_113 = (FStar_Syntax_Syntax.new_bv None FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _176_113))


let check_pats_for_ite : (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term Prims.option) = (fun l -> (

let def = ((false), (None), (None))
in if ((FStar_List.length l) <> (Prims.parse_int "2")) then begin
def
end else begin
(

let _80_288 = (FStar_List.hd l)
in (match (_80_288) with
| (p1, w1, e1) -> begin
(

let _80_292 = (let _176_116 = (FStar_List.tl l)
in (FStar_List.hd _176_116))
in (match (_80_292) with
| (p2, w2, e2) -> begin
(match (((w1), (w2), (p1.FStar_Syntax_Syntax.v), (p2.FStar_Syntax_Syntax.v))) with
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) -> begin
((true), (Some (e1)), (Some (e2)))
end
| (None, None, FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false)), FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) -> begin
((true), (Some (e2)), (Some (e1)))
end
| _80_312 -> begin
def
end)
end))
end))
end))


let instantiate : FStar_Extraction_ML_Syntax.mltyscheme  ->  FStar_Extraction_ML_Syntax.mlty Prims.list  ->  FStar_Extraction_ML_Syntax.mlty = (fun s args -> (FStar_Extraction_ML_Util.subst s args))


let erasable : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.bool = (fun g f t -> ((f = FStar_Extraction_ML_Syntax.E_GHOST) || ((f = FStar_Extraction_ML_Syntax.E_PURE) && (erasableType g t))))


let erase : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g e ty f -> (

let e = if (erasable g f ty) then begin
if (type_leq g ty FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
FStar_Extraction_ML_Syntax.ml_unit
end else begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_Coerce (((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.ml_unit_ty), (ty)))))
end
end else begin
e
end
in ((e), (f), (ty))))


let maybe_coerce : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g e ty expect -> (

let ty = (eraseTypeDeep g ty)
in (match ((type_leq_c g (Some (e)) ty expect)) with
| (true, Some (e')) -> begin
e'
end
| _80_333 -> begin
(

let _80_335 = (FStar_Extraction_ML_UEnv.debug g (fun _80_334 -> (match (()) with
| () -> begin
(let _176_146 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _176_145 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (let _176_144 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule expect)
in (FStar_Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n" _176_146 _176_145 _176_144))))
end)))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty expect) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (ty), (expect))))))
end)))


let bv_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Extraction_ML_Syntax.mlty = (fun g bv -> (match ((FStar_Extraction_ML_UEnv.lookup_bv g bv)) with
| FStar_Util.Inl (_80_340, t) -> begin
t
end
| _80_345 -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end))


let rec term_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun g t0 -> (

let rec is_top_ty = (fun t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
true
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_80_352) -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| None -> begin
false
end
| Some (t) -> begin
(is_top_ty t)
end)
end
| _80_358 -> begin
false
end))
in (

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (

let mlt = (term_as_mlty' g t)
in if (is_top_ty mlt) then begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t0)
in (term_as_mlty' g t))
end else begin
mlt
end))))
and term_as_mlty' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.mlty = (fun env t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _176_169 = (let _176_168 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Impossible: Unexpected term %s" _176_168))
in (FStar_All.failwith _176_169))
end
| FStar_Syntax_Syntax.Tm_constant (_80_373) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| FStar_Syntax_Syntax.Tm_uvar (_80_376) -> begin
FStar_Extraction_ML_UEnv.unknownType
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) -> begin
(term_as_mlty' env t)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv [])
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _80_412 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_80_412) with
| (bs, c) -> begin
(

let _80_415 = (binders_as_ml_binders env bs)
in (match (_80_415) with
| (mlbs, env) -> begin
(

let t_ret = (

let eff = (FStar_TypeChecker_Env.norm_eff_name env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.comp_effect_name c))
in (

let ed = (FStar_TypeChecker_Env.get_effect_decl env.FStar_Extraction_ML_UEnv.tcenv eff)
in if (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) then begin
(

let t = (FStar_TypeChecker_Util.reify_comp env.FStar_Extraction_ML_UEnv.tcenv (FStar_Syntax_Util.lcomp_of_comp c) FStar_Syntax_Syntax.U_unknown)
in (

let res = (term_as_mlty' env t)
in res))
end else begin
(term_as_mlty' env (FStar_Syntax_Util.comp_result c))
end))
in (

let erase = (effect_as_etag env (FStar_Syntax_Util.comp_effect_name c))
in (

let _80_432 = (FStar_List.fold_right (fun _80_425 _80_428 -> (match (((_80_425), (_80_428))) with
| ((_80_423, t), (tag, t')) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((t), (tag), (t')))))
end)) mlbs ((erase), (t_ret)))
in (match (_80_432) with
| (_80_430, t) -> begin
t
end))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let res = (match ((let _176_172 = (FStar_Syntax_Util.un_uinst head)
in _176_172.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(bv_as_mlty env bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(fv_app_as_mlty env fv args)
end
| FStar_Syntax_Syntax.Tm_app (head, args') -> begin
(let _176_173 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), ((FStar_List.append args' args))))) None t.FStar_Syntax_Syntax.pos)
in (term_as_mlty' env _176_173))
end
| _80_446 -> begin
FStar_Extraction_ML_UEnv.unknownType
end)
in res)
end
| FStar_Syntax_Syntax.Tm_abs (bs, ty, _80_451) -> begin
(

let _80_456 = (FStar_Syntax_Subst.open_term bs ty)
in (match (_80_456) with
| (bs, ty) -> begin
(

let _80_459 = (binders_as_ml_binders env bs)
in (match (_80_459) with
| (bts, env) -> begin
(term_as_mlty' env ty)
end))
end))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
FStar_Extraction_ML_UEnv.unknownType
end)))
and arg_as_mlty : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  FStar_Extraction_ML_Syntax.mlty = (fun g _80_473 -> (match (_80_473) with
| (a, _80_472) -> begin
if (is_type g a) then begin
(term_as_mlty' g a)
end else begin
FStar_Extraction_ML_UEnv.erasedContent
end
end))
and fv_app_as_mlty : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.args  ->  FStar_Extraction_ML_Syntax.mlty = (fun g fv args -> (

let _80_479 = (FStar_Syntax_Util.arrow_formals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.ty)
in (match (_80_479) with
| (formals, t) -> begin
(

let mlargs = (FStar_List.map (arg_as_mlty g) args)
in (

let mlargs = (

let n_args = (FStar_List.length args)
in if ((FStar_List.length formals) > n_args) then begin
(

let _80_485 = (FStar_Util.first_N n_args formals)
in (match (_80_485) with
| (_80_483, rest) -> begin
(let _176_180 = (FStar_List.map (fun _80_486 -> FStar_Extraction_ML_UEnv.erasedContent) rest)
in (FStar_List.append mlargs _176_180))
end))
end else begin
mlargs
end)
in (

let nm = (match ((FStar_Extraction_ML_UEnv.maybe_mangle_type_projector g fv)) with
| Some (p) -> begin
p
end
| None -> begin
(FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in FStar_Extraction_ML_Syntax.MLTY_Named (((mlargs), (nm))))))
end)))
and binders_as_ml_binders : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty) Prims.list * FStar_Extraction_ML_UEnv.env) = (fun g bs -> (

let _80_508 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _80_497 b -> (match (_80_497) with
| (ml_bs, env) -> begin
if (is_type_binder g b) then begin
(

let b = (Prims.fst b)
in (

let env = (FStar_Extraction_ML_UEnv.extend_ty env b (Some (FStar_Extraction_ML_Syntax.MLTY_Top)))
in (

let ml_b = (let _176_185 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_176_185), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
in (((ml_b)::ml_bs), (env)))))
end else begin
(

let b = (Prims.fst b)
in (

let t = (term_as_mlty env b.FStar_Syntax_Syntax.sort)
in (

let env = (FStar_Extraction_ML_UEnv.extend_bv env b (([]), (t)) false false false)
in (

let ml_b = (let _176_186 = (FStar_Extraction_ML_UEnv.bv_as_ml_termvar b)
in ((_176_186), (t)))
in (((ml_b)::ml_bs), (env))))))
end
end)) (([]), (g))))
in (match (_80_508) with
| (ml_bs, env) -> begin
(((FStar_List.rev ml_bs)), (env))
end)))


let mk_MLE_Seq : FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun e1 e2 -> (match (((e1.FStar_Extraction_ML_Syntax.expr), (e2.FStar_Extraction_ML_Syntax.expr))) with
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 es2))
end
| (FStar_Extraction_ML_Syntax.MLE_Seq (es1), _80_519) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((FStar_List.append es1 ((e2)::[])))
end
| (_80_522, FStar_Extraction_ML_Syntax.MLE_Seq (es2)) -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::es2)
end
| _80_527 -> begin
FStar_Extraction_ML_Syntax.MLE_Seq ((e1)::(e2)::[])
end))


let mk_MLE_Let : Prims.bool  ->  FStar_Extraction_ML_Syntax.mlletbinding  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr' = (fun top_level lbs body -> (match (lbs) with
| (FStar_Extraction_ML_Syntax.NonRec, quals, (lb)::[]) when (not (top_level)) -> begin
(match (lb.FStar_Extraction_ML_Syntax.mllb_tysc) with
| Some ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
if (body.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) then begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end else begin
(match (body.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Var (x) when (x = lb.FStar_Extraction_ML_Syntax.mllb_name) -> begin
lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr
end
| _80_543 when (lb.FStar_Extraction_ML_Syntax.mllb_def.FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr) -> begin
body.FStar_Extraction_ML_Syntax.expr
end
| _80_545 -> begin
(mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def body)
end)
end
end
| _80_547 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end)
end
| _80_549 -> begin
FStar_Extraction_ML_Syntax.MLE_Let (((lbs), (body)))
end))


let resugar_pat : FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Extraction_ML_Syntax.mlpattern = (fun q p -> (match (p) with
| FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) -> begin
(match ((FStar_Extraction_ML_Util.is_xtuple d)) with
| Some (n) -> begin
FStar_Extraction_ML_Syntax.MLP_Tuple (pats)
end
| _80_559 -> begin
(match (q) with
| Some (FStar_Syntax_Syntax.Record_ctor (_80_561, fns)) -> begin
(

let p = (FStar_Extraction_ML_Util.record_field_path fns)
in (

let fs = (FStar_Extraction_ML_Util.record_fields fns pats)
in FStar_Extraction_ML_Syntax.MLP_Record (((p), (fs)))))
end
| _80_569 -> begin
p
end)
end)
end
| _80_571 -> begin
p
end))


let extract_pat : FStar_Extraction_ML_UEnv.env  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_UEnv.env * (FStar_Extraction_ML_Syntax.mlpattern * FStar_Extraction_ML_Syntax.mlexpr Prims.option) Prims.list * Prims.bool) = (fun g p expected_t -> (

let rec extract_one_pat = (fun disjunctive_pat imp g p expected_topt -> (

let ok = (fun t -> (match (expected_topt) with
| None -> begin
true
end
| Some (t') -> begin
(

let ok = (type_leq g t t')
in (

let _80_589 = if (not (ok)) then begin
(FStar_Extraction_ML_UEnv.debug g (fun _80_587 -> (let _176_221 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t')
in (let _176_220 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t)
in (FStar_Util.print2 "Expected pattern type %s; got pattern type %s\n" _176_221 _176_220)))))
end else begin
()
end
in ok))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_80_592) -> begin
(FStar_All.failwith "Impossible: Nested disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int (c, None)) -> begin
(

let i = FStar_Const.Const_int (((c), (None)))
in (

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (

let when_clause = (let _176_230 = (let _176_229 = (let _176_228 = (let _176_227 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (let _176_226 = (let _176_225 = (let _176_224 = (let _176_223 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p i)
in (FStar_All.pipe_left (fun _176_222 -> FStar_Extraction_ML_Syntax.MLE_Const (_176_222)) _176_223))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty) _176_224))
in (_176_225)::[])
in (_176_227)::_176_226))
in ((FStar_Extraction_ML_Util.prims_op_equality), (_176_228)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_229))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _176_230))
in (let _176_231 = (ok FStar_Extraction_ML_Syntax.ml_int_ty)
in ((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Var (x)), ((when_clause)::[])))), (_176_231))))))
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(

let t = (FStar_TypeChecker_TcTerm.tc_constant FStar_Range.dummyRange s)
in (

let mlty = (term_as_mlty g t)
in (let _176_236 = (let _176_234 = (let _176_233 = (let _176_232 = (FStar_Extraction_ML_Util.mlconst_of_const' p.FStar_Syntax_Syntax.p s)
in FStar_Extraction_ML_Syntax.MLP_Const (_176_232))
in ((_176_233), ([])))
in Some (_176_234))
in (let _176_235 = (ok mlty)
in ((g), (_176_236), (_176_235))))))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _176_241 = if imp then begin
None
end else begin
(let _176_239 = (let _176_238 = (let _176_237 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_176_237))
in ((_176_238), ([])))
in Some (_176_239))
end
in (let _176_240 = (ok mlty)
in ((g), (_176_241), (_176_240))))))
end
| FStar_Syntax_Syntax.Pat_wild (x) when disjunctive_pat -> begin
((g), (Some (((FStar_Extraction_ML_Syntax.MLP_Wild), ([])))), (true))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let mlty = (term_as_mlty g x.FStar_Syntax_Syntax.sort)
in (

let g = (FStar_Extraction_ML_UEnv.extend_bv g x (([]), (mlty)) false false imp)
in (let _176_246 = if imp then begin
None
end else begin
(let _176_244 = (let _176_243 = (let _176_242 = (FStar_Extraction_ML_Syntax.bv_as_mlident x)
in FStar_Extraction_ML_Syntax.MLP_Var (_176_242))
in ((_176_243), ([])))
in Some (_176_244))
end
in (let _176_245 = (ok mlty)
in ((g), (_176_246), (_176_245))))))
end
| FStar_Syntax_Syntax.Pat_dot_term (_80_617) -> begin
((g), (None), (true))
end
| FStar_Syntax_Syntax.Pat_cons (f, pats) -> begin
(

let _80_639 = (match ((FStar_Extraction_ML_UEnv.lookup_fv g f)) with
| FStar_Util.Inr ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (n); FStar_Extraction_ML_Syntax.mlty = _80_626; FStar_Extraction_ML_Syntax.loc = _80_624}, ttys, _80_632) -> begin
((n), (ttys))
end
| _80_636 -> begin
(FStar_All.failwith "Expected a constructor")
end)
in (match (_80_639) with
| (d, tys) -> begin
(

let nTyVars = (FStar_List.length (Prims.fst tys))
in (

let _80_643 = (FStar_Util.first_N nTyVars pats)
in (match (_80_643) with
| (tysVarPats, restPats) -> begin
(

let f_ty_opt = try
(match (()) with
| () -> begin
(

let mlty_args = (FStar_All.pipe_right tysVarPats (FStar_List.map (fun _80_653 -> (match (_80_653) with
| (p, _80_652) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (_80_655, t) -> begin
(term_as_mlty g t)
end
| _80_660 -> begin
(

let _80_663 = (FStar_Extraction_ML_UEnv.debug g (fun _80_661 -> (let _176_250 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print1 "Pattern %s is not extractable" _176_250))))
in (Prims.raise Un_extractable))
end)
end))))
in (

let f_ty = (FStar_Extraction_ML_Util.subst tys mlty_args)
in (let _176_251 = (FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty)
in Some (_176_251))))
end)
with
| Un_extractable -> begin
None
end
in (

let _80_679 = (FStar_Util.fold_map (fun g _80_671 -> (match (_80_671) with
| (p, imp) -> begin
(

let _80_676 = (extract_one_pat disjunctive_pat true g p None)
in (match (_80_676) with
| (g, p, _80_675) -> begin
((g), (p))
end))
end)) g tysVarPats)
in (match (_80_679) with
| (g, tyMLPats) -> begin
(

let _80_706 = (FStar_Util.fold_map (fun _80_682 _80_685 -> (match (((_80_682), (_80_685))) with
| ((g, f_ty_opt), (p, imp)) -> begin
(

let _80_696 = (match (f_ty_opt) with
| Some ((hd)::rest, res) -> begin
((Some (((rest), (res)))), (Some (hd)))
end
| _80_693 -> begin
((None), (None))
end)
in (match (_80_696) with
| (f_ty_opt, expected_ty) -> begin
(

let _80_701 = (extract_one_pat disjunctive_pat false g p expected_ty)
in (match (_80_701) with
| (g, p, _80_700) -> begin
((((g), (f_ty_opt))), (p))
end))
end))
end)) ((g), (f_ty_opt)) restPats)
in (match (_80_706) with
| ((g, f_ty_opt), restMLPats) -> begin
(

let _80_714 = (let _176_258 = (FStar_All.pipe_right (FStar_List.append tyMLPats restMLPats) (FStar_List.collect (fun _80_2 -> (match (_80_2) with
| Some (x) -> begin
(x)::[]
end
| _80_711 -> begin
[]
end))))
in (FStar_All.pipe_right _176_258 FStar_List.split))
in (match (_80_714) with
| (mlPats, when_clauses) -> begin
(

let pat_ty_compat = (match (f_ty_opt) with
| Some ([], t) -> begin
(ok t)
end
| _80_720 -> begin
false
end)
in (let _176_262 = (let _176_261 = (let _176_260 = (resugar_pat f.FStar_Syntax_Syntax.fv_qual (FStar_Extraction_ML_Syntax.MLP_CTor (((d), (mlPats)))))
in (let _176_259 = (FStar_All.pipe_right when_clauses FStar_List.flatten)
in ((_176_260), (_176_259))))
in Some (_176_261))
in ((g), (_176_262), (pat_ty_compat))))
end))
end))
end)))
end)))
end))
end)))
in (

let extract_one_pat = (fun disj g p expected_t -> (match ((extract_one_pat disj false g p expected_t)) with
| (g, Some (x, v), b) -> begin
((g), (((x), (v))), (b))
end
| _80_735 -> begin
(FStar_All.failwith "Impossible: Unable to translate pattern")
end))
in (

let mk_when_clause = (fun whens -> (match (whens) with
| [] -> begin
None
end
| (hd)::tl -> begin
(let _176_273 = (FStar_List.fold_left FStar_Extraction_ML_Util.conjoin hd tl)
in Some (_176_273))
end))
in (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: Empty disjunctive pattern")
end
| FStar_Syntax_Syntax.Pat_disj ((p)::pats) -> begin
(

let _80_751 = (extract_one_pat true g p (Some (expected_t)))
in (match (_80_751) with
| (g, p, b) -> begin
(

let _80_761 = (FStar_Util.fold_map (fun b p -> (

let _80_758 = (extract_one_pat true g p (Some (expected_t)))
in (match (_80_758) with
| (_80_755, p, b') -> begin
(((b && b')), (p))
end))) b pats)
in (match (_80_761) with
| (b, ps) -> begin
(

let ps = (p)::ps
in (

let _80_776 = (FStar_All.pipe_right ps (FStar_List.partition (fun _80_3 -> (match (_80_3) with
| (_80_765, (_80_769)::_80_767) -> begin
true
end
| _80_773 -> begin
false
end))))
in (match (_80_776) with
| (ps_when, rest) -> begin
(

let ps = (FStar_All.pipe_right ps_when (FStar_List.map (fun _80_779 -> (match (_80_779) with
| (x, whens) -> begin
(let _176_278 = (mk_when_clause whens)
in ((x), (_176_278)))
end))))
in (

let res = (match (rest) with
| [] -> begin
((g), (ps), (b))
end
| rest -> begin
(let _176_282 = (let _176_281 = (let _176_280 = (let _176_279 = (FStar_List.map Prims.fst rest)
in FStar_Extraction_ML_Syntax.MLP_Branch (_176_279))
in ((_176_280), (None)))
in (_176_281)::ps)
in ((g), (_176_282), (b)))
end)
in res))
end)))
end))
end))
end
| _80_785 -> begin
(

let _80_791 = (extract_one_pat false g p (Some (expected_t)))
in (match (_80_791) with
| (g, (p, whens), b) -> begin
(

let when_clause = (mk_when_clause whens)
in ((g), ((((p), (when_clause)))::[]), (b)))
end))
end)))))


let maybe_eta_data_and_project_record : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv_qual Prims.option  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr = (fun g qual residualType mlAppExpr -> (

let rec eta_args = (fun more_args t -> (match (t) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (t0, _80_802, t1) -> begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _176_297 = (let _176_296 = (let _176_295 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t0) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in ((((x), (t0))), (_176_295)))
in (_176_296)::more_args)
in (eta_args _176_297 t1)))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (_80_808, _80_810) -> begin
(((FStar_List.rev more_args)), (t))
end
| _80_814 -> begin
(FStar_All.failwith "Impossible: Head type is not an arrow")
end))
in (

let as_record = (fun qual e -> (match (((e.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (FStar_Extraction_ML_Syntax.MLE_CTor (_80_819, args), Some (FStar_Syntax_Syntax.Record_ctor (_80_824, fields))) -> begin
(

let path = (FStar_Extraction_ML_Util.record_field_path fields)
in (

let fields = (FStar_Extraction_ML_Util.record_fields fields args)
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Record (((path), (fields)))))))
end
| _80_833 -> begin
e
end))
in (

let resugar_and_maybe_eta = (fun qual e -> (

let _80_839 = (eta_args [] residualType)
in (match (_80_839) with
| (eargs, tres) -> begin
(match (eargs) with
| [] -> begin
(let _176_306 = (as_record qual e)
in (FStar_Extraction_ML_Util.resugar_exp _176_306))
end
| _80_842 -> begin
(

let _80_845 = (FStar_List.unzip eargs)
in (match (_80_845) with
| (binders, eargs) -> begin
(match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_CTor (head, args) -> begin
(

let body = (let _176_308 = (let _176_307 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tres) (FStar_Extraction_ML_Syntax.MLE_CTor (((head), ((FStar_List.append args eargs))))))
in (FStar_All.pipe_left (as_record qual) _176_307))
in (FStar_All.pipe_left FStar_Extraction_ML_Util.resugar_exp _176_308))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty e.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Fun (((binders), (body))))))
end
| _80_852 -> begin
(FStar_All.failwith "Impossible: Not a constructor")
end)
end))
end)
end)))
in (match (((mlAppExpr.FStar_Extraction_ML_Syntax.expr), (qual))) with
| (_80_854, None) -> begin
mlAppExpr
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _80_860; FStar_Extraction_ML_Syntax.loc = _80_858}, (mle)::args), Some (FStar_Syntax_Syntax.Record_projector (f))) -> begin
(

let fn = (FStar_Extraction_ML_Util.mlpath_of_lid f)
in (

let proj = FStar_Extraction_ML_Syntax.MLE_Proj (((mle), (fn)))
in (

let e = (match (args) with
| [] -> begin
proj
end
| _80_877 -> begin
(let _176_310 = (let _176_309 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) proj)
in ((_176_309), (args)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_310))
end)
in (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty e))))
end
| ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (mlp); FStar_Extraction_ML_Syntax.mlty = _; FStar_Extraction_ML_Syntax.loc = _}, mlargs), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _176_311 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), (mlargs)))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _176_311))
end
| ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Data_ctor))) | ((FStar_Extraction_ML_Syntax.MLE_Name (mlp), Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(let _176_312 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty mlAppExpr.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_CTor (((mlp), ([])))))
in (FStar_All.pipe_left (resugar_and_maybe_eta qual) _176_312))
end
| _80_917 -> begin
mlAppExpr
end)))))


let maybe_downgrade_eff : FStar_Extraction_ML_UEnv.env  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Extraction_ML_Syntax.e_tag = (fun g f t -> if ((f = FStar_Extraction_ML_Syntax.E_GHOST) && (type_leq g t FStar_Extraction_ML_Syntax.ml_unit_ty)) then begin
FStar_Extraction_ML_Syntax.E_PURE
end else begin
f
end)


let rec term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g t -> (

let _80_926 = (term_as_mlexpr' g t)
in (match (_80_926) with
| (e, tag, ty) -> begin
(

let tag = (maybe_downgrade_eff g tag ty)
in (

let _80_929 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _176_337 = (let _176_336 = (FStar_Syntax_Print.tag_of_term t)
in (let _176_335 = (FStar_Syntax_Print.term_to_string t)
in (let _176_334 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule ty)
in (FStar_Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n" _176_336 _176_335 _176_334 (FStar_Extraction_ML_Util.eff_to_string tag)))))
in (FStar_Util.print_string _176_337))))
in (erase g e ty tag)))
end)))
and check_term_as_mlexpr : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g t f ty -> (

let _80_937 = (check_term_as_mlexpr' g t f ty)
in (match (_80_937) with
| (e, t) -> begin
(

let _80_942 = (erase g e t f)
in (match (_80_942) with
| (r, _80_940, t) -> begin
((r), (t))
end))
end)))
and check_term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Extraction_ML_Syntax.e_tag  ->  FStar_Extraction_ML_Syntax.mlty  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlty) = (fun g e0 f ty -> (

let _80_950 = (term_as_mlexpr g e0)
in (match (_80_950) with
| (e, tag, t) -> begin
(

let tag = (maybe_downgrade_eff g tag t)
in if (FStar_Extraction_ML_Util.eff_leq tag f) then begin
(let _176_346 = (maybe_coerce g e t ty)
in ((_176_346), (ty)))
end else begin
(err_unexpected_eff e0 f tag)
end)
end)))
and term_as_mlexpr' : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag * FStar_Extraction_ML_Syntax.mlty) = (fun g top -> (

let _80_955 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (let _176_353 = (let _176_352 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _176_351 = (FStar_Syntax_Print.tag_of_term top)
in (let _176_350 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format3 "%s: term_as_mlexpr\' (%s) :  %s \n" _176_352 _176_351 _176_350))))
in (FStar_Util.print_string _176_353))))
in (

let t = (FStar_Syntax_Subst.compress top)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) -> begin
(let _176_355 = (let _176_354 = (FStar_Syntax_Print.tag_of_term t)
in (FStar_Util.format1 "Impossible: Unexpected term: %s" _176_354))
in (FStar_All.failwith _176_355))
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc)) -> begin
(match ((term_as_mlexpr' g t)) with
| ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let ((FStar_Extraction_ML_Syntax.NonRec, flags, bodies), continuation); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}, tag, typ) -> begin
(({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Let (((((FStar_Extraction_ML_Syntax.NonRec), ((FStar_Extraction_ML_Syntax.Mutable)::flags), (bodies))), (continuation))); FStar_Extraction_ML_Syntax.mlty = mlty; FStar_Extraction_ML_Syntax.loc = loc}), (tag), (typ))
end
| _80_996 -> begin
(FStar_All.failwith "impossible")
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, _80_1000)) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) when (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl g.FStar_Extraction_ML_UEnv.tcenv m)
in if (let _176_356 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _176_356 Prims.op_Negation)) then begin
(term_as_mlexpr' g t)
end else begin
(

let ml_result_ty_1 = (term_as_mlty g lb.FStar_Syntax_Syntax.lbtyp)
in (

let _80_1020 = (term_as_mlexpr g lb.FStar_Syntax_Syntax.lbdef)
in (match (_80_1020) with
| (comp_1, _80_1017, _80_1019) -> begin
(

let _80_1039 = (

let k = (let _176_359 = (let _176_358 = (let _176_357 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_All.pipe_right _176_357 FStar_Syntax_Syntax.mk_binder))
in (_176_358)::[])
in (FStar_Syntax_Util.abs _176_359 body None))
in (

let _80_1026 = (term_as_mlexpr g k)
in (match (_80_1026) with
| (ml_k, _80_1024, t_k) -> begin
(

let m_2 = (match (t_k) with
| FStar_Extraction_ML_Syntax.MLTY_Fun (_80_1028, _80_1030, m_2) -> begin
m_2
end
| _80_1035 -> begin
(FStar_All.failwith "Impossible")
end)
in ((ml_k), (m_2)))
end)))
in (match (_80_1039) with
| (ml_k, ty) -> begin
(

let bind = (let _176_362 = (let _176_361 = (let _176_360 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (FStar_All.pipe_right _176_360 Prims.fst))
in FStar_Extraction_ML_Syntax.MLE_Name (_176_361))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) _176_362))
in (let _176_363 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty ty) (FStar_Extraction_ML_Syntax.MLE_App (((bind), ((comp_1)::(ml_k)::[])))))
in ((_176_363), (FStar_Extraction_ML_Syntax.E_IMPURE), (ty))))
end))
end)))
end)
end
| _80_1042 -> begin
(term_as_mlexpr' g t)
end))
end
| (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_uinst (t, _)) -> begin
(term_as_mlexpr' g t)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let _80_1059 = (FStar_TypeChecker_TcTerm.type_of_tot_term g.FStar_Extraction_ML_UEnv.tcenv t)
in (match (_80_1059) with
| (_80_1055, ty, _80_1058) -> begin
(

let ml_ty = (term_as_mlty g ty)
in (let _176_367 = (let _176_366 = (let _176_365 = (FStar_Extraction_ML_Util.mlconst_of_const' t.FStar_Syntax_Syntax.pos c)
in (FStar_All.pipe_left (fun _176_364 -> FStar_Extraction_ML_Syntax.MLE_Const (_176_364)) _176_365))
in (FStar_Extraction_ML_Syntax.with_ty ml_ty _176_366))
in ((_176_367), (FStar_Extraction_ML_Syntax.E_PURE), (ml_ty))))
end))
end
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(match ((FStar_Extraction_ML_UEnv.lookup_term g t)) with
| (FStar_Util.Inl (_80_1068), _80_1071) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end
| (FStar_Util.Inr (x, mltys, _80_1076), qual) -> begin
(match (mltys) with
| ([], t) when (t = FStar_Extraction_ML_Syntax.ml_unit_ty) -> begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (t))
end
| ([], t) -> begin
(let _176_368 = (maybe_eta_data_and_project_record g qual t x)
in ((_176_368), (FStar_Extraction_ML_Syntax.E_PURE), (t)))
end
| _80_1088 -> begin
(err_uninst g t mltys)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, copt) -> begin
(

let _80_1096 = (FStar_Syntax_Subst.open_term bs body)
in (match (_80_1096) with
| (bs, body) -> begin
(

let _80_1099 = (binders_as_ml_binders g bs)
in (match (_80_1099) with
| (ml_bs, env) -> begin
(

let _80_1103 = (term_as_mlexpr env body)
in (match (_80_1103) with
| (ml_body, f, t) -> begin
(

let _80_1113 = (FStar_List.fold_right (fun _80_1107 _80_1110 -> (match (((_80_1107), (_80_1110))) with
| ((_80_1105, targ), (f, t)) -> begin
((FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.MLTY_Fun (((targ), (f), (t)))))
end)) ml_bs ((f), (t)))
in (match (_80_1113) with
| (f, tfun) -> begin
(let _176_371 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty tfun) (FStar_Extraction_ML_Syntax.MLE_Fun (((ml_bs), (ml_body)))))
in ((_176_371), (f), (tfun)))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _80_1119; FStar_Syntax_Syntax.pos = _80_1117; FStar_Syntax_Syntax.vars = _80_1115}, (t)::[]) -> begin
(

let _80_1130 = (term_as_mlexpr' g (Prims.fst t))
in (match (_80_1130) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_PURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_80_1138)); FStar_Syntax_Syntax.tk = _80_1136; FStar_Syntax_Syntax.pos = _80_1134; FStar_Syntax_Syntax.vars = _80_1132}, (t)::[]) -> begin
(

let _80_1149 = (term_as_mlexpr' g (Prims.fst t))
in (match (_80_1149) with
| (ml, e_tag, mlty) -> begin
((ml), (FStar_Extraction_ML_Syntax.E_IMPURE), (mlty))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let is_total = (fun _80_4 -> (match (_80_4) with
| FStar_Util.Inl (l) -> begin
(FStar_Syntax_Util.is_total_lcomp l)
end
| FStar_Util.Inr (l) -> begin
(FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid)
end))
in (match ((let _176_375 = (let _176_374 = (FStar_Syntax_Subst.compress head)
in _176_374.FStar_Syntax_Syntax.n)
in ((head.FStar_Syntax_Syntax.n), (_176_375)))) with
| (FStar_Syntax_Syntax.Tm_uvar (_80_1161), _80_1164) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| (_80_1168, FStar_Syntax_Syntax.Tm_abs (bs, _80_1171, Some (lc))) when (is_total lc) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Iota)::(FStar_TypeChecker_Normalize.Zeta)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) g.FStar_Extraction_ML_UEnv.tcenv t)
in (term_as_mlexpr' g t))
end
| _80_1179 -> begin
(

let rec extract_app = (fun is_data _80_1184 _80_1187 restArgs -> (match (((_80_1184), (_80_1187))) with
| ((mlhead, mlargs_f), (f, t)) -> begin
(match (((restArgs), (t))) with
| ([], _80_1191) -> begin
(

let evaluation_order_guaranteed = ((((FStar_List.length mlargs_f) = (Prims.parse_int "1")) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = {FStar_Syntax_Syntax.v = v; FStar_Syntax_Syntax.ty = _80_1200; FStar_Syntax_Syntax.p = _80_1198}; FStar_Syntax_Syntax.fv_delta = _80_1196; FStar_Syntax_Syntax.fv_qual = _80_1194}) -> begin
((v = FStar_Syntax_Const.op_And) || (v = FStar_Syntax_Const.op_Or))
end
| _80_1206 -> begin
false
end))
in (

let _80_1217 = if evaluation_order_guaranteed then begin
(let _176_384 = (FStar_All.pipe_right (FStar_List.rev mlargs_f) (FStar_List.map Prims.fst))
in (([]), (_176_384)))
end else begin
(FStar_List.fold_left (fun _80_1210 _80_1213 -> (match (((_80_1210), (_80_1213))) with
| ((lbs, out_args), (arg, f)) -> begin
if ((f = FStar_Extraction_ML_Syntax.E_PURE) || (f = FStar_Extraction_ML_Syntax.E_GHOST)) then begin
((lbs), ((arg)::out_args))
end else begin
(

let x = (FStar_Extraction_ML_Syntax.gensym ())
in (let _176_388 = (let _176_387 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty arg.FStar_Extraction_ML_Syntax.mlty) (FStar_Extraction_ML_Syntax.MLE_Var (x)))
in (_176_387)::out_args)
in (((((x), (arg)))::lbs), (_176_388))))
end
end)) (([]), ([])) mlargs_f)
end
in (match (_80_1217) with
| (lbs, mlargs) -> begin
(

let app = (let _176_389 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t) (FStar_Extraction_ML_Syntax.MLE_App (((mlhead), (mlargs)))))
in (FStar_All.pipe_left (maybe_eta_data_and_project_record g is_data t) _176_389))
in (

let l_app = (FStar_List.fold_right (fun _80_1221 out -> (match (_80_1221) with
| (x, arg) -> begin
(FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty out.FStar_Extraction_ML_Syntax.mlty) (mk_MLE_Let false ((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = x; FStar_Extraction_ML_Syntax.mllb_tysc = Some ((([]), (arg.FStar_Extraction_ML_Syntax.mlty))); FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = arg; FStar_Extraction_ML_Syntax.print_typ = true})::[])) out))
end)) lbs app)
in ((l_app), (f), (t))))
end)))
end
| (((arg, _80_1227))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (formal_t, f', t)) when (is_type g arg) -> begin
if (type_leq g formal_t FStar_Extraction_ML_Syntax.ml_unit_ty) then begin
(let _176_393 = (let _176_392 = (FStar_Extraction_ML_Util.join arg.FStar_Syntax_Syntax.pos f f')
in ((_176_392), (t)))
in (extract_app is_data ((mlhead), ((((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE)))::mlargs_f)) _176_393 rest))
end else begin
(let _176_398 = (let _176_397 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule mlhead)
in (let _176_396 = (FStar_Syntax_Print.term_to_string arg)
in (let _176_395 = (FStar_Syntax_Print.tag_of_term arg)
in (let _176_394 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule formal_t)
in (FStar_Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" _176_397 _176_396 _176_395 _176_394)))))
in (FStar_All.failwith _176_398))
end
end
| (((e0, _80_1239))::rest, FStar_Extraction_ML_Syntax.MLTY_Fun (tExpected, f', t)) -> begin
(

let r = e0.FStar_Syntax_Syntax.pos
in (

let _80_1252 = (term_as_mlexpr g e0)
in (match (_80_1252) with
| (e0, f0, tInferred) -> begin
(

let e0 = (maybe_coerce g e0 tInferred tExpected)
in (let _176_400 = (let _176_399 = (FStar_Extraction_ML_Util.join_l r ((f)::(f')::(f0)::[]))
in ((_176_399), (t)))
in (extract_app is_data ((mlhead), ((((e0), (f0)))::mlargs_f)) _176_400 rest)))
end)))
end
| _80_1255 -> begin
(match ((FStar_Extraction_ML_Util.udelta_unfold g t)) with
| Some (t) -> begin
(extract_app is_data ((mlhead), (mlargs_f)) ((f), (t)) restArgs)
end
| None -> begin
(err_ill_typed_application g top restArgs t)
end)
end)
end))
in (

let extract_app_maybe_projector = (fun is_data mlhead _80_1264 args -> (match (_80_1264) with
| (f, t) -> begin
(match (is_data) with
| Some (FStar_Syntax_Syntax.Record_projector (_80_1267)) -> begin
(

let rec remove_implicits = (fun args f t -> (match (((args), (t))) with
| (((a0, Some (FStar_Syntax_Syntax.Implicit (_80_1277))))::args, FStar_Extraction_ML_Syntax.MLTY_Fun (_80_1283, f', t)) -> begin
(let _176_415 = (FStar_Extraction_ML_Util.join a0.FStar_Syntax_Syntax.pos f f')
in (remove_implicits args _176_415 t))
end
| _80_1290 -> begin
((args), (f), (t))
end))
in (

let _80_1294 = (remove_implicits args f t)
in (match (_80_1294) with
| (args, f, t) -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)))
end
| _80_1296 -> begin
(extract_app is_data ((mlhead), ([])) ((f), (t)) args)
end)
end))
in if (is_type g t) then begin
((FStar_Extraction_ML_Syntax.ml_unit), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty))
end else begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let _80_1317 = (match ((FStar_Extraction_ML_UEnv.lookup_term g head)) with
| (FStar_Util.Inr (u), q) -> begin
((u), (q))
end
| _80_1309 -> begin
(FStar_All.failwith "FIXME Ty")
end)
in (match (_80_1317) with
| ((head_ml, (vars, t), inst_ok), qual) -> begin
(

let has_typ_apps = (match (args) with
| ((a, _80_1322))::_80_1319 -> begin
(is_type g a)
end
| _80_1326 -> begin
false
end)
in (

let _80_1372 = (match (vars) with
| (_80_1331)::_80_1329 when ((not (has_typ_apps)) && inst_ok) -> begin
((head_ml), (t), (args))
end
| _80_1334 -> begin
(

let n = (FStar_List.length vars)
in if (n <= (FStar_List.length args)) then begin
(

let _80_1338 = (FStar_Util.first_N n args)
in (match (_80_1338) with
| (prefix, rest) -> begin
(

let prefixAsMLTypes = (FStar_List.map (fun _80_1342 -> (match (_80_1342) with
| (x, _80_1341) -> begin
(term_as_mlty g x)
end)) prefix)
in (

let t = (instantiate ((vars), (t)) prefixAsMLTypes)
in (

let head = (match (head_ml.FStar_Extraction_ML_Syntax.expr) with
| (FStar_Extraction_ML_Syntax.MLE_Name (_)) | (FStar_Extraction_ML_Syntax.MLE_Var (_)) -> begin
(

let _80_1351 = head_ml
in {FStar_Extraction_ML_Syntax.expr = _80_1351.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = t; FStar_Extraction_ML_Syntax.loc = _80_1351.FStar_Extraction_ML_Syntax.loc})
end
| FStar_Extraction_ML_Syntax.MLE_App (head, ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Unit); FStar_Extraction_ML_Syntax.mlty = _80_1357; FStar_Extraction_ML_Syntax.loc = _80_1355})::[]) -> begin
(FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLE_App ((((

let _80_1364 = head
in {FStar_Extraction_ML_Syntax.expr = _80_1364.FStar_Extraction_ML_Syntax.expr; FStar_Extraction_ML_Syntax.mlty = FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), (t))); FStar_Extraction_ML_Syntax.loc = _80_1364.FStar_Extraction_ML_Syntax.loc})), ((FStar_Extraction_ML_Syntax.ml_unit)::[])))) (FStar_Extraction_ML_Syntax.with_ty t))
end
| _80_1367 -> begin
(FStar_All.failwith "Impossible: Unexpected head term")
end)
in ((head), (t), (rest)))))
end))
end else begin
(err_uninst g head ((vars), (t)))
end)
end)
in (match (_80_1372) with
| (head_ml, head_t, args) -> begin
(match (args) with
| [] -> begin
(let _176_417 = (maybe_eta_data_and_project_record g qual head_t head_ml)
in ((_176_417), (FStar_Extraction_ML_Syntax.E_PURE), (head_t)))
end
| _80_1375 -> begin
(extract_app_maybe_projector qual head_ml ((FStar_Extraction_ML_Syntax.E_PURE), (head_t)) args)
end)
end)))
end))
end
| _80_1377 -> begin
(

let _80_1381 = (term_as_mlexpr g head)
in (match (_80_1381) with
| (head, f, t) -> begin
(extract_app_maybe_projector None head ((f), (t)) args)
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e0, tc, f) -> begin
(

let t = (match (tc) with
| FStar_Util.Inl (t) -> begin
(term_as_mlty g t)
end
| FStar_Util.Inr (c) -> begin
(term_as_mlty g (FStar_Syntax_Util.comp_result c))
end)
in (

let f = (match (f) with
| None -> begin
(FStar_All.failwith "Ascription node with an empty effect label")
end
| Some (l) -> begin
(effect_as_etag g l)
end)
in (

let _80_1398 = (check_term_as_mlexpr g e0 f t)
in (match (_80_1398) with
| (e, t) -> begin
((e), (f), (t))
end))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), e') -> begin
(

let top_level = (FStar_Syntax_Syntax.is_top_level lbs)
in (

let _80_1414 = if is_rec then begin
(FStar_Syntax_Subst.open_let_rec lbs e')
end else begin
if (FStar_Syntax_Syntax.is_top_level lbs) then begin
((lbs), (e'))
end else begin
(

let lb = (FStar_List.hd lbs)
in (

let x = (let _176_418 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _176_418))
in (

let lb = (

let _80_1408 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _80_1408.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _80_1408.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _80_1408.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _80_1408.FStar_Syntax_Syntax.lbdef})
in (

let e' = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (x))))::[]) e')
in (((lb)::[]), (e'))))))
end
end
in (match (_80_1414) with
| (lbs, e') -> begin
(

let lbs = if top_level then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let tcenv = (let _176_420 = (FStar_Ident.lid_of_path (FStar_List.append (Prims.fst g.FStar_Extraction_ML_UEnv.currentModule) (((Prims.snd g.FStar_Extraction_ML_UEnv.currentModule))::[])) FStar_Range.dummyRange)
in (FStar_TypeChecker_Env.set_current_module g.FStar_Extraction_ML_UEnv.tcenv _176_420))
in (

let lbdef = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.Inlining)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.PureSubtermsWithinComputations)::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv lb.FStar_Syntax_Syntax.lbdef)
in (

let _80_1418 = lb
in {FStar_Syntax_Syntax.lbname = _80_1418.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _80_1418.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _80_1418.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _80_1418.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbdef}))))))
end else begin
lbs
end
in (

let maybe_generalize = (fun _80_1428 -> (match (_80_1428) with
| {FStar_Syntax_Syntax.lbname = lbname_; FStar_Syntax_Syntax.lbunivs = _80_1426; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = lbeff; FStar_Syntax_Syntax.lbdef = e} -> begin
(

let f_e = (effect_as_etag g lbeff)
in (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when (let _176_423 = (FStar_List.hd bs)
in (FStar_All.pipe_right _176_423 (is_type_binder g))) -> begin
(

let _80_1437 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_80_1437) with
| (bs, c) -> begin
(

let _80_1447 = (match ((FStar_Util.prefix_until (fun x -> (not ((is_type_binder g x)))) bs)) with
| None -> begin
((bs), ((FStar_Syntax_Util.comp_result c)))
end
| Some (bs, b, rest) -> begin
(let _176_425 = (FStar_Syntax_Util.arrow ((b)::rest) c)
in ((bs), (_176_425)))
end)
in (match (_80_1447) with
| (tbinders, tbody) -> begin
(

let n_tbinders = (FStar_List.length tbinders)
in (

let e = (normalize_abs e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _80_1453) -> begin
(

let _80_1458 = (FStar_Syntax_Subst.open_term bs body)
in (match (_80_1458) with
| (bs, body) -> begin
if (n_tbinders <= (FStar_List.length bs)) then begin
(

let _80_1461 = (FStar_Util.first_N n_tbinders bs)
in (match (_80_1461) with
| (targs, rest_args) -> begin
(

let expected_source_ty = (

let s = (FStar_List.map2 (fun _80_1465 _80_1469 -> (match (((_80_1465), (_80_1469))) with
| ((x, _80_1464), (y, _80_1468)) -> begin
(let _176_429 = (let _176_428 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_176_428)))
in FStar_Syntax_Syntax.NT (_176_429))
end)) tbinders targs)
in (FStar_Syntax_Subst.subst s tbody))
in (

let env = (FStar_List.fold_left (fun env _80_1476 -> (match (_80_1476) with
| (a, _80_1475) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g targs)
in (

let expected_t = (term_as_mlty env expected_source_ty)
in (

let polytype = (let _176_433 = (FStar_All.pipe_right targs (FStar_List.map (fun _80_1482 -> (match (_80_1482) with
| (x, _80_1481) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_176_433), (expected_t)))
in (

let add_unit = (match (rest_args) with
| [] -> begin
(not ((is_fstar_value body)))
end
| _80_1486 -> begin
false
end)
in (

let rest_args = if add_unit then begin
(unit_binder)::rest_args
end else begin
rest_args
end
in (

let body = (match (rest_args) with
| [] -> begin
body
end
| _80_1491 -> begin
(FStar_Syntax_Util.abs rest_args body None)
end)
in ((lbname_), (f_e), (((t), (((targs), (polytype))))), (add_unit), (body)))))))))
end))
end else begin
(FStar_All.failwith "Not enough type binders")
end
end))
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let env = (FStar_List.fold_left (fun env _80_1506 -> (match (_80_1506) with
| (a, _80_1505) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) g tbinders)
in (

let expected_t = (term_as_mlty env tbody)
in (

let polytype = (let _176_437 = (FStar_All.pipe_right tbinders (FStar_List.map (fun _80_1512 -> (match (_80_1512) with
| (x, _80_1511) -> begin
(FStar_Extraction_ML_UEnv.bv_as_ml_tyvar x)
end))))
in ((_176_437), (expected_t)))
in (

let args = (FStar_All.pipe_right tbinders (FStar_List.map (fun _80_1517 -> (match (_80_1517) with
| (bv, _80_1516) -> begin
(let _176_439 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_All.pipe_right _176_439 FStar_Syntax_Syntax.as_arg))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((e), (args)))) None e.FStar_Syntax_Syntax.pos)
in ((lbname_), (f_e), (((t), (((tbinders), (polytype))))), (false), (e)))))))
end
| _80_1521 -> begin
(err_value_restriction e)
end)))
end))
end))
end
| _80_1523 -> begin
(

let expected_t = (term_as_mlty g t)
in ((lbname_), (f_e), (((t), ((([]), ((([]), (expected_t))))))), (false), (e)))
end)))
end))
in (

let check_lb = (fun env _80_1538 -> (match (_80_1538) with
| (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) -> begin
(

let env = (FStar_List.fold_left (fun env _80_1543 -> (match (_80_1543) with
| (a, _80_1542) -> begin
(FStar_Extraction_ML_UEnv.extend_ty env a None)
end)) env targs)
in (

let expected_t = if add_unit then begin
FStar_Extraction_ML_Syntax.MLTY_Fun (((FStar_Extraction_ML_Syntax.ml_unit_ty), (FStar_Extraction_ML_Syntax.E_PURE), ((Prims.snd polytype))))
end else begin
(Prims.snd polytype)
end
in (

let _80_1549 = (check_term_as_mlexpr env e f expected_t)
in (match (_80_1549) with
| (e, _80_1548) -> begin
(

let f = (maybe_downgrade_eff env f expected_t)
in ((f), ({FStar_Extraction_ML_Syntax.mllb_name = nm; FStar_Extraction_ML_Syntax.mllb_tysc = Some (polytype); FStar_Extraction_ML_Syntax.mllb_add_unit = add_unit; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = true})))
end))))
end))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map maybe_generalize))
in (

let _80_1574 = (FStar_List.fold_right (fun lb _80_1555 -> (match (_80_1555) with
| (env, lbs) -> begin
(

let _80_1568 = lb
in (match (_80_1568) with
| (lbname, _80_1558, (t, (_80_1561, polytype)), add_unit, _80_1567) -> begin
(

let _80_1571 = (FStar_Extraction_ML_UEnv.extend_lb env lbname t polytype add_unit true)
in (match (_80_1571) with
| (env, nm) -> begin
((env), ((((nm), (lb)))::lbs))
end))
end))
end)) lbs ((g), ([])))
in (match (_80_1574) with
| (env_body, lbs) -> begin
(

let env_def = if is_rec then begin
env_body
end else begin
g
end
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (check_lb env_def)))
in (

let e'_rng = e'.FStar_Syntax_Syntax.pos
in (

let _80_1581 = (term_as_mlexpr env_body e')
in (match (_80_1581) with
| (e', f', t') -> begin
(

let f = (let _176_449 = (let _176_448 = (FStar_List.map Prims.fst lbs)
in (f')::_176_448)
in (FStar_Extraction_ML_Util.join_l e'_rng _176_449))
in (

let is_rec = if (is_rec = true) then begin
FStar_Extraction_ML_Syntax.Rec
end else begin
FStar_Extraction_ML_Syntax.NonRec
end
in (let _176_454 = (let _176_453 = (let _176_451 = (let _176_450 = (FStar_List.map Prims.snd lbs)
in ((is_rec), ([]), (_176_450)))
in (mk_MLE_Let top_level _176_451 e'))
in (let _176_452 = (FStar_Extraction_ML_Util.mlloc_of_range t.FStar_Syntax_Syntax.pos)
in (FStar_Extraction_ML_Syntax.with_ty_loc t' _176_453 _176_452)))
in ((_176_454), (f), (t')))))
end)))))
end))))))
end)))
end
| FStar_Syntax_Syntax.Tm_match (scrutinee, pats) -> begin
(

let _80_1591 = (term_as_mlexpr g scrutinee)
in (match (_80_1591) with
| (e, f_e, t_e) -> begin
(

let _80_1595 = (check_pats_for_ite pats)
in (match (_80_1595) with
| (b, then_e, else_e) -> begin
(

let no_lift = (fun x t -> x)
in if b then begin
(match (((then_e), (else_e))) with
| (Some (then_e), Some (else_e)) -> begin
(

let _80_1607 = (term_as_mlexpr g then_e)
in (match (_80_1607) with
| (then_mle, f_then, t_then) -> begin
(

let _80_1611 = (term_as_mlexpr g else_e)
in (match (_80_1611) with
| (else_mle, f_else, t_else) -> begin
(

let _80_1614 = if (type_leq g t_then t_else) then begin
((t_else), (no_lift))
end else begin
if (type_leq g t_else t_then) then begin
((t_then), (no_lift))
end else begin
((FStar_Extraction_ML_Syntax.MLTY_Top), (FStar_Extraction_ML_Syntax.apply_obj_repr))
end
end
in (match (_80_1614) with
| (t_branch, maybe_lift) -> begin
(let _176_485 = (let _176_483 = (let _176_482 = (let _176_481 = (maybe_lift then_mle t_then)
in (let _176_480 = (let _176_479 = (maybe_lift else_mle t_else)
in Some (_176_479))
in ((e), (_176_481), (_176_480))))
in FStar_Extraction_ML_Syntax.MLE_If (_176_482))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_branch) _176_483))
in (let _176_484 = (FStar_Extraction_ML_Util.join then_e.FStar_Syntax_Syntax.pos f_then f_else)
in ((_176_485), (_176_484), (t_branch))))
end))
end))
end))
end
| _80_1616 -> begin
(FStar_All.failwith "ITE pats matched but then and else expressions not found?")
end)
end else begin
(

let _80_1648 = (FStar_All.pipe_right pats (FStar_Util.fold_map (fun compat br -> (

let _80_1622 = (FStar_Syntax_Subst.open_branch br)
in (match (_80_1622) with
| (pat, when_opt, branch) -> begin
(

let _80_1626 = (extract_pat g pat t_e)
in (match (_80_1626) with
| (env, p, pat_t_compat) -> begin
(

let _80_1637 = (match (when_opt) with
| None -> begin
((None), (FStar_Extraction_ML_Syntax.E_PURE))
end
| Some (w) -> begin
(

let _80_1633 = (term_as_mlexpr env w)
in (match (_80_1633) with
| (w, f_w, t_w) -> begin
(

let w = (maybe_coerce env w t_w FStar_Extraction_ML_Syntax.ml_bool_ty)
in ((Some (w)), (f_w)))
end))
end)
in (match (_80_1637) with
| (when_opt, f_when) -> begin
(

let _80_1641 = (term_as_mlexpr env branch)
in (match (_80_1641) with
| (mlbranch, f_branch, t_branch) -> begin
(let _176_489 = (FStar_All.pipe_right p (FStar_List.map (fun _80_1644 -> (match (_80_1644) with
| (p, wopt) -> begin
(

let when_clause = (FStar_Extraction_ML_Util.conjoin_opt wopt when_opt)
in ((p), (((when_clause), (f_when))), (((mlbranch), (f_branch), (t_branch)))))
end))))
in (((compat && pat_t_compat)), (_176_489)))
end))
end))
end))
end))) true))
in (match (_80_1648) with
| (pat_t_compat, mlbranches) -> begin
(

let mlbranches = (FStar_List.flatten mlbranches)
in (

let e = if pat_t_compat then begin
e
end else begin
(

let _80_1652 = (FStar_Extraction_ML_UEnv.debug g (fun _80_1650 -> (let _176_492 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule e)
in (let _176_491 = (FStar_Extraction_ML_Code.string_of_mlty g.FStar_Extraction_ML_UEnv.currentModule t_e)
in (FStar_Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n" _176_492 _176_491)))))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_e) (FStar_Extraction_ML_Syntax.MLE_Coerce (((e), (t_e), (FStar_Extraction_ML_Syntax.MLTY_Top))))))
end
in (match (mlbranches) with
| [] -> begin
(

let _80_1661 = (let _176_494 = (let _176_493 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Extraction_ML_UEnv.lookup_fv g _176_493))
in (FStar_All.pipe_left FStar_Util.right _176_494))
in (match (_80_1661) with
| (fw, _80_1658, _80_1660) -> begin
(let _176_499 = (let _176_498 = (let _176_497 = (let _176_496 = (let _176_495 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_string_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_String ("unreachable"))))
in (_176_495)::[])
in ((fw), (_176_496)))
in FStar_Extraction_ML_Syntax.MLE_App (_176_497))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_unit_ty) _176_498))
in ((_176_499), (FStar_Extraction_ML_Syntax.E_PURE), (FStar_Extraction_ML_Syntax.ml_unit_ty)))
end))
end
| ((_80_1664, _80_1666, (_80_1668, f_first, t_first)))::rest -> begin
(

let _80_1694 = (FStar_List.fold_left (fun _80_1676 _80_1686 -> (match (((_80_1676), (_80_1686))) with
| ((topt, f), (_80_1678, _80_1680, (_80_1682, f_branch, t_branch))) -> begin
(

let f = (FStar_Extraction_ML_Util.join top.FStar_Syntax_Syntax.pos f f_branch)
in (

let topt = (match (topt) with
| None -> begin
None
end
| Some (t) -> begin
if (type_leq g t t_branch) then begin
Some (t_branch)
end else begin
if (type_leq g t_branch t) then begin
Some (t)
end else begin
None
end
end
end)
in ((topt), (f))))
end)) ((Some (t_first)), (f_first)) rest)
in (match (_80_1694) with
| (topt, f_match) -> begin
(

let mlbranches = (FStar_All.pipe_right mlbranches (FStar_List.map (fun _80_1705 -> (match (_80_1705) with
| (p, (wopt, _80_1698), (b, _80_1702, t)) -> begin
(

let b = (match (topt) with
| None -> begin
(FStar_Extraction_ML_Syntax.apply_obj_repr b t)
end
| Some (_80_1708) -> begin
b
end)
in ((p), (wopt), (b)))
end))))
in (

let t_match = (match (topt) with
| None -> begin
FStar_Extraction_ML_Syntax.MLTY_Top
end
| Some (t) -> begin
t
end)
in (let _176_503 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty t_match) (FStar_Extraction_ML_Syntax.MLE_Match (((e), (mlbranches)))))
in ((_176_503), (f_match), (t_match)))))
end))
end)))
end))
end)
end))
end))
end))))


let fresh : Prims.string  ->  (Prims.string * Prims.int) = (

let c = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun x -> (

let _80_1718 = (FStar_Util.incr c)
in (let _176_506 = (FStar_ST.read c)
in ((x), (_176_506))))))


let ind_discriminator_body : FStar_Extraction_ML_UEnv.env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  FStar_Extraction_ML_Syntax.mlmodule1 = (fun env discName constrName -> (

let _80_1726 = (FStar_TypeChecker_Env.lookup_lid env.FStar_Extraction_ML_UEnv.tcenv discName)
in (match (_80_1726) with
| (_80_1724, fstar_disc_type) -> begin
(

let wildcards = (match ((let _176_513 = (FStar_Syntax_Subst.compress fstar_disc_type)
in _176_513.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _80_1729) -> begin
(let _176_517 = (FStar_All.pipe_right binders (FStar_List.filter (fun _80_5 -> (match (_80_5) with
| (_80_1734, Some (FStar_Syntax_Syntax.Implicit (_80_1736))) -> begin
true
end
| _80_1741 -> begin
false
end))))
in (FStar_All.pipe_right _176_517 (FStar_List.map (fun _80_1742 -> (let _176_516 = (fresh "_")
in ((_176_516), (FStar_Extraction_ML_Syntax.MLTY_Top)))))))
end
| _80_1745 -> begin
(FStar_All.failwith "Discriminator must be a function")
end)
in (

let mlid = (fresh "_discr_")
in (

let targ = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top
in (

let discrBody = (let _176_532 = (let _176_531 = (let _176_530 = (let _176_529 = (let _176_528 = (let _176_527 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty targ) (FStar_Extraction_ML_Syntax.MLE_Name ((([]), ((FStar_Extraction_ML_Syntax.idsym mlid))))))
in (let _176_526 = (let _176_525 = (let _176_521 = (let _176_519 = (let _176_518 = (FStar_Extraction_ML_Syntax.mlpath_of_lident constrName)
in ((_176_518), ((FStar_Extraction_ML_Syntax.MLP_Wild)::[])))
in FStar_Extraction_ML_Syntax.MLP_CTor (_176_519))
in (let _176_520 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (true))))
in ((_176_521), (None), (_176_520))))
in (let _176_524 = (let _176_523 = (let _176_522 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) (FStar_Extraction_ML_Syntax.MLE_Const (FStar_Extraction_ML_Syntax.MLC_Bool (false))))
in ((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (_176_522)))
in (_176_523)::[])
in (_176_525)::_176_524))
in ((_176_527), (_176_526))))
in FStar_Extraction_ML_Syntax.MLE_Match (_176_528))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_bool_ty) _176_529))
in (((FStar_List.append wildcards ((((mlid), (targ)))::[]))), (_176_530)))
in FStar_Extraction_ML_Syntax.MLE_Fun (_176_531))
in (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty disc_ty) _176_532))
in FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), (({FStar_Extraction_ML_Syntax.mllb_name = (FStar_Extraction_ML_UEnv.convIdent discName.FStar_Ident.ident); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = discrBody; FStar_Extraction_ML_Syntax.print_typ = false})::[]))))))))
end)))




