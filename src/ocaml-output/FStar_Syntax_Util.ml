
open Prims

let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Ident.mk_ident (((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText)), (lid.FStar_Ident.ident.FStar_Ident.idRange))))::[]))))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let arg_of_non_null_binder = (fun _39_16 -> (match (_39_16) with
| (b, imp) -> begin
(let _135_6 = (FStar_Syntax_Syntax.bv_to_name b)
in ((_135_6), (imp)))
end))


let args_of_non_null_binders : FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
[]
end else begin
(let _135_10 = (arg_of_non_null_binder b)
in (_135_10)::[])
end))))


let args_of_binders : FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _135_17 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(

let b = (let _135_14 = (FStar_Syntax_Syntax.new_bv None (Prims.fst b).FStar_Syntax_Syntax.sort)
in ((_135_14), ((Prims.snd b))))
in (let _135_15 = (arg_of_non_null_binder b)
in ((b), (_135_15))))
end else begin
(let _135_16 = (arg_of_non_null_binder b)
in ((b), (_135_16)))
end)))
in (FStar_All.pipe_right _135_17 FStar_List.unzip)))


let name_binders : FStar_Syntax_Syntax.binder Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
(

let _39_27 = b
in (match (_39_27) with
| (a, imp) -> begin
(

let b = (let _135_23 = (let _135_22 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _135_22))
in (FStar_Ident.id_of_text _135_23))
in (

let b = {FStar_Syntax_Syntax.ppname = b; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = a.FStar_Syntax_Syntax.sort}
in ((b), (imp))))
end))
end else begin
b
end))))


let name_function_binders = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (binders, comp) -> begin
(let _135_27 = (let _135_26 = (let _135_25 = (name_binders binders)
in ((_135_25), (comp)))
in FStar_Syntax_Syntax.Tm_arrow (_135_26))
in (FStar_Syntax_Syntax.mk _135_27 None t.FStar_Syntax_Syntax.pos))
end
| _39_36 -> begin
t
end))


let null_binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _39_40 -> (match (_39_40) with
| (t, imp) -> begin
(let _135_32 = (let _135_31 = (FStar_Syntax_Syntax.null_binder t)
in (FStar_All.pipe_left Prims.fst _135_31))
in ((_135_32), (imp)))
end)))))


let binders_of_tks : (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _39_44 -> (match (_39_44) with
| (t, imp) -> begin
(let _135_36 = (FStar_Syntax_Syntax.new_bv (Some (t.FStar_Syntax_Syntax.pos)) t)
in ((_135_36), (imp)))
end)))))


let binders_of_freevars : FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.binder Prims.list = (fun fvs -> (let _135_39 = (FStar_Util.set_elements fvs)
in (FStar_All.pipe_right _135_39 (FStar_List.map FStar_Syntax_Syntax.mk_binder))))


let mk_subst = (fun s -> (s)::[])


let subst_of_list : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.subst_t = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.fold_right2 (fun f a out -> (FStar_Syntax_Syntax.NT ((((Prims.fst f)), ((Prims.fst a)))))::out) formals actuals [])
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)


let rename_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun replace_xs with_ys -> if ((FStar_List.length replace_xs) = (FStar_List.length with_ys)) then begin
(FStar_List.map2 (fun _39_57 _39_61 -> (match (((_39_57), (_39_61))) with
| ((x, _39_56), (y, _39_60)) -> begin
(let _135_55 = (let _135_54 = (FStar_Syntax_Syntax.bv_to_name y)
in ((x), (_135_54)))
in FStar_Syntax_Syntax.NT (_135_55))
end)) replace_xs with_ys)
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)


let rec unmeta : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (e, _)) | (FStar_Syntax_Syntax.Tm_ascribed (e, _, _)) -> begin
(unmeta e)
end
| _39_76 -> begin
e
end)))


let rec univ_kernel : FStar_Syntax_Syntax.universe  ->  (FStar_Syntax_Syntax.universe * Prims.int) = (fun u -> (match (u) with
| (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
((u), ((Prims.parse_int "0")))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let _39_90 = (univ_kernel u)
in (match (_39_90) with
| (k, n) -> begin
((k), ((n + (Prims.parse_int "1"))))
end))
end
| FStar_Syntax_Syntax.U_max (_39_92) -> begin
(FStar_All.failwith "Imposible: univ_kernel (U_max _)")
end
| FStar_Syntax_Syntax.U_bvar (_39_95) -> begin
(FStar_All.failwith "Imposible: univ_kernel (U_bvar _)")
end))


let constant_univ_as_nat : FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u -> (let _135_62 = (univ_kernel u)
in (Prims.snd _135_62)))


let rec compare_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.int = (fun u1 u2 -> (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) -> begin
(FStar_All.failwith "Impossible: compare_univs")
end
| (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_unknown, _39_117) -> begin
(~- ((Prims.parse_int "1")))
end
| (_39_120, FStar_Syntax_Syntax.U_unknown) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "0")
end
| (FStar_Syntax_Syntax.U_zero, _39_128) -> begin
(~- ((Prims.parse_int "1")))
end
| (_39_131, FStar_Syntax_Syntax.U_zero) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_name (u1), FStar_Syntax_Syntax.U_name (u2)) -> begin
(FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText)
end
| (FStar_Syntax_Syntax.U_name (_39_140), FStar_Syntax_Syntax.U_unif (_39_143)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Syntax_Syntax.U_unif (_39_147), FStar_Syntax_Syntax.U_name (_39_150)) -> begin
(Prims.parse_int "1")
end
| (FStar_Syntax_Syntax.U_unif (u1), FStar_Syntax_Syntax.U_unif (u2)) -> begin
((FStar_Unionfind.uvar_id u1) - (FStar_Unionfind.uvar_id u2))
end
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
(

let n1 = (FStar_List.length us1)
in (

let n2 = (FStar_List.length us2)
in if (n1 <> n2) then begin
(n1 - n2)
end else begin
(

let copt = (let _135_68 = (FStar_List.zip us1 us2)
in (FStar_Util.find_map _135_68 (fun _39_167 -> (match (_39_167) with
| (u1, u2) -> begin
(

let c = (compare_univs u1 u2)
in if (c <> (Prims.parse_int "0")) then begin
Some (c)
end else begin
None
end)
end))))
in (match (copt) with
| None -> begin
(Prims.parse_int "0")
end
| Some (c) -> begin
c
end))
end))
end
| (FStar_Syntax_Syntax.U_max (_39_174), _39_177) -> begin
(~- ((Prims.parse_int "1")))
end
| (_39_180, FStar_Syntax_Syntax.U_max (_39_182)) -> begin
(Prims.parse_int "1")
end
| _39_186 -> begin
(

let _39_189 = (univ_kernel u1)
in (match (_39_189) with
| (k1, n1) -> begin
(

let _39_192 = (univ_kernel u2)
in (match (_39_192) with
| (k2, n2) -> begin
(

let r = (compare_univs k1 k2)
in if (r = (Prims.parse_int "0")) then begin
(n1 - n2)
end else begin
r
end)
end))
end))
end))


let eq_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  Prims.bool = (fun u1 u2 -> ((compare_univs u1 u2) = (Prims.parse_int "0")))


let ml_comp : FStar_Syntax_Syntax.typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.comp = (fun t r -> (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = (FStar_Syntax_Syntax.U_unknown)::[]; FStar_Syntax_Syntax.effect_name = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (FStar_Syntax_Syntax.MLEFFECT)::[]}))


let comp_set_flags : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.comp = (fun c f -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (_)) | (FStar_Syntax_Syntax.GTotal (_)) -> begin
c
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let _39_208 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp ((

let _39_210 = ct
in {FStar_Syntax_Syntax.comp_univs = _39_210.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _39_210.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _39_210.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _39_210.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = f})); FStar_Syntax_Syntax.tk = _39_208.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _39_208.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _39_208.FStar_Syntax_Syntax.vars})
end))


let comp_flags = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_214) -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| FStar_Syntax_Syntax.GTotal (_39_217) -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.flags
end))


let comp_effect_name = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c.FStar_Syntax_Syntax.effect_name
end
| FStar_Syntax_Syntax.Total (_39_225) -> begin
FStar_Syntax_Const.effect_Tot_lid
end
| FStar_Syntax_Syntax.GTotal (_39_228) -> begin
FStar_Syntax_Const.effect_GTot_lid
end))


let comp_to_comp_typ : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
c
end
| (FStar_Syntax_Syntax.Total (t, Some (u))) | (FStar_Syntax_Syntax.GTotal (t, Some (u))) -> begin
{FStar_Syntax_Syntax.comp_univs = (u)::[]; FStar_Syntax_Syntax.effect_name = (comp_effect_name c); FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = []; FStar_Syntax_Syntax.flags = (comp_flags c)}
end
| _39_242 -> begin
(FStar_All.failwith "Assertion failed: Computation type without universe")
end))


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _39_1 -> (match (_39_1) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_248 -> begin
false
end)))))


let is_total_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_2 -> (match (_39_2) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_254 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_3 -> (match (_39_3) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_260 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _39_4 -> (match (_39_4) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _39_266 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_5 -> (match (_39_5) with
| (FStar_Syntax_Syntax.RETURN) | (FStar_Syntax_Syntax.PARTIAL_RETURN) -> begin
true
end
| _39_272 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)))


let is_pure_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_277) -> begin
true
end
| FStar_Syntax_Syntax.GTotal (_39_280) -> begin
false
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(((is_total_comp c) || (is_pure_effect ct.FStar_Syntax_Syntax.effect_name)) || (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_6 -> (match (_39_6) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _39_287 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> (((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name)) || (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_Util.for_some (fun _39_7 -> (match (_39_7) with
| FStar_Syntax_Syntax.LEMMA -> begin
true
end
| _39_294 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)))


let is_pure_or_ghost_function : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _135_113 = (FStar_Syntax_Subst.compress t)
in _135_113.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_298, c) -> begin
(is_pure_or_ghost_comp c)
end
| _39_303 -> begin
true
end))


let is_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _135_116 = (FStar_Syntax_Subst.compress t)
in _135_116.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_306, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid)
end
| _39_313 -> begin
false
end)
end
| _39_315 -> begin
false
end))


let head_and_args : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.args) = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
((head), (args))
end
| _39_323 -> begin
((t), ([]))
end)))


let un_uinst : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (t, _39_328) -> begin
(FStar_Syntax_Subst.compress t)
end
| _39_332 -> begin
t
end)))


let is_smt_lemma : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _135_123 = (FStar_Syntax_Subst.compress t)
in _135_123.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_335, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| (_req)::(_ens)::((pats, _39_345))::_39_342 -> begin
(

let pats' = (unmeta pats)
in (

let _39_356 = (head_and_args pats')
in (match (_39_356) with
| (head, _39_355) -> begin
(match ((let _135_124 = (un_uinst head)
in _135_124.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid)
end
| _39_360 -> begin
false
end)
end)))
end
| _39_362 -> begin
false
end)
end
| _39_364 -> begin
false
end)
end
| _39_366 -> begin
false
end))


let is_ml_comp = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _39_8 -> (match (_39_8) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| _39_373 -> begin
false
end)))))
end
| _39_375 -> begin
false
end))


let comp_result = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Total (t, _)) | (FStar_Syntax_Syntax.GTotal (t, _)) -> begin
t
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
ct.FStar_Syntax_Syntax.result_typ
end))


let set_result_typ = (fun c t -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_391) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Syntax_Syntax.GTotal (_39_394) -> begin
(FStar_Syntax_Syntax.mk_GTotal t)
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(FStar_Syntax_Syntax.mk_Comp (

let _39_398 = ct
in {FStar_Syntax_Syntax.comp_univs = _39_398.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _39_398.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = t; FStar_Syntax_Syntax.effect_args = _39_398.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _39_398.FStar_Syntax_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _39_9 -> (match (_39_9) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.RETURN) -> begin
true
end
| _39_405 -> begin
false
end)))))


let primops : FStar_Ident.lident Prims.list = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]


let is_primop_lid : FStar_Ident.lident  ->  Prims.bool = (fun l -> (FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals l))))


let is_primop = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(is_primop_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end
| _39_411 -> begin
false
end))


let rec unascribe : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (e, _39_416, _39_418) -> begin
(unascribe e)
end
| _39_422 -> begin
e
end)))


let rec ascribe = (fun t k -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (t', _39_427, _39_429) -> begin
(ascribe t' k)
end
| _39_433 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((t), (k), (None)))) None t.FStar_Syntax_Syntax.pos)
end))


let rec unrefine : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _39_438) -> begin
(unrefine x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _39_443, _39_445) -> begin
(unrefine t)
end
| _39_449 -> begin
t
end)))


let rec is_unit : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _135_143 = (unrefine t)
in _135_143.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_452) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _39_458) -> begin
(is_unit t)
end
| _39_462 -> begin
false
end))


let rec non_informative : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _135_146 = (unrefine t)
in _135_146.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_39_465) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid))
end
| FStar_Syntax_Syntax.Tm_app (head, _39_471) -> begin
(non_informative head)
end
| FStar_Syntax_Syntax.Tm_uinst (t, _39_476) -> begin
(non_informative t)
end
| FStar_Syntax_Syntax.Tm_arrow (_39_480, c) -> begin
((is_tot_or_gtot_comp c) && (non_informative (comp_result c)))
end
| _39_485 -> begin
false
end))


let is_fun : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (match ((let _135_149 = (FStar_Syntax_Subst.compress e)
in _135_149.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_39_488) -> begin
true
end
| _39_491 -> begin
false
end))


let is_function_typ : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _135_152 = (FStar_Syntax_Subst.compress t)
in _135_152.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_39_494) -> begin
true
end
| _39_497 -> begin
false
end))


let rec pre_typ : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, _39_502) -> begin
(pre_typ x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_ascribed (t, _39_507, _39_509) -> begin
(pre_typ t)
end
| _39_513 -> begin
t
end)))


let destruct : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.args Prims.option = (fun typ lid -> (

let typ = (FStar_Syntax_Subst.compress typ)
in (match ((let _135_159 = (un_uinst typ)
in _135_159.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some (args)
end
| _39_525 -> begin
None
end))
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc lid) -> begin
Some ([])
end
| _39_529 -> begin
None
end)))


let rec lids_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.list = (fun se -> (match (se) with
| (FStar_Syntax_Syntax.Sig_let (_, _, lids, _)) | (FStar_Syntax_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Syntax_Syntax.Sig_inductive_typ (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (lid, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_datacon (lid, _, _, _, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (lid, _, _, _, _)) | (FStar_Syntax_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| (FStar_Syntax_Syntax.Sig_new_effect_for_free (n, _)) | (FStar_Syntax_Syntax.Sig_new_effect (n, _)) -> begin
(n.FStar_Syntax_Syntax.mname)::[]
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) -> begin
[]
end))


let lid_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
Some (l)
end
| _39_633 -> begin
None
end))


let quals_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, quals, _, _)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, quals, _, _)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, quals, _)) | (FStar_Syntax_Syntax.Sig_assume (_, _, quals, _)) | (FStar_Syntax_Syntax.Sig_let (_, _, _, quals)) | (FStar_Syntax_Syntax.Sig_new_effect ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _}, _)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free ({FStar_Syntax_Syntax.qualifiers = quals; FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _; FStar_Syntax_Syntax.binders = _; FStar_Syntax_Syntax.signature = _; FStar_Syntax_Syntax.ret_wp = _; FStar_Syntax_Syntax.bind_wp = _; FStar_Syntax_Syntax.if_then_else = _; FStar_Syntax_Syntax.ite_wp = _; FStar_Syntax_Syntax.stronger = _; FStar_Syntax_Syntax.close_wp = _; FStar_Syntax_Syntax.assert_p = _; FStar_Syntax_Syntax.assume_p = _; FStar_Syntax_Syntax.null_wp = _; FStar_Syntax_Syntax.trivial = _; FStar_Syntax_Syntax.repr = _; FStar_Syntax_Syntax.return_repr = _; FStar_Syntax_Syntax.bind_repr = _; FStar_Syntax_Syntax.actions = _}, _)) -> begin
quals
end
| (FStar_Syntax_Syntax.Sig_sub_effect (_, _)) | (FStar_Syntax_Syntax.Sig_pragma (_, _)) | (FStar_Syntax_Syntax.Sig_main (_, _)) -> begin
[]
end))


let range_of_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Syntax_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_datacon (_, _, _, _, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_declare_typ (_, _, _, _, r)) | (FStar_Syntax_Syntax.Sig_assume (_, _, _, r)) | (FStar_Syntax_Syntax.Sig_let (_, r, _, _)) | (FStar_Syntax_Syntax.Sig_main (_, r)) | (FStar_Syntax_Syntax.Sig_pragma (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect (_, r)) | (FStar_Syntax_Syntax.Sig_new_effect_for_free (_, r)) | (FStar_Syntax_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))


let range_of_lb = (fun _39_10 -> (match (_39_10) with
| (FStar_Util.Inl (x), _39_918, _39_920) -> begin
(FStar_Syntax_Syntax.range_of_bv x)
end
| (FStar_Util.Inr (l), _39_925, _39_927) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun _39_932 -> (match (_39_932) with
| (hd, _39_931) -> begin
hd.FStar_Syntax_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))


let mk_app = (fun f args -> (

let r = (range_of_args args f.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((f), (args)))) None r)))


let mk_data = (fun l args -> (match (args) with
| [] -> begin
(let _135_180 = (let _135_179 = (let _135_178 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_135_178), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))
in FStar_Syntax_Syntax.Tm_meta (_135_179))
in (FStar_Syntax_Syntax.mk _135_180 None (FStar_Ident.range_of_lid l)))
end
| _39_944 -> begin
(

let e = (let _135_181 = (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (mk_app _135_181 args))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))) None e.FStar_Syntax_Syntax.pos))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _135_187 = (let _135_186 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((_135_186), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident _135_187))
end else begin
x
end)


let mk_field_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.int  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.bv) = (fun lid x i -> (

let nm = if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _135_197 = (let _135_196 = (let _135_194 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _135_194))
in (let _135_195 = (FStar_Syntax_Syntax.range_of_bv x)
in ((_135_196), (_135_195))))
in (FStar_Ident.mk_ident _135_197))
end else begin
x.FStar_Syntax_Syntax.ppname
end
in (

let y = (

let _39_952 = x
in {FStar_Syntax_Syntax.ppname = nm; FStar_Syntax_Syntax.index = _39_952.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _39_952.FStar_Syntax_Syntax.sort})
in (let _135_201 = (let _135_200 = (let _135_199 = (let _135_198 = (unmangle_field_name nm)
in (_135_198)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _135_199))
in (FStar_Ident.lid_of_ids _135_200))
in ((_135_201), (y))))))


let set_uvar = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (_39_958) -> begin
(let _135_206 = (let _135_205 = (let _135_204 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _135_204))
in (FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _135_205))
in (FStar_All.failwith _135_206))
end
| _39_961 -> begin
(FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed (t)))
end))


let qualifier_equal : FStar_Syntax_Syntax.qualifier  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun q1 q2 -> (match (((q1), (q2))) with
| (FStar_Syntax_Syntax.Discriminator (l1), FStar_Syntax_Syntax.Discriminator (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (FStar_Syntax_Syntax.Projector (l1a, l1b), FStar_Syntax_Syntax.Projector (l2a, l2b)) -> begin
((FStar_Ident.lid_equals l1a l2a) && (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText))
end
| ((FStar_Syntax_Syntax.RecordType (f1), FStar_Syntax_Syntax.RecordType (f2))) | ((FStar_Syntax_Syntax.RecordConstructor (f1), FStar_Syntax_Syntax.RecordConstructor (f2))) -> begin
(((FStar_List.length f1) = (FStar_List.length f2)) && (FStar_List.forall2 FStar_Ident.lid_equals f1 f2))
end
| _39_987 -> begin
(q1 = q2)
end))


let abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  FStar_Syntax_Syntax.term = (fun bs t lopt -> if ((FStar_List.length bs) = (Prims.parse_int "0")) then begin
t
end else begin
(

let close_lopt = (fun lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _135_220 = (let _135_219 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (_135_219))
in Some (_135_220))
end))
in (match (bs) with
| [] -> begin
t
end
| _39_1003 -> begin
(

let body = (let _135_221 = (FStar_Syntax_Subst.close bs t)
in (FStar_Syntax_Subst.compress _135_221))
in (match (((body.FStar_Syntax_Syntax.n), (lopt))) with
| (FStar_Syntax_Syntax.Tm_abs (bs', t, lopt'), None) -> begin
(let _135_226 = (let _135_225 = (let _135_224 = (let _135_222 = (FStar_Syntax_Subst.close_binders bs)
in (FStar_List.append _135_222 bs'))
in (let _135_223 = (close_lopt lopt')
in ((_135_224), (t), (_135_223))))
in FStar_Syntax_Syntax.Tm_abs (_135_225))
in (FStar_Syntax_Syntax.mk _135_226 None t.FStar_Syntax_Syntax.pos))
end
| _39_1013 -> begin
(

let lopt = (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (lc)) -> begin
(let _135_228 = (let _135_227 = (FStar_Syntax_Subst.close_lcomp bs lc)
in FStar_Util.Inl (_135_227))
in Some (_135_228))
end)
in (let _135_231 = (let _135_230 = (let _135_229 = (FStar_Syntax_Subst.close_binders bs)
in ((_135_229), (body), (lopt)))
in FStar_Syntax_Syntax.Tm_abs (_135_230))
in (FStar_Syntax_Syntax.mk _135_231 None t.FStar_Syntax_Syntax.pos)))
end))
end))
end)


let arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.typ = (fun bs c -> (match (bs) with
| [] -> begin
(comp_result c)
end
| _39_1027 -> begin
(let _135_239 = (let _135_238 = (let _135_237 = (FStar_Syntax_Subst.close_binders bs)
in (let _135_236 = (FStar_Syntax_Subst.close_comp bs c)
in ((_135_237), (_135_236))))
in FStar_Syntax_Syntax.Tm_arrow (_135_238))
in (FStar_Syntax_Syntax.mk _135_239 None c.FStar_Syntax_Syntax.pos))
end))


let flat_arrow : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun bs c -> (

let t = (arrow bs c)
in (match ((let _135_244 = (FStar_Syntax_Subst.compress t)
in _135_244.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (tres, _39_1037) -> begin
(match ((let _135_245 = (FStar_Syntax_Subst.compress tres)
in _135_245.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs', c') -> begin
(let _135_246 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((((FStar_List.append bs bs')), (c')))) _135_246 t.FStar_Syntax_Syntax.pos))
end
| _39_1045 -> begin
t
end)
end
| _39_1047 -> begin
t
end)
end
| _39_1049 -> begin
t
end)))


let refine : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun b t -> (let _135_258 = (let _135_254 = (let _135_253 = (let _135_252 = (let _135_251 = (FStar_Syntax_Syntax.mk_binder b)
in (_135_251)::[])
in (FStar_Syntax_Subst.close _135_252 t))
in ((b), (_135_253)))
in FStar_Syntax_Syntax.Tm_refine (_135_254))
in (let _135_257 = (FStar_ST.read b.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.tk)
in (let _135_256 = (let _135_255 = (FStar_Syntax_Syntax.range_of_bv b)
in (FStar_Range.union_ranges _135_255 t.FStar_Syntax_Syntax.pos))
in (FStar_Syntax_Syntax.mk _135_258 _135_257 _135_256)))))


let branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun b -> (FStar_Syntax_Subst.close_branch b))


let rec arrow_formals_comp : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _39_1061 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_39_1061) with
| (bs, c) -> begin
if (is_tot_or_gtot_comp c) then begin
(

let _39_1064 = (arrow_formals_comp (comp_result c))
in (match (_39_1064) with
| (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end))
end else begin
((bs), (c))
end
end))
end
| _39_1066 -> begin
(let _135_263 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_135_263)))
end)))


let rec arrow_formals : FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.typ) = (fun k -> (

let _39_1070 = (arrow_formals_comp k)
in (match (_39_1070) with
| (bs, c) -> begin
((bs), ((comp_result c)))
end)))


let abs_formals : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option) = (fun t -> (

let rec aux = (fun t what -> (match ((let _135_273 = (let _135_272 = (FStar_Syntax_Subst.compress t)
in (FStar_All.pipe_left unascribe _135_272))
in _135_273.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, t, what) -> begin
(

let _39_1083 = (aux t what)
in (match (_39_1083) with
| (bs', t, what) -> begin
(((FStar_List.append bs bs')), (t), (what))
end))
end
| _39_1085 -> begin
(([]), (t), (what))
end))
in (

let _39_1089 = (aux t None)
in (match (_39_1089) with
| (bs, t, what) -> begin
(

let _39_1092 = (FStar_Syntax_Subst.open_term bs t)
in (match (_39_1092) with
| (bs, t) -> begin
((bs), (t), (what))
end))
end))))


let mk_letbinding : FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun lbname univ_vars typ eff def -> {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = eff; FStar_Syntax_Syntax.lbdef = def})


let close_univs_and_mk_letbinding : FStar_Syntax_Syntax.fv Prims.list Prims.option  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.letbinding = (fun recs lbname univ_vars typ eff def -> (

let def = (match (((recs), (univ_vars))) with
| ((None, _)) | ((_, [])) -> begin
def
end
| (Some (fvs), _39_1115) -> begin
(

let universes = (FStar_All.pipe_right univ_vars (FStar_List.map (fun _135_296 -> FStar_Syntax_Syntax.U_name (_135_296))))
in (

let inst = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (universes)))))
in (FStar_Syntax_InstFV.instantiate inst def)))
end)
in (

let typ = (FStar_Syntax_Subst.close_univ_vars univ_vars typ)
in (

let def = (FStar_Syntax_Subst.close_univ_vars univ_vars def)
in (mk_letbinding lbname univ_vars typ eff def)))))


let open_univ_vars_binders_and_comp : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * FStar_Syntax_Syntax.comp) = (fun uvs binders c -> (match (binders) with
| [] -> begin
(

let _39_1129 = (FStar_Syntax_Subst.open_univ_vars_comp uvs c)
in (match (_39_1129) with
| (uvs, c) -> begin
((uvs), ([]), (c))
end))
end
| _39_1131 -> begin
(

let t' = (arrow binders c)
in (

let _39_1135 = (FStar_Syntax_Subst.open_univ_vars uvs t')
in (match (_39_1135) with
| (uvs, t') -> begin
(match ((let _135_304 = (FStar_Syntax_Subst.compress t')
in _135_304.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
((uvs), (binders), (c))
end
| _39_1141 -> begin
(FStar_All.failwith "Impossible")
end)
end)))
end))


let is_tuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.tuple")
end
| _39_1146 -> begin
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _135_311 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "tuple%s" _135_311))
in (let _135_312 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _135_312 r))))


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _135_317 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mktuple%s" _135_317))
in (let _135_318 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _135_318 r))))


let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _135_323 = (mk_tuple_data_lid n FStar_Range.dummyRange)
in (FStar_Ident.lid_equals f _135_323)))


let is_dtuple_constructor : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Util.starts_with fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str "Prims.dtuple")
end
| _39_1159 -> begin
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _135_330 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "dtuple%s" _135_330))
in (let _135_331 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _135_331 r))))


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _135_336 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Mkdtuple%s" _135_336))
in (let _135_337 = (FStar_Syntax_Const.pconst t)
in (FStar_Ident.set_lid_range _135_337 r))))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> (FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Syntax_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Syntax_Const.and_lid)::(FStar_Syntax_Const.or_lid)::(FStar_Syntax_Const.not_lid)::(FStar_Syntax_Const.iff_lid)::(FStar_Syntax_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _135_353 = (pre_typ t)
in _135_353.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v lid)
end
| _39_1178 -> begin
false
end))


let rec is_constructed_typ : FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _135_358 = (pre_typ t)
in _135_358.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (_39_1182) -> begin
(is_constructor t lid)
end
| FStar_Syntax_Syntax.Tm_app (t, _39_1186) -> begin
(is_constructed_typ t lid)
end
| _39_1190 -> begin
false
end))


let rec get_tycon : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun t -> (

let t = (pre_typ t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_app (t, _39_1204) -> begin
(get_tycon t)
end
| _39_1208 -> begin
None
end)))


let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _39_1214 _39_1218 -> (match (((_39_1214), (_39_1218))) with
| ((fn1, _39_1213), (fn2, _39_1217)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Syntax_Const.op_Eq)::(FStar_Syntax_Const.op_notEq)::(FStar_Syntax_Const.op_LT)::(FStar_Syntax_Const.op_LTE)::(FStar_Syntax_Const.op_GT)::(FStar_Syntax_Const.op_GTE)::(FStar_Syntax_Const.op_Subtraction)::(FStar_Syntax_Const.op_Minus)::(FStar_Syntax_Const.op_Addition)::(FStar_Syntax_Const.op_Multiply)::(FStar_Syntax_Const.op_Division)::(FStar_Syntax_Const.op_Modulus)::(FStar_Syntax_Const.op_And)::(FStar_Syntax_Const.op_Or)::(FStar_Syntax_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


let ktype : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None FStar_Range.dummyRange)


let ktype0 : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)) None FStar_Range.dummyRange)


let type_u : Prims.unit  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe) = (fun _39_1221 -> (match (()) with
| () -> begin
(

let u = (let _135_369 = (FStar_Unionfind.fresh None)
in (FStar_All.pipe_left (fun _135_368 -> FStar_Syntax_Syntax.U_unif (_135_368)) _135_369))
in (let _135_370 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None FStar_Range.dummyRange)
in ((_135_370), (u))))
end))


let kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kunary ktype0 ktype0)


let kt_kt_kt : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (FStar_Syntax_Const.kbin ktype0 ktype0 ktype0)


let fvar_const : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None))


let tand : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.and_lid)


let tor : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.or_lid)


let timp : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.imp_lid)


let tiff : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.iff_lid)


let t_bool : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.bool_lid)


let t_false : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.false_lid)


let t_true : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.true_lid)


let b2t_v : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.b2t_lid)


let t_not : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.not_lid)


let mk_conj_opt : FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _135_384 = (let _135_383 = (let _135_381 = (let _135_380 = (let _135_379 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _135_378 = (let _135_377 = (FStar_Syntax_Syntax.as_arg phi2)
in (_135_377)::[])
in (_135_379)::_135_378))
in ((tand), (_135_380)))
in FStar_Syntax_Syntax.Tm_app (_135_381))
in (let _135_382 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _135_383 None _135_382)))
in Some (_135_384))
end))


let mk_binop = (fun op_t phi1 phi2 -> (let _135_394 = (let _135_392 = (let _135_391 = (let _135_390 = (FStar_Syntax_Syntax.as_arg phi1)
in (let _135_389 = (let _135_388 = (FStar_Syntax_Syntax.as_arg phi2)
in (_135_388)::[])
in (_135_390)::_135_389))
in ((op_t), (_135_391)))
in FStar_Syntax_Syntax.Tm_app (_135_392))
in (let _135_393 = (FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos phi2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _135_394 None _135_393))))


let mk_neg = (fun phi -> (let _135_399 = (let _135_398 = (let _135_397 = (let _135_396 = (FStar_Syntax_Syntax.as_arg phi)
in (_135_396)::[])
in ((t_not), (_135_397)))
in FStar_Syntax_Syntax.Tm_app (_135_398))
in (FStar_Syntax_Syntax.mk _135_399 None phi.FStar_Syntax_Syntax.pos)))


let mk_conj = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
(FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
end
| (hd)::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))


let mk_disj = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Syntax_Syntax.term Prims.list  ->  FStar_Syntax_Syntax.term = (fun phi -> (match (phi) with
| [] -> begin
t_false
end
| (hd)::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))


let mk_imp : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun phi1 phi2 -> (match ((let _135_412 = (FStar_Syntax_Subst.compress phi1)
in _135_412.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid) -> begin
t_true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
phi2
end
| _39_1254 -> begin
(match ((let _135_413 = (FStar_Syntax_Subst.compress phi2)
in _135_413.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when ((FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) || (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid)) -> begin
phi2
end
| _39_1258 -> begin
(mk_binop timp phi1 phi2)
end)
end))


let mk_iff = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t = (fun e -> (let _135_420 = (let _135_419 = (let _135_418 = (let _135_417 = (FStar_Syntax_Syntax.as_arg e)
in (_135_417)::[])
in ((b2t_v), (_135_418)))
in FStar_Syntax_Syntax.Tm_app (_135_419))
in (FStar_Syntax_Syntax.mk _135_420 None e.FStar_Syntax_Syntax.pos)))


let teq : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.eq2_lid)


let mk_eq = (fun t1 t2 e1 e2 -> (let _135_431 = (let _135_429 = (let _135_428 = (let _135_427 = (FStar_Syntax_Syntax.as_arg e1)
in (let _135_426 = (let _135_425 = (FStar_Syntax_Syntax.as_arg e2)
in (_135_425)::[])
in (_135_427)::_135_426))
in ((teq), (_135_428)))
in FStar_Syntax_Syntax.Tm_app (_135_429))
in (let _135_430 = (FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos e2.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk _135_431 None _135_430))))


let mk_has_type = (fun t x t' -> (

let t_has_type = (fvar_const FStar_Syntax_Const.has_type_lid)
in (

let t_has_type = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((t_has_type), ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))) None FStar_Range.dummyRange)
in (let _135_442 = (let _135_441 = (let _135_440 = (let _135_439 = (FStar_Syntax_Syntax.iarg t)
in (let _135_438 = (let _135_437 = (FStar_Syntax_Syntax.as_arg x)
in (let _135_436 = (let _135_435 = (FStar_Syntax_Syntax.as_arg t')
in (_135_435)::[])
in (_135_437)::_135_436))
in (_135_439)::_135_438))
in ((t_has_type), (_135_440)))
in FStar_Syntax_Syntax.Tm_app (_135_441))
in (FStar_Syntax_Syntax.mk _135_442 None FStar_Range.dummyRange)))))


let lex_t : FStar_Syntax_Syntax.term = (fvar_const FStar_Syntax_Const.lex_t_lid)


let lex_top : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let lex_pair : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))


let tforall : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)


let t_haseq : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.haseq_lid FStar_Syntax_Syntax.Delta_constant None)


let lcomp_of_comp : (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lcomp = (fun c0 -> (

let _39_1282 = (match (c0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_39_1273) -> begin
((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[]))
end
| FStar_Syntax_Syntax.GTotal (_39_1276) -> begin
((FStar_Syntax_Const.effect_GTot_lid), ((FStar_Syntax_Syntax.SOMETRIVIAL)::[]))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
((c.FStar_Syntax_Syntax.effect_name), (c.FStar_Syntax_Syntax.flags))
end)
in (match (_39_1282) with
| (eff_name, flags) -> begin
{FStar_Syntax_Syntax.eff_name = eff_name; FStar_Syntax_Syntax.res_typ = (comp_result c0); FStar_Syntax_Syntax.cflags = flags; FStar_Syntax_Syntax.comp = (fun _39_1283 -> (match (()) with
| () -> begin
c0
end))}
end)))


let mk_forall : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x body -> (let _135_462 = (let _135_461 = (let _135_460 = (let _135_459 = (FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort)
in (let _135_458 = (let _135_457 = (let _135_456 = (let _135_455 = (let _135_450 = (FStar_Syntax_Syntax.mk_binder x)
in (_135_450)::[])
in (let _135_454 = (let _135_453 = (let _135_452 = (let _135_451 = (FStar_Syntax_Syntax.mk_Total ktype0)
in (FStar_All.pipe_left lcomp_of_comp _135_451))
in FStar_Util.Inl (_135_452))
in Some (_135_453))
in (abs _135_455 body _135_454)))
in (FStar_Syntax_Syntax.as_arg _135_456))
in (_135_457)::[])
in (_135_459)::_135_458))
in ((tforall), (_135_460)))
in FStar_Syntax_Syntax.Tm_app (_135_461))
in (FStar_Syntax_Syntax.mk _135_462 None FStar_Range.dummyRange)))


let rec close_forall : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
f
end else begin
(mk_forall (Prims.fst b) f)
end) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (_39_1292) -> begin
true
end
| _39_1295 -> begin
false
end))


let if_then_else = (fun b t1 t2 -> (

let then_branch = (let _135_473 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t1.FStar_Syntax_Syntax.pos)
in ((_135_473), (None), (t1)))
in (

let else_branch = (let _135_474 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (false))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Syntax_Syntax.pos)
in ((_135_474), (None), (t2)))
in (let _135_476 = (let _135_475 = (FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos t2.FStar_Syntax_Syntax.pos)
in (FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _135_475))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((b), ((then_branch)::(else_branch)::[])))) None _135_476)))))


type qpats =
FStar_Syntax_Syntax.args Prims.list


type connective =
| QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args)


let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))


let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))


let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))


let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_39_1303) -> begin
_39_1303
end))


let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_39_1306) -> begin
_39_1306
end))


let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_39_1309) -> begin
_39_1309
end))


let destruct_typ_as_formula : FStar_Syntax_Syntax.term  ->  connective Prims.option = (fun f -> (

let rec unmeta_monadic = (fun f -> (

let f = (FStar_Syntax_Subst.compress f)
in (match (f.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (_))) | (FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (_))) -> begin
(unmeta_monadic t)
end
| _39_1326 -> begin
f
end)))
in (

let destruct_base_conn = (fun f -> (

let connectives = (((FStar_Syntax_Const.true_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.false_lid), ((Prims.parse_int "0"))))::(((FStar_Syntax_Const.and_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.or_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.imp_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.iff_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.ite_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.not_lid), ((Prims.parse_int "1"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "3"))))::(((FStar_Syntax_Const.eq2_lid), ((Prims.parse_int "2"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "4"))))::(((FStar_Syntax_Const.eq3_lid), ((Prims.parse_int "2"))))::[]
in (

let rec aux = (fun f _39_1334 -> (match (_39_1334) with
| (lid, arity) -> begin
(

let _39_1337 = (let _135_529 = (unmeta_monadic f)
in (head_and_args _135_529))
in (match (_39_1337) with
| (t, args) -> begin
(

let t = (un_uinst t)
in if ((is_constructor t lid) && ((FStar_List.length args) = arity)) then begin
Some (BaseConn (((lid), (args))))
end else begin
None
end)
end))
end))
in (FStar_Util.find_map connectives (aux f)))))
in (

let patterns = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(let _135_532 = (FStar_Syntax_Subst.compress t)
in ((pats), (_135_532)))
end
| _39_1348 -> begin
(let _135_533 = (FStar_Syntax_Subst.compress t)
in (([]), (_135_533)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa fv -> if fa then begin
(is_forall fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end else begin
(is_exists fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end)
in (

let flat = (fun t -> (

let _39_1358 = (head_and_args t)
in (match (_39_1358) with
| (t, args) -> begin
(let _135_545 = (un_uinst t)
in (let _135_544 = (FStar_All.pipe_right args (FStar_List.map (fun _39_1361 -> (match (_39_1361) with
| (t, imp) -> begin
(let _135_543 = (unascribe t)
in ((_135_543), (imp)))
end))))
in ((_135_545), (_135_544))))
end)))
in (

let rec aux = (fun qopt out t -> (match ((let _135_552 = (flat t)
in ((qopt), (_135_552)))) with
| ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((Some (fa), ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_q fa tc) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) | ((None, ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (tc); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (_)::(({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs ((b)::[], t2, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))::[]))) when (is_qlid tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))) ((b)::out) t2)
end
| (Some (b), _39_1488) -> begin
(

let bs = (FStar_List.rev out)
in (

let _39_1493 = (FStar_Syntax_Subst.open_term bs t)
in (match (_39_1493) with
| (bs, t) -> begin
(

let _39_1496 = (patterns t)
in (match (_39_1496) with
| (pats, body) -> begin
if b then begin
Some (QAll (((bs), (pats), (body))))
end else begin
Some (QEx (((bs), (pats), (body))))
end
end))
end)))
end
| _39_1498 -> begin
None
end))
in (aux None [] t)))))
in (

let phi = (unmeta_monadic f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end)))))))


let action_as_lb : FStar_Syntax_Syntax.action  ->  FStar_Syntax_Syntax.sigelt = (fun a -> (

let lb = (let _135_556 = (let _135_555 = (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name FStar_Syntax_Syntax.Delta_equational None)
in FStar_Util.Inr (_135_555))
in (close_univs_and_mk_letbinding None _135_556 a.FStar_Syntax_Syntax.action_univs a.FStar_Syntax_Syntax.action_typ FStar_Syntax_Const.effect_Tot_lid a.FStar_Syntax_Syntax.action_defn))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos), ((a.FStar_Syntax_Syntax.action_name)::[]), ([])))))


let mk_reify = (fun t -> (

let reify_ = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) None t.FStar_Syntax_Syntax.pos)
in (let _135_561 = (let _135_560 = (let _135_559 = (let _135_558 = (FStar_Syntax_Syntax.as_arg t)
in (_135_558)::[])
in ((reify_), (_135_559)))
in FStar_Syntax_Syntax.Tm_app (_135_560))
in (FStar_Syntax_Syntax.mk _135_561 None t.FStar_Syntax_Syntax.pos))))


let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_39_1510) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) | (FStar_Syntax_Syntax.Tm_app (t, _)) | (FStar_Syntax_Syntax.Tm_abs (_, t, _)) | (FStar_Syntax_Syntax.Tm_let (_, t)) -> begin
(delta_qualifier t)
end)))


let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (

let d = (delta_qualifier t)
in (

let rec aux = (fun d -> (match (d) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
FStar_Syntax_Syntax.Delta_defined_at_level ((i + (Prims.parse_int "1")))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(aux d)
end))
in (aux d))))


let is_unknown : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _135_573 = (FStar_Syntax_Subst.compress t)
in _135_573.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
true
end
| _39_1587 -> begin
false
end))


let rec list_elements : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term Prims.list Prims.option = (fun e -> (

let _39_1591 = (let _135_576 = (unmeta e)
in (head_and_args _135_576))
in (match (_39_1591) with
| (head, args) -> begin
(match ((let _135_578 = (let _135_577 = (un_uinst head)
in _135_577.FStar_Syntax_Syntax.n)
in ((_135_578), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _39_1595) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_39_1608)::((hd, _39_1605))::((tl, _39_1601))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _135_581 = (let _135_580 = (let _135_579 = (list_elements tl)
in (FStar_Util.must _135_579))
in (hd)::_135_580)
in Some (_135_581))
end
| _39_1612 -> begin
None
end)
end)))




