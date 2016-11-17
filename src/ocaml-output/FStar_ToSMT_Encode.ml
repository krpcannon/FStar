
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _51_40 -> (match (_51_40) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _51_1 -> (match (_51_1) with
| (FStar_Util.Inl (_51_44), _51_47) -> begin
false
end
| _51_50 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText a.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)


let mk_typ_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.string = (fun lid a -> (let _147_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _147_14)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.string = (fun lid a -> (

let a = (let _147_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _147_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _147_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _147_20))))


let primitive_projector_by_pos : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _51_62 -> (match (()) with
| () -> begin
(let _147_30 = (let _147_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _147_29 lid.FStar_Ident.str))
in (FStar_All.failwith _147_30))
end))
in (

let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _147_31 = (FStar_Absyn_Util.compress_typ t)
in _147_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _51_66) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(mk_typ_projector_name lid a.FStar_Absyn_Syntax.v)
end
| FStar_Util.Inr (x) -> begin
(mk_term_projector_name lid x.FStar_Absyn_Syntax.v)
end))
end
end
| _51_75 -> begin
(fail ())
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _147_37 = (let _147_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _147_36))
in (FStar_All.pipe_left escape _147_37)))


let mk_typ_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _147_43 = (let _147_42 = (mk_typ_projector_name lid a)
in ((_147_42), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Type_sort))))))
in (FStar_ToSMT_Term.mkFreeV _147_43)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _147_49 = (let _147_48 = (mk_term_projector_name lid a)
in ((_147_48), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Term_sort))))))
in (FStar_ToSMT_Term.mkFreeV _147_49)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_ToSMT_Term.term = (fun lid i -> (let _147_55 = (let _147_54 = (mk_term_projector_name_by_pos lid i)
in ((_147_54), (FStar_ToSMT_Term.Arrow (((FStar_ToSMT_Term.Term_sort), (FStar_ToSMT_Term.Term_sort))))))
in (FStar_ToSMT_Term.mkFreeV _147_55)))


let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  FStar_Ident.ident  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "10")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _51_101 -> (match (()) with
| () -> begin
(let _147_159 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _147_158 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_147_159), (_147_158))))
end))
in (

let scopes = (let _147_161 = (let _147_160 = (new_scope ())
in (_147_160)::[])
in (FStar_Util.mk_ref _147_161))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _147_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _147_165 (fun _51_109 -> (match (_51_109) with
| (names, _51_108) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_51_112) -> begin
(

let _51_114 = (FStar_Util.incr ctr)
in (let _147_168 = (let _147_167 = (let _147_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _147_166))
in (Prims.strcat "__" _147_167))
in (Prims.strcat y _147_168)))
end)
in (

let top_scope = (let _147_170 = (let _147_169 = (FStar_ST.read scopes)
in (FStar_List.hd _147_169))
in (FStar_All.pipe_left Prims.fst _147_170))
in (

let _51_118 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" rn.FStar_Ident.idText))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _51_126 -> (match (()) with
| () -> begin
(

let _51_127 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _147_182 = (let _147_181 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _147_181))
in (FStar_Util.format2 "%s_%s" pfx _147_182)))
in (

let string_const = (fun s -> (match ((let _147_186 = (FStar_ST.read scopes)
in (FStar_Util.find_map _147_186 (fun _51_136 -> (match (_51_136) with
| (_51_134, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _147_187 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _147_187))
in (

let top_scope = (let _147_189 = (let _147_188 = (FStar_ST.read scopes)
in (FStar_List.hd _147_188))
in (FStar_All.pipe_left Prims.snd _147_189))
in (

let _51_143 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _51_146 -> (match (()) with
| () -> begin
(let _147_194 = (let _147_193 = (new_scope ())
in (let _147_192 = (FStar_ST.read scopes)
in (_147_193)::_147_192))
in (FStar_ST.op_Colon_Equals scopes _147_194))
end))
in (

let pop = (fun _51_148 -> (match (()) with
| () -> begin
(let _147_198 = (let _147_197 = (FStar_ST.read scopes)
in (FStar_List.tl _147_197))
in (FStar_ST.op_Colon_Equals scopes _147_198))
end))
in (

let mark = (fun _51_150 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _51_152 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _51_154 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _51_167 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _51_172 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _51_175 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle = (fun x -> (let _147_214 = (let _147_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _147_212 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in ((_147_213), (_147_212))))
in (FStar_Absyn_Util.mkbvd _147_214)))


type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term)
| Binding_tvar of (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option)


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_tvar = (fun _discr_ -> (match (_discr_) with
| Binding_tvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))


let is_Binding_ftvar = (fun _discr_ -> (match (_discr_) with
| Binding_ftvar (_) -> begin
true
end
| _ -> begin
false
end))


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_51_180) -> begin
_51_180
end))


let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_51_183) -> begin
_51_183
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_51_186) -> begin
_51_186
end))


let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_51_189) -> begin
_51_189
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _147_300 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _51_2 -> (match (_51_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _51_214) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _147_300 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string Prims.option = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_310 = (FStar_Absyn_Print.typ_to_string t)
in Some (_147_310))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_ToSMT_Term.sort  ->  (Prims.string * FStar_ToSMT_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _147_315 = (FStar_ToSMT_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_147_315)))))


let gen_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _147_320 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _147_320))
in (

let y = (FStar_ToSMT_Term.mkFreeV ((ysym), (FStar_ToSMT_Term.Term_sort)))
in ((ysym), (y), ((

let _51_233 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _51_233.tcenv; warn = _51_233.warn; cache = _51_233.cache; nolabels = _51_233.nolabels; use_zfuel_name = _51_233.use_zfuel_name; encode_non_total_function_typ = _51_233.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _51_239 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _51_239.depth; tcenv = _51_239.tcenv; warn = _51_239.warn; cache = _51_239.cache; nolabels = _51_239.nolabels; use_zfuel_name = _51_239.use_zfuel_name; encode_non_total_function_typ = _51_239.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _51_244 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _51_244.depth; tcenv = _51_244.tcenv; warn = _51_244.warn; cache = _51_244.cache; nolabels = _51_244.nolabels; use_zfuel_name = _51_244.use_zfuel_name; encode_non_total_function_typ = _51_244.encode_non_total_function_typ}))


let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _51_3 -> (match (_51_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (((b), (t)))
end
| _51_254 -> begin
None
end)))) with
| None -> begin
(let _147_335 = (let _147_334 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _147_334))
in (FStar_All.failwith _147_335))
end
| Some (b, t) -> begin
t
end))


let gen_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _147_340 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _147_340))
in (

let y = (FStar_ToSMT_Term.mkFreeV ((ysym), (FStar_ToSMT_Term.Type_sort)))
in ((ysym), (y), ((

let _51_264 = env
in {bindings = (Binding_tvar (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _51_264.tcenv; warn = _51_264.warn; cache = _51_264.cache; nolabels = _51_264.nolabels; use_zfuel_name = _51_264.use_zfuel_name; encode_non_total_function_typ = _51_264.encode_non_total_function_typ}))))))


let new_typ_constant : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _51_270 = env
in {bindings = (Binding_tvar (((x), (y))))::env.bindings; depth = _51_270.depth; tcenv = _51_270.tcenv; warn = _51_270.warn; cache = _51_270.cache; nolabels = _51_270.nolabels; use_zfuel_name = _51_270.use_zfuel_name; encode_non_total_function_typ = _51_270.encode_non_total_function_typ}))))))


let push_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _51_275 = env
in {bindings = (Binding_tvar (((x), (t))))::env.bindings; depth = _51_275.depth; tcenv = _51_275.tcenv; warn = _51_275.warn; cache = _51_275.cache; nolabels = _51_275.nolabels; use_zfuel_name = _51_275.use_zfuel_name; encode_non_total_function_typ = _51_275.encode_non_total_function_typ}))


let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _51_4 -> (match (_51_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (((b), (t)))
end
| _51_285 -> begin
None
end)))) with
| None -> begin
(let _147_355 = (let _147_354 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _147_354))
in (FStar_All.failwith _147_355))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _147_366 = (

let _51_295 = env
in (let _147_365 = (let _147_364 = (let _147_363 = (let _147_362 = (let _147_361 = (FStar_ToSMT_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _147_360 -> Some (_147_360)) _147_361))
in ((x), (fname), (_147_362), (None)))
in Binding_fvar (_147_363))
in (_147_364)::env.bindings)
in {bindings = _147_365; depth = _51_295.depth; tcenv = _51_295.tcenv; warn = _51_295.warn; cache = _51_295.cache; nolabels = _51_295.nolabels; use_zfuel_name = _51_295.use_zfuel_name; encode_non_total_function_typ = _51_295.encode_non_total_function_typ}))
in ((fname), (ftok), (_147_366))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _51_5 -> (match (_51_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _51_307 -> begin
None
end))))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _147_377 = (let _147_376 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _147_376))
in (FStar_All.failwith _147_377))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _51_317 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _51_317.depth; tcenv = _51_317.tcenv; warn = _51_317.warn; cache = _51_317.cache; nolabels = _51_317.nolabels; use_zfuel_name = _51_317.use_zfuel_name; encode_non_total_function_typ = _51_317.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _51_326 = (lookup_lid env x)
in (match (_51_326) with
| (t1, t2, _51_325) -> begin
(

let t3 = (let _147_394 = (let _147_393 = (let _147_392 = (FStar_ToSMT_Term.mkApp (("ZFuel"), ([])))
in (_147_392)::[])
in ((f), (_147_393)))
in (FStar_ToSMT_Term.mkApp _147_394))
in (

let _51_328 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _51_328.depth; tcenv = _51_328.tcenv; warn = _51_328.warn; cache = _51_328.cache; nolabels = _51_328.nolabels; use_zfuel_name = _51_328.use_zfuel_name; encode_non_total_function_typ = _51_328.encode_non_total_function_typ}))
end)))


let lookup_free_var = (fun env a -> (

let _51_335 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_51_335) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _51_339 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_51_343, (fuel)::[]) -> begin
if (let _147_398 = (let _147_397 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _147_397 Prims.fst))
in (FStar_Util.starts_with _147_398 "fuel")) then begin
(let _147_399 = (FStar_ToSMT_Term.mkFreeV ((name), (FStar_ToSMT_Term.Term_sort)))
in (FStar_ToSMT_Term.mk_ApplyEF _147_399 fuel))
end else begin
t
end
end
| _51_349 -> begin
t
end)
end
| _51_351 -> begin
(let _147_401 = (let _147_400 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _147_400))
in (FStar_All.failwith _147_401))
end)
end)
end)))


let lookup_free_var_name = (fun env a -> (

let _51_359 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_51_359) with
| (x, _51_356, _51_358) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _51_365 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_51_365) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _51_369; FStar_ToSMT_Term.freevars = _51_367}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _51_377 -> begin
(match (sym) with
| None -> begin
((FStar_ToSMT_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _51_387 -> begin
((FStar_ToSMT_Term.Var (name)), ([]))
end)
end)
end)
end)))


let new_typ_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _147_416 = (

let _51_392 = env
in (let _147_415 = (let _147_414 = (let _147_413 = (let _147_412 = (let _147_411 = (FStar_ToSMT_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _147_410 -> Some (_147_410)) _147_411))
in ((x), (fname), (_147_412)))
in Binding_ftvar (_147_413))
in (_147_414)::env.bindings)
in {bindings = _147_415; depth = _51_392.depth; tcenv = _51_392.tcenv; warn = _51_392.warn; cache = _51_392.cache; nolabels = _51_392.nolabels; use_zfuel_name = _51_392.use_zfuel_name; encode_non_total_function_typ = _51_392.encode_non_total_function_typ}))
in ((fname), (ftok), (_147_416))))))


let lookup_tlid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((lookup_binding env (fun _51_6 -> (match (_51_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2)))
end
| _51_403 -> begin
None
end)))) with
| None -> begin
(let _147_423 = (let _147_422 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _147_422))
in (FStar_All.failwith _147_423))
end
| Some (s) -> begin
s
end))


let push_free_tvar : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _51_411 = env
in {bindings = (Binding_ftvar (((x), (fname), (ftok))))::env.bindings; depth = _51_411.depth; tcenv = _51_411.tcenv; warn = _51_411.warn; cache = _51_411.cache; nolabels = _51_411.nolabels; use_zfuel_name = _51_411.use_zfuel_name; encode_non_total_function_typ = _51_411.encode_non_total_function_typ}))


let lookup_free_tvar = (fun env a -> (match ((let _147_434 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _147_434 Prims.snd))) with
| None -> begin
(let _147_436 = (let _147_435 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _147_435))
in (FStar_All.failwith _147_436))
end
| Some (t) -> begin
t
end))


let lookup_free_tvar_name = (fun env a -> (let _147_439 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _147_439 Prims.fst)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _51_7 -> (match (_51_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _51_436 -> begin
None
end))))


let mkForall_fuel' = (fun n _51_441 -> (match (_51_441) with
| (pats, vars, body) -> begin
(

let fallback = (fun _51_443 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _51_446 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_51_446) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _51_456 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _147_452 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _147_452))
end
| _51_469 -> begin
(let _147_453 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _147_453 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp ((guard), (body'))))
end
| _51_472 -> begin
body
end)
in (

let vars = (((fsym), (FStar_ToSMT_Term.Fuel_sort)))::vars
in (FStar_ToSMT_Term.mkForall ((pats), (vars), (body)))))))
end))
end)
end))


let mkForall_fuel : (FStar_ToSMT_Term.pat Prims.list Prims.list * FStar_ToSMT_Term.fvs * FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun env t -> (

let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _147_459 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _147_459 FStar_Option.isNone))
end
| _51_510 -> begin
false
end)))


let whnf : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end)


let whnf_e : env_t  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun env e -> (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))


let norm_t : env_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env.tcenv t))


let norm_k : env_t  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (FStar_Tc_Normalize.normalize_kind env.tcenv k))


let trivial_post : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t -> (let _147_481 = (let _147_480 = (let _147_478 = (FStar_Absyn_Syntax.null_v_binder t)
in (_147_478)::[])
in (let _147_479 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in ((_147_480), (_147_479))))
in (FStar_Absyn_Syntax.mk_Typ_lam _147_481 None t.FStar_Absyn_Syntax.pos)))


let mk_ApplyE : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _147_488 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _147_488))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _147_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _147_489))
end
| _51_527 -> begin
(let _147_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _147_490))
end)) e)))


let mk_ApplyE_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyET out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))


let mk_ApplyT : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun t vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _147_503 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _147_503))
end
| _51_542 -> begin
(let _147_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _147_504))
end)) t)))


let mk_ApplyT_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))


let is_app : FStar_ToSMT_Term.op  ->  Prims.bool = (fun _51_8 -> (match (_51_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _51_561 -> begin
false
end))


let is_eta : env_t  ->  FStar_ToSMT_Term.fv Prims.list  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_ToSMT_Term.tm), (xs))) with
| (FStar_ToSMT_Term.App (app, (f)::({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _51_572; FStar_ToSMT_Term.freevars = _51_570})::[]), (x)::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _51_590) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _51_597 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_51_599, []) -> begin
(

let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _51_605 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list


type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))


exception Let_rec_unencodeable


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


exception Bad_form


let is_Bad_form = (fun _discr_ -> (match (_discr_) with
| Bad_form (_) -> begin
true
end
| _ -> begin
false
end))


let constructor_string_of_int_qualifier : (FStar_Const.signedness * FStar_Const.width)  ->  Prims.string = (fun _51_9 -> (match (_51_9) with
| (FStar_Const.Unsigned, FStar_Const.Int8) -> begin
"FStar.UInt8.UInt8"
end
| (FStar_Const.Signed, FStar_Const.Int8) -> begin
"FStar.Int8.Int8"
end
| (FStar_Const.Unsigned, FStar_Const.Int16) -> begin
"FStar.UInt16.UInt16"
end
| (FStar_Const.Signed, FStar_Const.Int16) -> begin
"FStar.Int16.Int16"
end
| (FStar_Const.Unsigned, FStar_Const.Int32) -> begin
"FStar.UInt32.UInt32"
end
| (FStar_Const.Signed, FStar_Const.Int32) -> begin
"FStar.Int32.Int32"
end
| (FStar_Const.Unsigned, FStar_Const.Int64) -> begin
"FStar.UInt64.UInt64"
end
| (FStar_Const.Signed, FStar_Const.Int64) -> begin
"FStar.Int64.Int64"
end))


let encode_const : FStar_Const.sconst  ->  FStar_ToSMT_Term.term = (fun _51_10 -> (match (_51_10) with
| FStar_Const.Const_unit -> begin
FStar_ToSMT_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _147_566 = (let _147_565 = (let _147_564 = (let _147_563 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _147_563))
in (_147_564)::[])
in (("FStar.Char.Char"), (_147_565)))
in (FStar_ToSMT_Term.mkApp _147_566))
end
| FStar_Const.Const_int (i, None) -> begin
(let _147_567 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _147_567))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _147_571 = (let _147_570 = (let _147_569 = (let _147_568 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _147_568))
in (_147_569)::[])
in (((constructor_string_of_int_qualifier q)), (_147_570)))
in (FStar_ToSMT_Term.mkApp _147_571))
end
| FStar_Const.Const_string (bytes, _51_655) -> begin
(let _147_572 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _147_572))
end
| c -> begin
(let _147_574 = (let _147_573 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _147_573))
in (FStar_All.failwith _147_574))
end))


let as_function_typ : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_51_666) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_51_669) -> begin
(let _147_583 = (FStar_Absyn_Util.unrefine t)
in (aux true _147_583))
end
| _51_672 -> begin
if norm then begin
(let _147_584 = (whnf env t)
in (aux false _147_584))
end else begin
(let _147_587 = (let _147_586 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _147_585 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _147_586 _147_585)))
in (FStar_All.failwith _147_587))
end
end)))
in (aux true t0)))


let rec encode_knd_term : FStar_Absyn_Syntax.knd  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun k env -> (match ((let _147_624 = (FStar_Absyn_Util.compress_kind k)
in _147_624.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
((FStar_ToSMT_Term.mk_Kind_type), ([]))
end
| FStar_Absyn_Syntax.Kind_abbrev (_51_677, k0) -> begin
(

let _51_681 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _147_626 = (FStar_Absyn_Print.kind_to_string k)
in (let _147_625 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _147_626 _147_625)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _51_685) -> begin
(let _147_628 = (let _147_627 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _147_627))
in ((_147_628), ([])))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(

let tsym = (let _147_629 = (varops.fresh "t")
in ((_147_629), (FStar_ToSMT_Term.Type_sort)))
in (

let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (

let _51_700 = (encode_binders None bs env)
in (match (_51_700) with
| (vars, guards, env', decls, _51_699) -> begin
(

let app = (mk_ApplyT t vars)
in (

let _51_704 = (encode_knd kbody env' app)
in (match (_51_704) with
| (kbody, decls') -> begin
(

let rec aux = (fun app vars guards -> (match (((vars), (guards))) with
| ([], []) -> begin
kbody
end
| ((x)::vars, (g)::guards) -> begin
(

let app = (mk_ApplyT app ((x)::[]))
in (

let body = (aux app vars guards)
in (

let body = (match (vars) with
| [] -> begin
body
end
| _51_723 -> begin
(let _147_638 = (let _147_637 = (let _147_636 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _147_636))
in ((_147_637), (body)))
in (FStar_ToSMT_Term.mkAnd _147_638))
end)
in (let _147_640 = (let _147_639 = (FStar_ToSMT_Term.mkImp ((g), (body)))
in ((((app)::[])::[]), ((x)::[]), (_147_639)))
in (FStar_ToSMT_Term.mkForall _147_640)))))
end
| _51_726 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (

let k_interp = (aux t vars guards)
in (

let cvars = (let _147_642 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _147_642 (FStar_List.filter (fun _51_731 -> (match (_51_731) with
| (x, _51_730) -> begin
(x <> (Prims.fst tsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((tsym)::cvars), (k_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _51_737) -> begin
(let _147_645 = (let _147_644 = (let _147_643 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((k'), (_147_643)))
in (FStar_ToSMT_Term.mkApp _147_644))
in ((_147_645), ([])))
end
| None -> begin
(

let ksym = (varops.fresh "Kind_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _147_646 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_147_646))
end else begin
None
end
in (

let kdecl = FStar_ToSMT_Term.DeclFun (((ksym), (cvar_sorts), (FStar_ToSMT_Term.Kind_sort), (caption)))
in (

let k = (let _147_648 = (let _147_647 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((ksym), (_147_647)))
in (FStar_ToSMT_Term.mkApp _147_648))
in (

let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (

let k_interp = (let _147_657 = (let _147_656 = (let _147_655 = (let _147_654 = (let _147_653 = (let _147_652 = (let _147_651 = (let _147_650 = (let _147_649 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _147_649))
in ((_147_650), (k_interp)))
in (FStar_ToSMT_Term.mkAnd _147_651))
in ((t_has_k), (_147_652)))
in (FStar_ToSMT_Term.mkIff _147_653))
in ((((t_has_k)::[])::[]), ((tsym)::cvars), (_147_654)))
in (FStar_ToSMT_Term.mkForall _147_655))
in ((_147_656), (Some ((Prims.strcat ksym " interpretation")))))
in FStar_ToSMT_Term.Assume (_147_657))
in (

let k_decls = (FStar_List.append decls (FStar_List.append decls' ((kdecl)::(k_interp)::[])))
in (

let _51_749 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((ksym), (cvar_sorts), (k_decls)))
in ((k), (k_decls)))))))))))
end)))))
end)))
end))))
end
| _51_752 -> begin
(let _147_659 = (let _147_658 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _147_658))
in (FStar_All.failwith _147_659))
end))
and encode_knd : FStar_Absyn_Syntax.knd  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decl Prims.list) = (fun k env t -> (

let _51_758 = (encode_knd_term k env)
in (match (_51_758) with
| (k, decls) -> begin
(let _147_663 = (FStar_ToSMT_Term.mk_HasKind t k)
in ((_147_663), (decls)))
end)))
and encode_binders : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.binders  ->  env_t  ->  (FStar_ToSMT_Term.fv Prims.list * FStar_ToSMT_Term.term Prims.list * env_t * FStar_ToSMT_Term.decls_t * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list) = (fun fuel_opt bs env -> (

let _51_762 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_667 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _147_667))
end else begin
()
end
in (

let _51_812 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _51_769 b -> (match (_51_769) with
| (vars, guards, env, decls, names) -> begin
(

let _51_806 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _51_772}) -> begin
(

let a = (unmangle a)
in (

let _51_781 = (gen_typ_var env a)
in (match (_51_781) with
| (aasym, aa, env') -> begin
(

let _51_782 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _147_671 = (FStar_Absyn_Print.strBvd a)
in (let _147_670 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _147_671 aasym _147_670)))
end else begin
()
end
in (

let _51_786 = (encode_knd k env aa)
in (match (_51_786) with
| (guard_a_k, decls') -> begin
((((aasym), (FStar_ToSMT_Term.Type_sort))), (guard_a_k), (env'), (decls'), (FStar_Util.Inl (a)))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _51_788}) -> begin
(

let x = (unmangle x)
in (

let _51_797 = (gen_term_var env x)
in (match (_51_797) with
| (xxsym, xx, env') -> begin
(

let _51_800 = (let _147_672 = (norm_t env t)
in (encode_typ_pred fuel_opt _147_672 env xx))
in (match (_51_800) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_ToSMT_Term.Term_sort))), (guard_x_t), (env'), (decls'), (FStar_Util.Inr (x)))
end))
end)))
end)
in (match (_51_806) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_51_812) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_typ_pred : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _51_820 = (encode_typ_term t env)
in (match (_51_820) with
| (t, decls) -> begin
(let _147_677 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_147_677), (decls)))
end))))
and encode_typ_pred' : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _51_828 = (encode_typ_term t env)
in (match (_51_828) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _147_682 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in ((_147_682), (decls)))
end
| Some (f) -> begin
(let _147_683 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in ((_147_683), (decls)))
end)
end))))
and encode_typ_term : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _147_686 = (lookup_typ_var env a)
in ((_147_686), ([])))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _147_687 = (lookup_free_tvar env fv)
in ((_147_687), ([])))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(

let _51_849 = (encode_binders None binders env)
in (match (_51_849) with
| (vars, guards, env', decls, _51_848) -> begin
(

let fsym = (let _147_688 = (varops.fresh "f")
in ((_147_688), (FStar_ToSMT_Term.Term_sort)))
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let app = (mk_ApplyE f vars)
in (

let _51_855 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_51_855) with
| (pre_opt, res_t) -> begin
(

let _51_858 = (encode_typ_pred None res_t env' app)
in (match (_51_858) with
| (res_pred, decls') -> begin
(

let _51_867 = (match (pre_opt) with
| None -> begin
(let _147_689 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_689), (decls)))
end
| Some (pre) -> begin
(

let _51_864 = (encode_formula pre env')
in (match (_51_864) with
| (guard, decls0) -> begin
(let _147_690 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in ((_147_690), ((FStar_List.append decls decls0))))
end))
end)
in (match (_51_867) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _147_692 = (let _147_691 = (FStar_ToSMT_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_147_691)))
in (FStar_ToSMT_Term.mkForall _147_692))
in (

let cvars = (let _147_694 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _147_694 (FStar_List.filter (fun _51_872 -> (match (_51_872) with
| (x, _51_871) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _51_878) -> begin
(let _147_697 = (let _147_696 = (let _147_695 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((t'), (_147_695)))
in (FStar_ToSMT_Term.mkApp _147_696))
in ((_147_697), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_fun")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _147_698 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_147_698))
end else begin
None
end
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (caption)))
in (

let t = (let _147_700 = (let _147_699 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_147_699)))
in (FStar_ToSMT_Term.mkApp _147_700))
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let k_assumption = (let _147_702 = (let _147_701 = (FStar_ToSMT_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_147_701), (Some ((Prims.strcat tsym " kinding")))))
in FStar_ToSMT_Term.Assume (_147_702))
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (

let pre_typing = (let _147_709 = (let _147_708 = (let _147_707 = (let _147_706 = (let _147_705 = (let _147_704 = (let _147_703 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _147_703))
in ((f_has_t), (_147_704)))
in (FStar_ToSMT_Term.mkImp _147_705))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_147_706)))
in (mkForall_fuel _147_707))
in ((_147_708), (Some ("pre-typing for functions"))))
in FStar_ToSMT_Term.Assume (_147_709))
in (

let t_interp = (let _147_713 = (let _147_712 = (let _147_711 = (let _147_710 = (FStar_ToSMT_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_147_710)))
in (FStar_ToSMT_Term.mkForall _147_711))
in ((_147_712), (Some ((Prims.strcat tsym " interpretation")))))
in FStar_ToSMT_Term.Assume (_147_713))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[])))
in (

let _51_894 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Typ_fun")
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (FStar_ToSMT_Term.mkApp ((tsym), ([])))
in (

let t_kinding = (let _147_715 = (let _147_714 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in ((_147_714), (None)))
in FStar_ToSMT_Term.Assume (_147_715))
in (

let fsym = (("f"), (FStar_ToSMT_Term.Term_sort))
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let t_interp = (let _147_722 = (let _147_721 = (let _147_720 = (let _147_719 = (let _147_718 = (let _147_717 = (let _147_716 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _147_716))
in ((f_has_t), (_147_717)))
in (FStar_ToSMT_Term.mkImp _147_718))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_147_719)))
in (mkForall_fuel _147_720))
in ((_147_721), (Some ("pre-typing"))))
in FStar_ToSMT_Term.Assume (_147_722))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_51_905) -> begin
(

let _51_924 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _51_914; FStar_Absyn_Syntax.pos = _51_912; FStar_Absyn_Syntax.fvs = _51_910; FStar_Absyn_Syntax.uvs = _51_908} -> begin
((x), (f))
end
| _51_921 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_51_924) with
| (x, f) -> begin
(

let _51_927 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_51_927) with
| (base_t, decls) -> begin
(

let _51_931 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_51_931) with
| (x, xtm, env') -> begin
(

let _51_934 = (encode_formula f env')
in (match (_51_934) with
| (refinement, decls') -> begin
(

let _51_937 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_51_937) with
| (fsym, fterm) -> begin
(

let encoding = (let _147_724 = (let _147_723 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_147_723), (refinement)))
in (FStar_ToSMT_Term.mkAnd _147_724))
in (

let cvars = (let _147_726 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _147_726 (FStar_List.filter (fun _51_942 -> (match (_51_942) with
| (y, _51_941) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_ToSMT_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_ToSMT_Term.Fuel_sort))
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _51_949, _51_951) -> begin
(let _147_729 = (let _147_728 = (let _147_727 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in ((t), (_147_727)))
in (FStar_ToSMT_Term.mkApp _147_728))
in ((_147_729), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (let _147_731 = (let _147_730 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_147_730)))
in (FStar_ToSMT_Term.mkApp _147_731))
in (

let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let t_kinding = (FStar_ToSMT_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in (

let assumption = (let _147_733 = (let _147_732 = (FStar_ToSMT_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_147_732)))
in (FStar_ToSMT_Term.mkForall _147_733))
in (

let t_decls = (let _147_741 = (let _147_740 = (let _147_739 = (let _147_738 = (let _147_737 = (let _147_736 = (let _147_735 = (let _147_734 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_147_734))
in ((assumption), (_147_735)))
in FStar_ToSMT_Term.Assume (_147_736))
in (_147_737)::[])
in (FStar_ToSMT_Term.Assume (((t_kinding), (None))))::_147_738)
in (tdecl)::_147_739)
in (FStar_List.append decls' _147_740))
in (FStar_List.append decls _147_741))
in (

let _51_964 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls))))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _147_742 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _147_742))
in (

let _51_973 = (encode_knd k env ttm)
in (match (_51_973) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume (((t_has_k), (None)))
in ((ttm), ((d)::decls)))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let is_full_app = (fun _51_980 -> (match (()) with
| () -> begin
(

let kk = (FStar_Tc_Recheck.recompute_kind head)
in (

let _51_985 = (FStar_Absyn_Util.kind_formals kk)
in (match (_51_985) with
| (formals, _51_984) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (

let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(

let head = (lookup_typ_var env a)
in (

let _51_992 = (encode_args args env)
in (match (_51_992) with
| (args, decls) -> begin
(

let t = (mk_ApplyT_args head args)
in ((t), (decls)))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let _51_998 = (encode_args args env)
in (match (_51_998) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(

let head = (lookup_free_tvar_name env fv)
in (

let t = (let _147_747 = (let _147_746 = (FStar_List.map (fun _51_11 -> (match (_51_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in ((head), (_147_746)))
in (FStar_ToSMT_Term.mkApp _147_747))
in ((t), (decls))))
end else begin
(

let head = (lookup_free_tvar env fv)
in (

let t = (mk_ApplyT_args head args)
in ((t), (decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _147_748 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _147_748))
in (

let _51_1014 = (encode_knd k env ttm)
in (match (_51_1014) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume (((t_has_k), (None)))
in ((ttm), ((d)::decls)))
end)))
end
| _51_1017 -> begin
(

let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(

let _51_1029 = (encode_binders None bs env)
in (match (_51_1029) with
| (vars, guards, env, decls, _51_1028) -> begin
(

let _51_1032 = (encode_typ_term body env)
in (match (_51_1032) with
| (body, decls') -> begin
(

let key_body = (let _147_752 = (let _147_751 = (let _147_750 = (let _147_749 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_749), (body)))
in (FStar_ToSMT_Term.mkImp _147_750))
in (([]), (vars), (_147_751)))
in (FStar_ToSMT_Term.mkForall _147_752))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _51_1038, _51_1040) -> begin
(let _147_755 = (let _147_754 = (let _147_753 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((t), (_147_753)))
in (FStar_ToSMT_Term.mkApp _147_754))
in ((_147_755), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
((head), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tsym = (varops.fresh "Typ_lam")
in (

let tdecl = FStar_ToSMT_Term.DeclFun (((tsym), (cvar_sorts), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let t = (let _147_757 = (let _147_756 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((tsym), (_147_756)))
in (FStar_ToSMT_Term.mkApp _147_757))
in (

let app = (mk_ApplyT t vars)
in (

let interp = (let _147_764 = (let _147_763 = (let _147_762 = (let _147_761 = (let _147_760 = (let _147_759 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_758 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_147_759), (_147_758))))
in (FStar_ToSMT_Term.mkImp _147_760))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_147_761)))
in (FStar_ToSMT_Term.mkForall _147_762))
in ((_147_763), (Some ("Typ_lam interpretation"))))
in FStar_ToSMT_Term.Assume (_147_764))
in (

let kinding = (

let _51_1055 = (let _147_765 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _147_765 env t))
in (match (_51_1055) with
| (ktm, decls'') -> begin
(let _147_769 = (let _147_768 = (let _147_767 = (let _147_766 = (FStar_ToSMT_Term.mkForall ((((t)::[])::[]), (cvars), (ktm)))
in ((_147_766), (Some ("Typ_lam kinding"))))
in FStar_ToSMT_Term.Assume (_147_767))
in (_147_768)::[])
in (FStar_List.append decls'' _147_769))
end))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(interp)::kinding)))
in (

let _51_1058 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _51_1062) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_51_1066) -> begin
(let _147_770 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _147_770 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _147_775 = (let _147_774 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _147_773 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _147_772 = (FStar_Absyn_Print.typ_to_string t0)
in (let _147_771 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _147_774 _147_773 _147_772 _147_771)))))
in (FStar_All.failwith _147_775))
end)))
and encode_exp : FStar_Absyn_Syntax.exp  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun e env -> (

let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (

let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_51_1077) -> begin
(let _147_778 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _147_778 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _51_1084) -> begin
(let _147_779 = (lookup_free_var env v)
in ((_147_779), ([])))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _147_780 = (encode_const c)
in ((_147_780), ([])))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _51_1092) -> begin
(

let _51_1095 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _51_1099)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _51_1105) -> begin
(

let e = (let _147_781 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _147_781))
in ((e), ([])))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let fallback = (fun _51_1114 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Exp_abs")
in (

let decl = FStar_ToSMT_Term.DeclFun (((f), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (let _147_784 = (FStar_ToSMT_Term.mkFreeV ((f), (FStar_ToSMT_Term.Term_sort)))
in ((_147_784), ((decl)::[])))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(

let _51_1118 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _147_785 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _147_785)) then begin
(fallback ())
end else begin
(

let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(

let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(

let _51_1130 = (FStar_Util.first_N nformals bs)
in (match (_51_1130) with
| (bs0, rest) -> begin
(

let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _51_1134 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let e = (let _147_787 = (let _147_786 = (FStar_Absyn_Syntax.mk_Exp_abs ((rest), (body)) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in ((bs0), (_147_786)))
in (FStar_Absyn_Syntax.mk_Exp_abs _147_787 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(

let _51_1143 = (encode_binders None bs env)
in (match (_51_1143) with
| (vars, guards, envbody, decls, _51_1142) -> begin
(

let _51_1146 = (encode_exp body envbody)
in (match (_51_1146) with
| (body, decls') -> begin
(

let key_body = (let _147_791 = (let _147_790 = (let _147_789 = (let _147_788 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_788), (body)))
in (FStar_ToSMT_Term.mkImp _147_789))
in (([]), (vars), (_147_790)))
in (FStar_ToSMT_Term.mkForall _147_791))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _51_1152, _51_1154) -> begin
(let _147_794 = (let _147_793 = (let _147_792 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((t), (_147_792)))
in (FStar_ToSMT_Term.mkApp _147_793))
in ((_147_794), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.fresh "Exp_abs")
in (

let fdecl = FStar_ToSMT_Term.DeclFun (((fsym), (cvar_sorts), (FStar_ToSMT_Term.Term_sort), (None)))
in (

let f = (let _147_796 = (let _147_795 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in ((fsym), (_147_795)))
in (FStar_ToSMT_Term.mkApp _147_796))
in (

let app = (mk_ApplyE f vars)
in (

let _51_1168 = (encode_typ_pred None tfun env f)
in (match (_51_1168) with
| (f_has_t, decls'') -> begin
(

let typing_f = (let _147_798 = (let _147_797 = (FStar_ToSMT_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_147_797), (Some ((Prims.strcat fsym " typing")))))
in FStar_ToSMT_Term.Assume (_147_798))
in (

let interp_f = (let _147_805 = (let _147_804 = (let _147_803 = (let _147_802 = (let _147_801 = (let _147_800 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _147_799 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_147_800), (_147_799))))
in (FStar_ToSMT_Term.mkImp _147_801))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_147_802)))
in (FStar_ToSMT_Term.mkForall _147_803))
in ((_147_804), (Some ((Prims.strcat fsym " interpretation")))))
in FStar_ToSMT_Term.Assume (_147_805))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::decls'') ((typing_f)::(interp_f)::[]))))
in (

let _51_1172 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls))))))
end)))))))
end)
end))))
end))
end))
end)
end
| _51_1175 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _51_1186); FStar_Absyn_Syntax.tk = _51_1183; FStar_Absyn_Syntax.pos = _51_1181; FStar_Absyn_Syntax.fvs = _51_1179; FStar_Absyn_Syntax.uvs = _51_1177}, ((FStar_Util.Inl (_51_1201), _51_1204))::((FStar_Util.Inr (v1), _51_1198))::((FStar_Util.Inr (v2), _51_1193))::[]) when (FStar_Ident.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(

let _51_1211 = (encode_exp v1 env)
in (match (_51_1211) with
| (v1, decls1) -> begin
(

let _51_1214 = (encode_exp v2 env)
in (match (_51_1214) with
| (v2, decls2) -> begin
(let _147_806 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in ((_147_806), ((FStar_List.append decls1 decls2))))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_51_1224); FStar_Absyn_Syntax.tk = _51_1222; FStar_Absyn_Syntax.pos = _51_1220; FStar_Absyn_Syntax.fvs = _51_1218; FStar_Absyn_Syntax.uvs = _51_1216}, _51_1228) -> begin
(let _147_807 = (whnf_e env e)
in (encode_exp _147_807 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(

let _51_1237 = (encode_args args_e env)
in (match (_51_1237) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _51_1242 = (encode_exp head env)
in (match (_51_1242) with
| (head, decls') -> begin
(

let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _51_1251 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_51_1251) with
| (formals, rest) -> begin
(

let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (

let ty = (let _147_810 = (FStar_Absyn_Syntax.mk_Typ_fun ((rest), (c)) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _147_810 (FStar_Absyn_Util.subst_typ subst)))
in (

let _51_1256 = (encode_typ_pred None ty env app_tm)
in (match (_51_1256) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (

let e_typing = (let _147_812 = (let _147_811 = (FStar_ToSMT_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in ((_147_811), (None)))
in FStar_ToSMT_Term.Assume (_147_812))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _51_1263 = (lookup_free_var_sym env fv)
in (match (_51_1263) with
| (fname, fuel_args) -> begin
(

let tm = (let _147_818 = (let _147_817 = (let _147_816 = (FStar_List.map (fun _51_12 -> (match (_51_12) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _147_816))
in ((fname), (_147_817)))
in (FStar_ToSMT_Term.mkApp' _147_818))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Absyn_Util.compress_exp head)
in (

let _51_1270 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _147_820 = (FStar_Absyn_Print.exp_to_string head)
in (let _147_819 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _147_820 _147_819)))
end else begin
()
end
in (

let head_type = (let _147_823 = (let _147_822 = (let _147_821 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _147_821))
in (whnf env _147_822))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _147_823))
in (

let _51_1273 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _147_826 = (FStar_Absyn_Print.exp_to_string head)
in (let _147_825 = (FStar_Absyn_Print.tag_of_exp head)
in (let _147_824 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _147_826 _147_825 _147_824))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _147_830 = (let _147_829 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _147_828 = (FStar_Absyn_Print.exp_to_string e0)
in (let _147_827 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _147_829 _147_828 _147_827))))
in (FStar_All.failwith _147_830))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _51_1282) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _51_1286 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some (((formals), (c)))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_51_1295); FStar_Absyn_Syntax.lbtyp = _51_1293; FStar_Absyn_Syntax.lbeff = _51_1291; FStar_Absyn_Syntax.lbdef = _51_1289})::[]), _51_1301) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _51_1307; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _51_1319 = (encode_exp e1 env)
in (match (_51_1319) with
| (ee1, decls1) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _51_1323 = (encode_exp e2 env')
in (match (_51_1323) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_51_1325) -> begin
(

let _51_1327 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_ToSMT_Term.DeclFun (((e), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (let _147_831 = (FStar_ToSMT_Term.mkFreeV ((e), (FStar_ToSMT_Term.Term_sort)))
in ((_147_831), ((decl_e)::[]))))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(

let _51_1337 = (encode_exp e env)
in (match (_51_1337) with
| (scr, decls) -> begin
(

let _51_1377 = (FStar_List.fold_right (fun _51_1341 _51_1344 -> (match (((_51_1341), (_51_1344))) with
| ((p, w, br), (else_case, decls)) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _51_1348 _51_1351 -> (match (((_51_1348), (_51_1351))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _51_1357 -> (match (_51_1357) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (

let _51_1371 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _51_1368 = (encode_exp w env)
in (match (_51_1368) with
| (w, decls2) -> begin
(let _147_842 = (let _147_841 = (let _147_840 = (let _147_839 = (let _147_838 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in ((w), (_147_838)))
in (FStar_ToSMT_Term.mkEq _147_839))
in ((guard), (_147_840)))
in (FStar_ToSMT_Term.mkAnd _147_841))
in ((_147_842), (decls2)))
end))
end)
in (match (_51_1371) with
| (guard, decls2) -> begin
(

let _51_1374 = (encode_exp br env)
in (match (_51_1374) with
| (br, decls3) -> begin
(let _147_843 = (FStar_ToSMT_Term.mkITE ((guard), (br), (else_case)))
in ((_147_843), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end)) pats ((FStar_ToSMT_Term.mk_Term_unit), (decls)))
in (match (_51_1377) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_51_1379) -> begin
(let _147_846 = (let _147_845 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _147_844 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _147_845 _147_844)))
in (FStar_All.failwith _147_846))
end))))
and encode_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _51_1386 -> begin
(let _147_849 = (encode_one_pat env pat)
in (_147_849)::[])
end))
and encode_one_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _51_1389 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_852 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _147_852))
end else begin
()
end
in (

let _51_1393 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_51_1393) with
| (vars, pat_exp_or_typ) -> begin
(

let _51_1414 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _51_1396 v -> (match (_51_1396) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(

let _51_1404 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_51_1404) with
| (aa, _51_1402, env) -> begin
((env), ((((v), (((aa), (FStar_ToSMT_Term.Type_sort)))))::vars))
end))
end
| FStar_Util.Inr (x) -> begin
(

let _51_1411 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_51_1411) with
| (xx, _51_1409, env) -> begin
((env), ((((v), (((xx), (FStar_ToSMT_Term.Term_sort)))))::vars))
end))
end)
end)) ((env), ([]))))
in (match (_51_1414) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_51_1419) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _147_860 = (let _147_859 = (encode_const c)
in ((scrutinee), (_147_859)))
in (FStar_ToSMT_Term.mkEq _147_860))
end
| FStar_Absyn_Syntax.Pat_cons (f, _51_1443, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _51_1452 -> (match (_51_1452) with
| (arg, _51_1451) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _147_863 = (FStar_ToSMT_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _147_863)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_51_1459) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
(((FStar_Util.Inr (x)), (scrutinee)))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
(((FStar_Util.Inl (a)), (scrutinee)))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_51_1476) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _51_1480, args) -> begin
(let _147_871 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _51_1488 -> (match (_51_1488) with
| (arg, _51_1487) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _147_870 = (FStar_ToSMT_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _147_870)))
end))))
in (FStar_All.pipe_right _147_871 FStar_List.flatten))
end))
in (

let pat_term = (fun _51_1491 -> (match (()) with
| () -> begin
(match (pat_exp_or_typ) with
| FStar_Util.Inl (t) -> begin
(encode_typ_term t env)
end
| FStar_Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Absyn_Syntax.args  ->  env_t  ->  ((FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list * FStar_ToSMT_Term.decls_t) = (fun l env -> (

let _51_1521 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _51_1501 x -> (match (_51_1501) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _51_1506) -> begin
(

let _51_1510 = (encode_typ_term t env)
in (match (_51_1510) with
| (t, decls') -> begin
(((FStar_Util.Inl (t))::tms), ((FStar_List.append decls decls')))
end))
end
| (FStar_Util.Inr (e), _51_1514) -> begin
(

let _51_1518 = (encode_exp e env)
in (match (_51_1518) with
| (t, decls') -> begin
(((FStar_Util.Inr (t))::tms), ((FStar_List.append decls decls')))
end))
end)
end)) (([]), ([]))))
in (match (_51_1521) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_formula : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let _51_1527 = (encode_formula_with_labels phi env)
in (match (_51_1527) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
((t), (decls))
end
| _51_1530 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (match ((let _147_886 = (FStar_Absyn_Util.unmeta_exp e)
in _147_886.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _51_1547); FStar_Absyn_Syntax.tk = _51_1544; FStar_Absyn_Syntax.pos = _51_1542; FStar_Absyn_Syntax.fvs = _51_1540; FStar_Absyn_Syntax.uvs = _51_1538}, _51_1552) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _51_1565); FStar_Absyn_Syntax.tk = _51_1562; FStar_Absyn_Syntax.pos = _51_1560; FStar_Absyn_Syntax.fvs = _51_1558; FStar_Absyn_Syntax.uvs = _51_1556}, (_51_1580)::((FStar_Util.Inr (hd), _51_1577))::((FStar_Util.Inr (tl), _51_1572))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _147_887 = (list_elements tl)
in (hd)::_147_887)
end
| _51_1585 -> begin
(

let _51_1586 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let v_or_t_pat = (fun p -> (match ((let _147_890 = (FStar_Absyn_Util.unmeta_exp p)
in _147_890.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _51_1600); FStar_Absyn_Syntax.tk = _51_1597; FStar_Absyn_Syntax.pos = _51_1595; FStar_Absyn_Syntax.fvs = _51_1593; FStar_Absyn_Syntax.uvs = _51_1591}, ((FStar_Util.Inl (_51_1610), _51_1613))::((FStar_Util.Inr (e), _51_1607))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _51_1628); FStar_Absyn_Syntax.tk = _51_1625; FStar_Absyn_Syntax.pos = _51_1623; FStar_Absyn_Syntax.fvs = _51_1621; FStar_Absyn_Syntax.uvs = _51_1619}, ((FStar_Util.Inl (t), _51_1635))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _51_1641 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (match (elts) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _51_1663); FStar_Absyn_Syntax.tk = _51_1660; FStar_Absyn_Syntax.pos = _51_1658; FStar_Absyn_Syntax.fvs = _51_1656; FStar_Absyn_Syntax.uvs = _51_1654}, ((FStar_Util.Inr (e), _51_1670))::[]); FStar_Absyn_Syntax.tk = _51_1652; FStar_Absyn_Syntax.pos = _51_1650; FStar_Absyn_Syntax.fvs = _51_1648; FStar_Absyn_Syntax.uvs = _51_1646})::[] when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _147_895 = (list_elements e)
in (FStar_All.pipe_right _147_895 (FStar_List.map (fun branch -> (let _147_894 = (list_elements branch)
in (FStar_All.pipe_right _147_894 (FStar_List.map v_or_t_pat)))))))
end
| _51_1679 -> begin
(let _147_896 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_147_896)::[])
end)))
in (

let _51_1722 = (match ((let _147_897 = (FStar_Absyn_Util.compress_typ t)
in _147_897.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _51_1688; FStar_Absyn_Syntax.pos = _51_1686; FStar_Absyn_Syntax.fvs = _51_1684; FStar_Absyn_Syntax.uvs = _51_1682}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (pre), _51_1707))::((FStar_Util.Inl (post), _51_1702))::((FStar_Util.Inr (pats), _51_1697))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _147_898 = (lemma_pats pats')
in ((binders), (pre), (post), (_147_898))))
end
| _51_1715 -> begin
(FStar_All.failwith "impos")
end)
end
| _51_1717 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_51_1722) with
| (binders, pre, post, patterns) -> begin
(

let _51_1729 = (encode_binders None binders env)
in (match (_51_1729) with
| (vars, guards, env, decls, _51_1728) -> begin
(

let _51_1749 = (let _147_902 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _51_1746 = (let _147_901 = (FStar_All.pipe_right branch (FStar_List.map (fun _51_13 -> (match (_51_13) with
| (FStar_Util.Inl (t), _51_1735) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _51_1740) -> begin
(encode_exp e (

let _51_1742 = env
in {bindings = _51_1742.bindings; depth = _51_1742.depth; tcenv = _51_1742.tcenv; warn = _51_1742.warn; cache = _51_1742.cache; nolabels = _51_1742.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _51_1742.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _147_901 FStar_List.unzip))
in (match (_51_1746) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _147_902 FStar_List.unzip))
in (match (_51_1749) with
| (pats, decls') -> begin
(

let decls' = (FStar_List.flatten decls')
in (

let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| (l)::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _147_905 = (let _147_904 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _147_904 e))
in (_147_905)::p))))
end
| _51_1759 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _147_911 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_147_911)::p))))
end
| ((x, FStar_ToSMT_Term.Term_sort))::vars -> begin
(let _147_913 = (let _147_912 = (FStar_ToSMT_Term.mkFreeV ((x), (FStar_ToSMT_Term.Term_sort)))
in (FStar_ToSMT_Term.mk_LexCons _147_912 tl))
in (aux _147_913 vars))
end
| _51_1771 -> begin
pats
end))
in (let _147_914 = (FStar_ToSMT_Term.mkFreeV (("Prims.LexTop"), (FStar_ToSMT_Term.Term_sort)))
in (aux _147_914 vars)))
end)
end)
in (

let env = (

let _51_1773 = env
in {bindings = _51_1773.bindings; depth = _51_1773.depth; tcenv = _51_1773.tcenv; warn = _51_1773.warn; cache = _51_1773.cache; nolabels = true; use_zfuel_name = _51_1773.use_zfuel_name; encode_non_total_function_typ = _51_1773.encode_non_total_function_typ})
in (

let _51_1778 = (let _147_915 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _147_915 env))
in (match (_51_1778) with
| (pre, decls'') -> begin
(

let _51_1781 = (let _147_916 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _147_916 env))
in (match (_51_1781) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _147_921 = (let _147_920 = (let _147_919 = (let _147_918 = (let _147_917 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in ((_147_917), (post)))
in (FStar_ToSMT_Term.mkImp _147_918))
in ((pats), (vars), (_147_919)))
in (FStar_ToSMT_Term.mkForall _147_920))
in ((_147_921), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * labels * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let enc = (fun f l -> (

let _51_1802 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(

let _51_1794 = (encode_typ_term t env)
in (match (_51_1794) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))
end
| FStar_Util.Inr (e) -> begin
(

let _51_1799 = (encode_exp e env)
in (match (_51_1799) with
| (e, decls') -> begin
(((FStar_List.append decls decls')), (e))
end))
end)) [] l)
in (match (_51_1802) with
| (decls, args) -> begin
(let _147_939 = (f args)
in ((_147_939), ([]), (decls)))
end)))
in (

let enc_prop_c = (fun f l -> (

let _51_1822 = (FStar_List.fold_right (fun t _51_1810 -> (match (_51_1810) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(

let _51_1816 = (encode_formula_with_labels t env)
in (match (_51_1816) with
| (phi, labs', decls') -> begin
(((phi)::phis), ((FStar_List.append labs' labs)), ((FStar_List.append decls' decls)))
end))
end
| _51_1818 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l (([]), ([]), ([])))
in (match (_51_1822) with
| (phis, labs, decls) -> begin
(let _147_955 = (f phis)
in ((_147_955), (labs), (decls)))
end)))
in (

let const_op = (fun f _51_1825 -> ((f), ([]), ([])))
in (

let un_op = (fun f l -> (let _147_969 = (FStar_List.hd l)
in (FStar_All.pipe_left f _147_969)))
in (

let bin_op = (fun f _51_14 -> (match (_51_14) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _51_1836 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let eq_op = (fun _51_15 -> (match (_51_15) with
| (_51_1844)::(_51_1842)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (

let mk_imp = (fun _51_16 -> (match (_51_16) with
| ((FStar_Util.Inl (lhs), _51_1857))::((FStar_Util.Inl (rhs), _51_1852))::[] -> begin
(

let _51_1863 = (encode_formula_with_labels rhs env)
in (match (_51_1863) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _51_1866) -> begin
((l1), (labs1), (decls1))
end
| _51_1870 -> begin
(

let _51_1874 = (encode_formula_with_labels lhs env)
in (match (_51_1874) with
| (l2, labs2, decls2) -> begin
(let _147_983 = (FStar_ToSMT_Term.mkImp ((l2), (l1)))
in ((_147_983), ((FStar_List.append labs1 labs2)), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _51_1876 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _51_17 -> (match (_51_17) with
| ((FStar_Util.Inl (guard), _51_1892))::((FStar_Util.Inl (_then), _51_1887))::((FStar_Util.Inl (_else), _51_1882))::[] -> begin
(

let _51_1898 = (encode_formula_with_labels guard env)
in (match (_51_1898) with
| (g, labs1, decls1) -> begin
(

let _51_1902 = (encode_formula_with_labels _then env)
in (match (_51_1902) with
| (t, labs2, decls2) -> begin
(

let _51_1906 = (encode_formula_with_labels _else env)
in (match (_51_1906) with
| (e, labs3, decls3) -> begin
(

let res = (FStar_ToSMT_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append labs1 (FStar_List.append labs2 labs3))), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _51_1909 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _147_995 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _147_995)))
in (

let connectives = (let _147_1056 = (let _147_1004 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in ((FStar_Absyn_Const.and_lid), (_147_1004)))
in (let _147_1055 = (let _147_1054 = (let _147_1010 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in ((FStar_Absyn_Const.or_lid), (_147_1010)))
in (let _147_1053 = (let _147_1052 = (let _147_1051 = (let _147_1019 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in ((FStar_Absyn_Const.iff_lid), (_147_1019)))
in (let _147_1050 = (let _147_1049 = (let _147_1048 = (let _147_1028 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in ((FStar_Absyn_Const.not_lid), (_147_1028)))
in (let _147_1047 = (let _147_1046 = (let _147_1034 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in ((FStar_Absyn_Const.eqT_lid), (_147_1034)))
in (_147_1046)::(((FStar_Absyn_Const.eq2_lid), (eq_op)))::(((FStar_Absyn_Const.true_lid), ((const_op FStar_ToSMT_Term.mkTrue))))::(((FStar_Absyn_Const.false_lid), ((const_op FStar_ToSMT_Term.mkFalse))))::[])
in (_147_1048)::_147_1047))
in (((FStar_Absyn_Const.ite_lid), (mk_ite)))::_147_1049)
in (_147_1051)::_147_1050))
in (((FStar_Absyn_Const.imp_lid), (mk_imp)))::_147_1052)
in (_147_1054)::_147_1053))
in (_147_1056)::_147_1055))
in (

let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(

let _51_1927 = (encode_formula_with_labels phi' env)
in (match (_51_1927) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
((phi), ([]), (decls))
end else begin
(

let lvar = (let _147_1059 = (varops.fresh "label")
in ((_147_1059), (FStar_ToSMT_Term.Bool_sort)))
in (

let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (

let lphi = (FStar_ToSMT_Term.mkOr ((lterm), (phi)))
in ((lphi), ((((lvar), (msg), (r)))::labs), (decls)))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _51_1938; FStar_Absyn_Syntax.pos = _51_1936; FStar_Absyn_Syntax.fvs = _51_1934; FStar_Absyn_Syntax.uvs = _51_1932}, (_51_1953)::((FStar_Util.Inr (l), _51_1950))::((FStar_Util.Inl (phi), _51_1945))::[]) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let _51_1959 = (encode_exp l env)
in (match (_51_1959) with
| (e, decls) -> begin
(

let _51_1962 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_51_1962) with
| (f, decls') -> begin
((f), ([]), ((FStar_List.append decls decls')))
end))
end))
end else begin
((FStar_ToSMT_Term.mkTrue), ([]), ([]))
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _51_1970; FStar_Absyn_Syntax.pos = _51_1968; FStar_Absyn_Syntax.fvs = _51_1966; FStar_Absyn_Syntax.uvs = _51_1964}, (_51_1982)::((FStar_Util.Inl (phi), _51_1978))::tl) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let pat = (match (tl) with
| [] -> begin
None
end
| ((FStar_Util.Inr (pat), _51_1990))::[] -> begin
Some (pat)
end
| _51_1994 -> begin
(Prims.raise Bad_form)
end)
in (

let _51_1998 = (encode_function_type_as_formula None pat phi env)
in (match (_51_1998) with
| (f, decls) -> begin
((f), ([]), (decls))
end)))
end else begin
((FStar_ToSMT_Term.mkTrue), ([]), ([]))
end
end
| _51_2000 -> begin
(

let _51_2003 = (encode_typ_term phi env)
in (match (_51_2003) with
| (tt, decls) -> begin
(let _147_1060 = (FStar_ToSMT_Term.mk_Valid tt)
in ((_147_1060), ([]), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _51_2015 = (encode_binders None bs env)
in (match (_51_2015) with
| (vars, guards, env, decls, _51_2014) -> begin
(

let _51_2035 = (let _147_1072 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _51_2032 = (let _147_1071 = (FStar_All.pipe_right p (FStar_List.map (fun _51_18 -> (match (_51_18) with
| (FStar_Util.Inl (t), _51_2021) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _51_2026) -> begin
(encode_exp e (

let _51_2028 = env
in {bindings = _51_2028.bindings; depth = _51_2028.depth; tcenv = _51_2028.tcenv; warn = _51_2028.warn; cache = _51_2028.cache; nolabels = _51_2028.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _51_2028.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _147_1071 FStar_List.unzip))
in (match (_51_2032) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _147_1072 FStar_List.unzip))
in (match (_51_2035) with
| (pats, decls') -> begin
(

let _51_2039 = (encode_formula_with_labels body env)
in (match (_51_2039) with
| (body, labs, decls'') -> begin
(let _147_1073 = (FStar_ToSMT_Term.mk_and_l guards)
in ((vars), (pats), (_147_1073), (body), (labs), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls'')))))
end))
end))
end)))
in (

let _51_2040 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_1074 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _147_1074))
end else begin
()
end
in (

let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _51_2052 -> (match (_51_2052) with
| (l, _51_2051) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_51_2055, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(

let _51_2065 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_1091 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _147_1091))
end else begin
()
end
in (

let _51_2073 = (encode_q_body env vars pats body)
in (match (_51_2073) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _147_1094 = (let _147_1093 = (let _147_1092 = (FStar_ToSMT_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_147_1092)))
in (FStar_ToSMT_Term.mkForall _147_1093))
in ((_147_1094), (labs), (decls)))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(

let _51_2086 = (encode_q_body env vars pats body)
in (match (_51_2086) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _147_1097 = (let _147_1096 = (let _147_1095 = (FStar_ToSMT_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_147_1095)))
in (FStar_ToSMT_Term.mkExists _147_1096))
in ((_147_1097), (labs), (decls)))
end))
end))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _51_2092 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_51_2092) with
| (asym, a) -> begin
(

let _51_2095 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_51_2095) with
| (xsym, x) -> begin
(

let _51_2098 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_51_2098) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (let _147_1132 = (let _147_1131 = (let _147_1130 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _147_1129 = (FStar_ToSMT_Term.abstr vars body)
in ((x), (_147_1130), (FStar_ToSMT_Term.Term_sort), (_147_1129), (None))))
in FStar_ToSMT_Term.DefineFun (_147_1131))
in (_147_1132)::[]))
in (

let quant = (fun vars body x -> (

let t1 = (let _147_1144 = (let _147_1143 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((x), (_147_1143)))
in (FStar_ToSMT_Term.mkApp _147_1144))
in (

let vname_decl = (let _147_1146 = (let _147_1145 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_147_1145), (FStar_ToSMT_Term.Term_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_1146))
in (let _147_1152 = (let _147_1151 = (let _147_1150 = (let _147_1149 = (let _147_1148 = (let _147_1147 = (FStar_ToSMT_Term.mkEq ((t1), (body)))
in ((((t1)::[])::[]), (vars), (_147_1147)))
in (FStar_ToSMT_Term.mkForall _147_1148))
in ((_147_1149), (None)))
in FStar_ToSMT_Term.Assume (_147_1150))
in (_147_1151)::[])
in (vname_decl)::_147_1152))))
in (

let def_or_quant = (fun vars body x -> if (FStar_Options.inline_arith ()) then begin
(deffun vars body x)
end else begin
(quant vars body x)
end)
in (

let axy = (((asym), (FStar_ToSMT_Term.Type_sort)))::(((xsym), (FStar_ToSMT_Term.Term_sort)))::(((ysym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_ToSMT_Term.Term_sort)))::(((ysym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_ToSMT_Term.Term_sort)))::[]
in (

let prims = (let _147_1318 = (let _147_1167 = (let _147_1166 = (let _147_1165 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1165))
in (def_or_quant axy _147_1166))
in ((FStar_Absyn_Const.op_Eq), (_147_1167)))
in (let _147_1317 = (let _147_1316 = (let _147_1174 = (let _147_1173 = (let _147_1172 = (let _147_1171 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in (FStar_ToSMT_Term.mkNot _147_1171))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1172))
in (def_or_quant axy _147_1173))
in ((FStar_Absyn_Const.op_notEq), (_147_1174)))
in (let _147_1315 = (let _147_1314 = (let _147_1183 = (let _147_1182 = (let _147_1181 = (let _147_1180 = (let _147_1179 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1178 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1179), (_147_1178))))
in (FStar_ToSMT_Term.mkLT _147_1180))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1181))
in (def_or_quant xy _147_1182))
in ((FStar_Absyn_Const.op_LT), (_147_1183)))
in (let _147_1313 = (let _147_1312 = (let _147_1192 = (let _147_1191 = (let _147_1190 = (let _147_1189 = (let _147_1188 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1187 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1188), (_147_1187))))
in (FStar_ToSMT_Term.mkLTE _147_1189))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1190))
in (def_or_quant xy _147_1191))
in ((FStar_Absyn_Const.op_LTE), (_147_1192)))
in (let _147_1311 = (let _147_1310 = (let _147_1201 = (let _147_1200 = (let _147_1199 = (let _147_1198 = (let _147_1197 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1196 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1197), (_147_1196))))
in (FStar_ToSMT_Term.mkGT _147_1198))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1199))
in (def_or_quant xy _147_1200))
in ((FStar_Absyn_Const.op_GT), (_147_1201)))
in (let _147_1309 = (let _147_1308 = (let _147_1210 = (let _147_1209 = (let _147_1208 = (let _147_1207 = (let _147_1206 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1205 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1206), (_147_1205))))
in (FStar_ToSMT_Term.mkGTE _147_1207))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1208))
in (def_or_quant xy _147_1209))
in ((FStar_Absyn_Const.op_GTE), (_147_1210)))
in (let _147_1307 = (let _147_1306 = (let _147_1219 = (let _147_1218 = (let _147_1217 = (let _147_1216 = (let _147_1215 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1214 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1215), (_147_1214))))
in (FStar_ToSMT_Term.mkSub _147_1216))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1217))
in (def_or_quant xy _147_1218))
in ((FStar_Absyn_Const.op_Subtraction), (_147_1219)))
in (let _147_1305 = (let _147_1304 = (let _147_1226 = (let _147_1225 = (let _147_1224 = (let _147_1223 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _147_1223))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1224))
in (def_or_quant qx _147_1225))
in ((FStar_Absyn_Const.op_Minus), (_147_1226)))
in (let _147_1303 = (let _147_1302 = (let _147_1235 = (let _147_1234 = (let _147_1233 = (let _147_1232 = (let _147_1231 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1230 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1231), (_147_1230))))
in (FStar_ToSMT_Term.mkAdd _147_1232))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1233))
in (def_or_quant xy _147_1234))
in ((FStar_Absyn_Const.op_Addition), (_147_1235)))
in (let _147_1301 = (let _147_1300 = (let _147_1244 = (let _147_1243 = (let _147_1242 = (let _147_1241 = (let _147_1240 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1239 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1240), (_147_1239))))
in (FStar_ToSMT_Term.mkMul _147_1241))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1242))
in (def_or_quant xy _147_1243))
in ((FStar_Absyn_Const.op_Multiply), (_147_1244)))
in (let _147_1299 = (let _147_1298 = (let _147_1253 = (let _147_1252 = (let _147_1251 = (let _147_1250 = (let _147_1249 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1248 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1249), (_147_1248))))
in (FStar_ToSMT_Term.mkDiv _147_1250))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1251))
in (def_or_quant xy _147_1252))
in ((FStar_Absyn_Const.op_Division), (_147_1253)))
in (let _147_1297 = (let _147_1296 = (let _147_1262 = (let _147_1261 = (let _147_1260 = (let _147_1259 = (let _147_1258 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1257 = (FStar_ToSMT_Term.unboxInt y)
in ((_147_1258), (_147_1257))))
in (FStar_ToSMT_Term.mkMod _147_1259))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _147_1260))
in (def_or_quant xy _147_1261))
in ((FStar_Absyn_Const.op_Modulus), (_147_1262)))
in (let _147_1295 = (let _147_1294 = (let _147_1271 = (let _147_1270 = (let _147_1269 = (let _147_1268 = (let _147_1267 = (FStar_ToSMT_Term.unboxBool x)
in (let _147_1266 = (FStar_ToSMT_Term.unboxBool y)
in ((_147_1267), (_147_1266))))
in (FStar_ToSMT_Term.mkAnd _147_1268))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1269))
in (def_or_quant xy _147_1270))
in ((FStar_Absyn_Const.op_And), (_147_1271)))
in (let _147_1293 = (let _147_1292 = (let _147_1280 = (let _147_1279 = (let _147_1278 = (let _147_1277 = (let _147_1276 = (FStar_ToSMT_Term.unboxBool x)
in (let _147_1275 = (FStar_ToSMT_Term.unboxBool y)
in ((_147_1276), (_147_1275))))
in (FStar_ToSMT_Term.mkOr _147_1277))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1278))
in (def_or_quant xy _147_1279))
in ((FStar_Absyn_Const.op_Or), (_147_1280)))
in (let _147_1291 = (let _147_1290 = (let _147_1287 = (let _147_1286 = (let _147_1285 = (let _147_1284 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _147_1284))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_1285))
in (def_or_quant qx _147_1286))
in ((FStar_Absyn_Const.op_Negation), (_147_1287)))
in (_147_1290)::[])
in (_147_1292)::_147_1291))
in (_147_1294)::_147_1293))
in (_147_1296)::_147_1295))
in (_147_1298)::_147_1297))
in (_147_1300)::_147_1299))
in (_147_1302)::_147_1301))
in (_147_1304)::_147_1303))
in (_147_1306)::_147_1305))
in (_147_1308)::_147_1307))
in (_147_1310)::_147_1309))
in (_147_1312)::_147_1311))
in (_147_1314)::_147_1313))
in (_147_1316)::_147_1315))
in (_147_1318)::_147_1317))
in (

let mk = (fun l v -> (let _147_1350 = (FStar_All.pipe_right prims (FStar_List.filter (fun _51_2122 -> (match (_51_2122) with
| (l', _51_2121) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _147_1350 (FStar_List.collect (fun _51_2126 -> (match (_51_2126) with
| (_51_2124, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _51_2132 -> (match (_51_2132) with
| (l', _51_2131) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))))
end))
end))
end))


let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.decl Prims.list = (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let yy = (("y"), (FStar_ToSMT_Term.Term_sort))
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let mk_unit = (fun _51_2138 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _147_1382 = (let _147_1373 = (let _147_1372 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in ((_147_1372), (Some ("unit typing"))))
in FStar_ToSMT_Term.Assume (_147_1373))
in (let _147_1381 = (let _147_1380 = (let _147_1379 = (let _147_1378 = (let _147_1377 = (let _147_1376 = (let _147_1375 = (let _147_1374 = (FStar_ToSMT_Term.mkEq ((x), (FStar_ToSMT_Term.mk_Term_unit)))
in ((typing_pred), (_147_1374)))
in (FStar_ToSMT_Term.mkImp _147_1375))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1376)))
in (mkForall_fuel _147_1377))
in ((_147_1378), (Some ("unit inversion"))))
in FStar_ToSMT_Term.Assume (_147_1379))
in (_147_1380)::[])
in (_147_1382)::_147_1381))))
in (

let mk_bool = (fun _51_2143 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_ToSMT_Term.Bool_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _147_1403 = (let _147_1392 = (let _147_1391 = (let _147_1390 = (let _147_1389 = (let _147_1388 = (let _147_1387 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_147_1387)))
in (FStar_ToSMT_Term.mkImp _147_1388))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1389)))
in (mkForall_fuel _147_1390))
in ((_147_1391), (Some ("bool inversion"))))
in FStar_ToSMT_Term.Assume (_147_1392))
in (let _147_1402 = (let _147_1401 = (let _147_1400 = (let _147_1399 = (let _147_1398 = (let _147_1397 = (let _147_1394 = (let _147_1393 = (FStar_ToSMT_Term.boxBool b)
in (_147_1393)::[])
in (_147_1394)::[])
in (let _147_1396 = (let _147_1395 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _147_1395 tt))
in ((_147_1397), ((bb)::[]), (_147_1396))))
in (FStar_ToSMT_Term.mkForall _147_1398))
in ((_147_1399), (Some ("bool typing"))))
in FStar_ToSMT_Term.Assume (_147_1400))
in (_147_1401)::[])
in (_147_1403)::_147_1402))))))
in (

let mk_int = (fun _51_2150 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_ToSMT_Term.Int_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let bb = (("b"), (FStar_ToSMT_Term.Int_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let precedes = (let _147_1415 = (let _147_1414 = (let _147_1413 = (let _147_1412 = (let _147_1411 = (let _147_1410 = (FStar_ToSMT_Term.boxInt a)
in (let _147_1409 = (let _147_1408 = (FStar_ToSMT_Term.boxInt b)
in (_147_1408)::[])
in (_147_1410)::_147_1409))
in (tt)::_147_1411)
in (tt)::_147_1412)
in (("Prims.Precedes"), (_147_1413)))
in (FStar_ToSMT_Term.mkApp _147_1414))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _147_1415))
in (

let precedes_y_x = (let _147_1416 = (FStar_ToSMT_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _147_1416))
in (let _147_1458 = (let _147_1422 = (let _147_1421 = (let _147_1420 = (let _147_1419 = (let _147_1418 = (let _147_1417 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_147_1417)))
in (FStar_ToSMT_Term.mkImp _147_1418))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1419)))
in (mkForall_fuel _147_1420))
in ((_147_1421), (Some ("int inversion"))))
in FStar_ToSMT_Term.Assume (_147_1422))
in (let _147_1457 = (let _147_1456 = (let _147_1430 = (let _147_1429 = (let _147_1428 = (let _147_1427 = (let _147_1424 = (let _147_1423 = (FStar_ToSMT_Term.boxInt b)
in (_147_1423)::[])
in (_147_1424)::[])
in (let _147_1426 = (let _147_1425 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _147_1425 tt))
in ((_147_1427), ((bb)::[]), (_147_1426))))
in (FStar_ToSMT_Term.mkForall _147_1428))
in ((_147_1429), (Some ("int typing"))))
in FStar_ToSMT_Term.Assume (_147_1430))
in (let _147_1455 = (let _147_1454 = (let _147_1453 = (let _147_1452 = (let _147_1451 = (let _147_1450 = (let _147_1449 = (let _147_1448 = (let _147_1447 = (let _147_1446 = (let _147_1445 = (let _147_1444 = (let _147_1433 = (let _147_1432 = (FStar_ToSMT_Term.unboxInt x)
in (let _147_1431 = (FStar_ToSMT_Term.mkInteger' (Prims.parse_int "0"))
in ((_147_1432), (_147_1431))))
in (FStar_ToSMT_Term.mkGT _147_1433))
in (let _147_1443 = (let _147_1442 = (let _147_1436 = (let _147_1435 = (FStar_ToSMT_Term.unboxInt y)
in (let _147_1434 = (FStar_ToSMT_Term.mkInteger' (Prims.parse_int "0"))
in ((_147_1435), (_147_1434))))
in (FStar_ToSMT_Term.mkGTE _147_1436))
in (let _147_1441 = (let _147_1440 = (let _147_1439 = (let _147_1438 = (FStar_ToSMT_Term.unboxInt y)
in (let _147_1437 = (FStar_ToSMT_Term.unboxInt x)
in ((_147_1438), (_147_1437))))
in (FStar_ToSMT_Term.mkLT _147_1439))
in (_147_1440)::[])
in (_147_1442)::_147_1441))
in (_147_1444)::_147_1443))
in (typing_pred_y)::_147_1445)
in (typing_pred)::_147_1446)
in (FStar_ToSMT_Term.mk_and_l _147_1447))
in ((_147_1448), (precedes_y_x)))
in (FStar_ToSMT_Term.mkImp _147_1449))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_147_1450)))
in (mkForall_fuel _147_1451))
in ((_147_1452), (Some ("well-founded ordering on nat (alt)"))))
in FStar_ToSMT_Term.Assume (_147_1453))
in (_147_1454)::[])
in (_147_1456)::_147_1455))
in (_147_1458)::_147_1457)))))))))))
in (

let mk_int_alias = (fun _51_2162 tt -> (let _147_1467 = (let _147_1466 = (let _147_1465 = (let _147_1464 = (let _147_1463 = (FStar_ToSMT_Term.mkApp ((FStar_Absyn_Const.int_lid.FStar_Ident.str), ([])))
in ((tt), (_147_1463)))
in (FStar_ToSMT_Term.mkEq _147_1464))
in ((_147_1465), (Some ("mapping to int; for now"))))
in FStar_ToSMT_Term.Assume (_147_1466))
in (_147_1467)::[]))
in (

let mk_str = (fun _51_2166 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_ToSMT_Term.String_sort))
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _147_1488 = (let _147_1477 = (let _147_1476 = (let _147_1475 = (let _147_1474 = (let _147_1473 = (let _147_1472 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in ((typing_pred), (_147_1472)))
in (FStar_ToSMT_Term.mkImp _147_1473))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_147_1474)))
in (mkForall_fuel _147_1475))
in ((_147_1476), (Some ("string inversion"))))
in FStar_ToSMT_Term.Assume (_147_1477))
in (let _147_1487 = (let _147_1486 = (let _147_1485 = (let _147_1484 = (let _147_1483 = (let _147_1482 = (let _147_1479 = (let _147_1478 = (FStar_ToSMT_Term.boxString b)
in (_147_1478)::[])
in (_147_1479)::[])
in (let _147_1481 = (let _147_1480 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _147_1480 tt))
in ((_147_1482), ((bb)::[]), (_147_1481))))
in (FStar_ToSMT_Term.mkForall _147_1483))
in ((_147_1484), (Some ("string typing"))))
in FStar_ToSMT_Term.Assume (_147_1485))
in (_147_1486)::[])
in (_147_1488)::_147_1487))))))
in (

let mk_ref = (fun reft_name _51_2174 -> (

let r = (("r"), (FStar_ToSMT_Term.Ref_sort))
in (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let refa = (let _147_1495 = (let _147_1494 = (let _147_1493 = (FStar_ToSMT_Term.mkFreeV aa)
in (_147_1493)::[])
in ((reft_name), (_147_1494)))
in (FStar_ToSMT_Term.mkApp _147_1495))
in (

let refb = (let _147_1498 = (let _147_1497 = (let _147_1496 = (FStar_ToSMT_Term.mkFreeV bb)
in (_147_1496)::[])
in ((reft_name), (_147_1497)))
in (FStar_ToSMT_Term.mkApp _147_1498))
in (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _147_1517 = (let _147_1504 = (let _147_1503 = (let _147_1502 = (let _147_1501 = (let _147_1500 = (let _147_1499 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_147_1499)))
in (FStar_ToSMT_Term.mkImp _147_1500))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_147_1501)))
in (mkForall_fuel _147_1502))
in ((_147_1503), (Some ("ref inversion"))))
in FStar_ToSMT_Term.Assume (_147_1504))
in (let _147_1516 = (let _147_1515 = (let _147_1514 = (let _147_1513 = (let _147_1512 = (let _147_1511 = (let _147_1510 = (let _147_1509 = (FStar_ToSMT_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _147_1508 = (let _147_1507 = (let _147_1506 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _147_1505 = (FStar_ToSMT_Term.mkFreeV bb)
in ((_147_1506), (_147_1505))))
in (FStar_ToSMT_Term.mkEq _147_1507))
in ((_147_1509), (_147_1508))))
in (FStar_ToSMT_Term.mkImp _147_1510))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_147_1511)))
in (mkForall_fuel' (Prims.parse_int "2") _147_1512))
in ((_147_1513), (Some ("ref typing is injective"))))
in FStar_ToSMT_Term.Assume (_147_1514))
in (_147_1515)::[])
in (_147_1517)::_147_1516))))))))))
in (

let mk_false_interp = (fun _51_2184 false_tm -> (

let valid = (FStar_ToSMT_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _147_1524 = (let _147_1523 = (let _147_1522 = (FStar_ToSMT_Term.mkIff ((FStar_ToSMT_Term.mkFalse), (valid)))
in ((_147_1522), (Some ("False interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1523))
in (_147_1524)::[])))
in (

let mk_and_interp = (fun conj _51_2190 -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1531 = (let _147_1530 = (let _147_1529 = (FStar_ToSMT_Term.mkApp ((conj), ((a)::(b)::[])))
in (_147_1529)::[])
in (("Valid"), (_147_1530)))
in (FStar_ToSMT_Term.mkApp _147_1531))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1538 = (let _147_1537 = (let _147_1536 = (let _147_1535 = (let _147_1534 = (let _147_1533 = (let _147_1532 = (FStar_ToSMT_Term.mkAnd ((valid_a), (valid_b)))
in ((_147_1532), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1533))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1534)))
in (FStar_ToSMT_Term.mkForall _147_1535))
in ((_147_1536), (Some ("/\\ interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1537))
in (_147_1538)::[])))))))))
in (

let mk_or_interp = (fun disj _51_2201 -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1545 = (let _147_1544 = (let _147_1543 = (FStar_ToSMT_Term.mkApp ((disj), ((a)::(b)::[])))
in (_147_1543)::[])
in (("Valid"), (_147_1544)))
in (FStar_ToSMT_Term.mkApp _147_1545))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1552 = (let _147_1551 = (let _147_1550 = (let _147_1549 = (let _147_1548 = (let _147_1547 = (let _147_1546 = (FStar_ToSMT_Term.mkOr ((valid_a), (valid_b)))
in ((_147_1546), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1547))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1548)))
in (FStar_ToSMT_Term.mkForall _147_1549))
in ((_147_1550), (Some ("\\/ interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1551))
in (_147_1552)::[])))))))))
in (

let mk_eq2_interp = (fun eq2 tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let yy = (("y"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let valid = (let _147_1559 = (let _147_1558 = (let _147_1557 = (FStar_ToSMT_Term.mkApp ((eq2), ((a)::(b)::(x)::(y)::[])))
in (_147_1557)::[])
in (("Valid"), (_147_1558)))
in (FStar_ToSMT_Term.mkApp _147_1559))
in (let _147_1566 = (let _147_1565 = (let _147_1564 = (let _147_1563 = (let _147_1562 = (let _147_1561 = (let _147_1560 = (FStar_ToSMT_Term.mkEq ((x), (y)))
in ((_147_1560), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1561))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_147_1562)))
in (FStar_ToSMT_Term.mkForall _147_1563))
in ((_147_1564), (Some ("Eq2 interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1565))
in (_147_1566)::[])))))))))))
in (

let mk_imp_interp = (fun imp tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1573 = (let _147_1572 = (let _147_1571 = (FStar_ToSMT_Term.mkApp ((imp), ((a)::(b)::[])))
in (_147_1571)::[])
in (("Valid"), (_147_1572)))
in (FStar_ToSMT_Term.mkApp _147_1573))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1580 = (let _147_1579 = (let _147_1578 = (let _147_1577 = (let _147_1576 = (let _147_1575 = (let _147_1574 = (FStar_ToSMT_Term.mkImp ((valid_a), (valid_b)))
in ((_147_1574), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1575))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1576)))
in (FStar_ToSMT_Term.mkForall _147_1577))
in ((_147_1578), (Some ("==> interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1579))
in (_147_1580)::[])))))))))
in (

let mk_iff_interp = (fun iff tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1587 = (let _147_1586 = (let _147_1585 = (FStar_ToSMT_Term.mkApp ((iff), ((a)::(b)::[])))
in (_147_1585)::[])
in (("Valid"), (_147_1586)))
in (FStar_ToSMT_Term.mkApp _147_1587))
in (

let valid_a = (FStar_ToSMT_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_ToSMT_Term.mkApp (("Valid"), ((b)::[])))
in (let _147_1594 = (let _147_1593 = (let _147_1592 = (let _147_1591 = (let _147_1590 = (let _147_1589 = (let _147_1588 = (FStar_ToSMT_Term.mkIff ((valid_a), (valid_b)))
in ((_147_1588), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1589))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1590)))
in (FStar_ToSMT_Term.mkForall _147_1591))
in ((_147_1592), (Some ("<==> interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1593))
in (_147_1594)::[])))))))))
in (

let mk_forall_interp = (fun for_all tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _147_1601 = (let _147_1600 = (let _147_1599 = (FStar_ToSMT_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_147_1599)::[])
in (("Valid"), (_147_1600)))
in (FStar_ToSMT_Term.mkApp _147_1601))
in (

let valid_b_x = (let _147_1604 = (let _147_1603 = (let _147_1602 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_147_1602)::[])
in (("Valid"), (_147_1603)))
in (FStar_ToSMT_Term.mkApp _147_1604))
in (let _147_1618 = (let _147_1617 = (let _147_1616 = (let _147_1615 = (let _147_1614 = (let _147_1613 = (let _147_1612 = (let _147_1611 = (let _147_1610 = (let _147_1606 = (let _147_1605 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_147_1605)::[])
in (_147_1606)::[])
in (let _147_1609 = (let _147_1608 = (let _147_1607 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in ((_147_1607), (valid_b_x)))
in (FStar_ToSMT_Term.mkImp _147_1608))
in ((_147_1610), ((xx)::[]), (_147_1609))))
in (FStar_ToSMT_Term.mkForall _147_1611))
in ((_147_1612), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1613))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1614)))
in (FStar_ToSMT_Term.mkForall _147_1615))
in ((_147_1616), (Some ("forall interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1617))
in (_147_1618)::[]))))))))))
in (

let mk_exists_interp = (fun for_all tt -> (

let aa = (("a"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("b"), (FStar_ToSMT_Term.Type_sort))
in (

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _147_1625 = (let _147_1624 = (let _147_1623 = (FStar_ToSMT_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_147_1623)::[])
in (("Valid"), (_147_1624)))
in (FStar_ToSMT_Term.mkApp _147_1625))
in (

let valid_b_x = (let _147_1628 = (let _147_1627 = (let _147_1626 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_147_1626)::[])
in (("Valid"), (_147_1627)))
in (FStar_ToSMT_Term.mkApp _147_1628))
in (let _147_1642 = (let _147_1641 = (let _147_1640 = (let _147_1639 = (let _147_1638 = (let _147_1637 = (let _147_1636 = (let _147_1635 = (let _147_1634 = (let _147_1630 = (let _147_1629 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_147_1629)::[])
in (_147_1630)::[])
in (let _147_1633 = (let _147_1632 = (let _147_1631 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in ((_147_1631), (valid_b_x)))
in (FStar_ToSMT_Term.mkImp _147_1632))
in ((_147_1634), ((xx)::[]), (_147_1633))))
in (FStar_ToSMT_Term.mkExists _147_1635))
in ((_147_1636), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1637))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_147_1638)))
in (FStar_ToSMT_Term.mkForall _147_1639))
in ((_147_1640), (Some ("exists interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1641))
in (_147_1642)::[]))))))))))
in (

let mk_foralltyp_interp = (fun for_all tt -> (

let kk = (("k"), (FStar_ToSMT_Term.Kind_sort))
in (

let aa = (("aa"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("bb"), (FStar_ToSMT_Term.Term_sort))
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1649 = (let _147_1648 = (let _147_1647 = (FStar_ToSMT_Term.mkApp ((for_all), ((k)::(a)::[])))
in (_147_1647)::[])
in (("Valid"), (_147_1648)))
in (FStar_ToSMT_Term.mkApp _147_1649))
in (

let valid_a_b = (let _147_1652 = (let _147_1651 = (let _147_1650 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_147_1650)::[])
in (("Valid"), (_147_1651)))
in (FStar_ToSMT_Term.mkApp _147_1652))
in (let _147_1666 = (let _147_1665 = (let _147_1664 = (let _147_1663 = (let _147_1662 = (let _147_1661 = (let _147_1660 = (let _147_1659 = (let _147_1658 = (let _147_1654 = (let _147_1653 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_147_1653)::[])
in (_147_1654)::[])
in (let _147_1657 = (let _147_1656 = (let _147_1655 = (FStar_ToSMT_Term.mk_HasKind b k)
in ((_147_1655), (valid_a_b)))
in (FStar_ToSMT_Term.mkImp _147_1656))
in ((_147_1658), ((bb)::[]), (_147_1657))))
in (FStar_ToSMT_Term.mkForall _147_1659))
in ((_147_1660), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1661))
in ((((valid)::[])::[]), ((kk)::(aa)::[]), (_147_1662)))
in (FStar_ToSMT_Term.mkForall _147_1663))
in ((_147_1664), (Some ("ForallTyp interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1665))
in (_147_1666)::[]))))))))))
in (

let mk_existstyp_interp = (fun for_some tt -> (

let kk = (("k"), (FStar_ToSMT_Term.Kind_sort))
in (

let aa = (("aa"), (FStar_ToSMT_Term.Type_sort))
in (

let bb = (("bb"), (FStar_ToSMT_Term.Term_sort))
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _147_1673 = (let _147_1672 = (let _147_1671 = (FStar_ToSMT_Term.mkApp ((for_some), ((k)::(a)::[])))
in (_147_1671)::[])
in (("Valid"), (_147_1672)))
in (FStar_ToSMT_Term.mkApp _147_1673))
in (

let valid_a_b = (let _147_1676 = (let _147_1675 = (let _147_1674 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_147_1674)::[])
in (("Valid"), (_147_1675)))
in (FStar_ToSMT_Term.mkApp _147_1676))
in (let _147_1690 = (let _147_1689 = (let _147_1688 = (let _147_1687 = (let _147_1686 = (let _147_1685 = (let _147_1684 = (let _147_1683 = (let _147_1682 = (let _147_1678 = (let _147_1677 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_147_1677)::[])
in (_147_1678)::[])
in (let _147_1681 = (let _147_1680 = (let _147_1679 = (FStar_ToSMT_Term.mk_HasKind b k)
in ((_147_1679), (valid_a_b)))
in (FStar_ToSMT_Term.mkImp _147_1680))
in ((_147_1682), ((bb)::[]), (_147_1681))))
in (FStar_ToSMT_Term.mkExists _147_1683))
in ((_147_1684), (valid)))
in (FStar_ToSMT_Term.mkIff _147_1685))
in ((((valid)::[])::[]), ((kk)::(aa)::[]), (_147_1686)))
in (FStar_ToSMT_Term.mkForall _147_1687))
in ((_147_1688), (Some ("ExistsTyp interpretation"))))
in FStar_ToSMT_Term.Assume (_147_1689))
in (_147_1690)::[]))))))))))
in (

let prims = (((FStar_Absyn_Const.unit_lid), (mk_unit)))::(((FStar_Absyn_Const.bool_lid), (mk_bool)))::(((FStar_Absyn_Const.int_lid), (mk_int)))::(((FStar_Absyn_Const.string_lid), (mk_str)))::(((FStar_Absyn_Const.ref_lid), (mk_ref)))::(((FStar_Absyn_Const.false_lid), (mk_false_interp)))::(((FStar_Absyn_Const.and_lid), (mk_and_interp)))::(((FStar_Absyn_Const.or_lid), (mk_or_interp)))::(((FStar_Absyn_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Absyn_Const.imp_lid), (mk_imp_interp)))::(((FStar_Absyn_Const.iff_lid), (mk_iff_interp)))::(((FStar_Absyn_Const.forall_lid), (mk_forall_interp)))::(((FStar_Absyn_Const.exists_lid), (mk_exists_interp)))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _51_2294 -> (match (_51_2294) with
| (l, _51_2293) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_51_2297, f) -> begin
(f s tt)
end)))))))))))))))))))))))


let rec encode_sigelt : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let _51_2303 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _147_1821 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _147_1821))
end else begin
()
end
in (

let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let _51_2311 = (encode_sigelt' env se)
in (match (_51_2311) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _147_1824 = (let _147_1823 = (let _147_1822 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_147_1822))
in (_147_1823)::[])
in ((_147_1824), (e)))
end
| _51_2314 -> begin
(let _147_1831 = (let _147_1830 = (let _147_1826 = (let _147_1825 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_147_1825))
in (_147_1826)::g)
in (let _147_1829 = (let _147_1828 = (let _147_1827 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_147_1827))
in (_147_1828)::[])
in (FStar_List.append _147_1830 _147_1829)))
in ((_147_1831), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Ident.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Ident.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.all_")))
in (

let encode_top_level_val = (fun env lid t quals -> (

let tt = (whnf env t)
in (

let _51_2327 = (encode_free_var env lid t tt quals)
in (match (_51_2327) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _147_1845 = (let _147_1844 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _147_1844))
in ((_147_1845), (env)))
end else begin
((decls), (env))
end
end))))
in (

let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _51_2334 lb -> (match (_51_2334) with
| (decls, env) -> begin
(

let _51_2338 = (let _147_1854 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _147_1854 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_51_2338) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_51_2340, _51_2342, _51_2344, _51_2346, (FStar_Absyn_Syntax.Effect)::[], _51_2350) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _51_2355, _51_2357, _51_2359, _51_2361, _51_2363) when (should_skip lid) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _51_2368, _51_2370, _51_2372, _51_2374, _51_2376) when (FStar_Ident.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(

let _51_2382 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_51_2382) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_ToSMT_Term.Term_sort))
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _147_1857 = (let _147_1856 = (let _147_1855 = (FStar_ToSMT_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_147_1855)::[])
in (("Valid"), (_147_1856)))
in (FStar_ToSMT_Term.mkApp _147_1857))
in (

let decls = (let _147_1865 = (let _147_1864 = (let _147_1863 = (let _147_1862 = (let _147_1861 = (let _147_1860 = (let _147_1859 = (let _147_1858 = (FStar_ToSMT_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_147_1858)))
in (FStar_ToSMT_Term.mkEq _147_1859))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_147_1860)))
in (FStar_ToSMT_Term.mkForall _147_1861))
in ((_147_1862), (Some ("b2t def"))))
in FStar_ToSMT_Term.Assume (_147_1863))
in (_147_1864)::[])
in (FStar_ToSMT_Term.DeclFun (((tname), ((FStar_ToSMT_Term.Term_sort)::[]), (FStar_ToSMT_Term.Type_sort), (None))))::_147_1865)
in ((decls), (env))))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _51_2390, t, tags, _51_2394) -> begin
(

let _51_2400 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_51_2400) with
| (tname, ttok, env) -> begin
(

let _51_2409 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
(((FStar_List.append tps tps')), (body))
end
| _51_2406 -> begin
((tps), (t))
end)
in (match (_51_2409) with
| (tps, t) -> begin
(

let _51_2416 = (encode_binders None tps env)
in (match (_51_2416) with
| (vars, guards, env', binder_decls, _51_2415) -> begin
(

let tok_app = (let _147_1866 = (FStar_ToSMT_Term.mkApp ((ttok), ([])))
in (mk_ApplyT _147_1866 vars))
in (

let tok_decl = FStar_ToSMT_Term.DeclFun (((ttok), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (

let app = (let _147_1868 = (let _147_1867 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((tname), (_147_1867)))
in (FStar_ToSMT_Term.mkApp _147_1868))
in (

let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _51_2422 -> begin
(let _147_1870 = (let _147_1869 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ttok), (FStar_ToSMT_Term.Type_sort)) _147_1869))
in (_147_1870)::[])
end)
in (

let decls = (let _147_1881 = (let _147_1873 = (let _147_1872 = (let _147_1871 = (FStar_List.map Prims.snd vars)
in ((tname), (_147_1871), (FStar_ToSMT_Term.Type_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_1872))
in (_147_1873)::(tok_decl)::[])
in (let _147_1880 = (let _147_1879 = (let _147_1878 = (let _147_1877 = (let _147_1876 = (let _147_1875 = (let _147_1874 = (FStar_ToSMT_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (vars), (_147_1874)))
in (FStar_ToSMT_Term.mkForall _147_1875))
in ((_147_1876), (Some ("name-token correspondence"))))
in FStar_ToSMT_Term.Assume (_147_1877))
in (_147_1878)::[])
in (FStar_List.append fresh_tok _147_1879))
in (FStar_List.append _147_1881 _147_1880)))
in (

let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (

let _51_2434 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _51_19 -> (match (_51_19) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _51_2429 -> begin
false
end)))) then begin
(let _147_1884 = (FStar_ToSMT_Term.mk_Valid app)
in (let _147_1883 = (encode_formula t env')
in ((_147_1884), (_147_1883))))
end else begin
(let _147_1885 = (encode_typ_term t env')
in ((app), (_147_1885)))
end
in (match (_51_2434) with
| (def, (body, decls1)) -> begin
(

let abbrev_def = (let _147_1892 = (let _147_1891 = (let _147_1890 = (let _147_1889 = (let _147_1888 = (let _147_1887 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_1886 = (FStar_ToSMT_Term.mkEq ((def), (body)))
in ((_147_1887), (_147_1886))))
in (FStar_ToSMT_Term.mkImp _147_1888))
in ((((def)::[])::[]), (vars), (_147_1889)))
in (FStar_ToSMT_Term.mkForall _147_1890))
in ((_147_1891), (Some ("abbrev. elimination"))))
in FStar_ToSMT_Term.Assume (_147_1892))
in (

let kindingAx = (

let _51_2438 = (let _147_1893 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _147_1893 env' app))
in (match (_51_2438) with
| (k, decls) -> begin
(let _147_1901 = (let _147_1900 = (let _147_1899 = (let _147_1898 = (let _147_1897 = (let _147_1896 = (let _147_1895 = (let _147_1894 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_1894), (k)))
in (FStar_ToSMT_Term.mkImp _147_1895))
in ((((app)::[])::[]), (vars), (_147_1896)))
in (FStar_ToSMT_Term.mkForall _147_1897))
in ((_147_1898), (Some ("abbrev. kinding"))))
in FStar_ToSMT_Term.Assume (_147_1899))
in (_147_1900)::[])
in (FStar_List.append decls _147_1901))
end))
in (

let g = (let _147_1905 = (let _147_1904 = (let _147_1903 = (let _147_1902 = (primitive_type_axioms lid tname app)
in (FStar_List.append ((abbrev_def)::kindingAx) _147_1902))
in (FStar_List.append decls1 _147_1903))
in (FStar_List.append decls _147_1904))
in (FStar_List.append binder_decls _147_1905))
in ((g), (env)))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _51_2445) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
(([]), (env))
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _51_2451, _51_2453) -> begin
(

let _51_2458 = (encode_formula f env)
in (match (_51_2458) with
| (f, decls) -> begin
(

let g = (let _147_1910 = (let _147_1909 = (let _147_1908 = (let _147_1907 = (let _147_1906 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _147_1906))
in Some (_147_1907))
in ((f), (_147_1908)))
in FStar_ToSMT_Term.Assume (_147_1909))
in (_147_1910)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _51_2464, datas, quals, _51_2468) when (FStar_Ident.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(

let _51_2474 = (new_typ_constant_and_tok_from_lid env t)
in (match (_51_2474) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _51_2477, _51_2479, _51_2481, _51_2483, _51_2485, _51_2487) when ((FStar_Ident.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Ident.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(

let tname = t.FStar_Ident.str
in (

let tsym = (FStar_ToSMT_Term.mkFreeV ((tname), (FStar_ToSMT_Term.Type_sort)))
in (

let decl = FStar_ToSMT_Term.DeclFun (((tname), ([]), (FStar_ToSMT_Term.Type_sort), (None)))
in (let _147_1912 = (let _147_1911 = (primitive_type_axioms t tname tsym)
in (decl)::_147_1911)
in ((_147_1912), ((push_free_tvar env t tname (Some (tsym)))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _51_2497, datas, quals, _51_2501) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_20 -> (match (_51_20) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _51_2508 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _51_2518 = c
in (match (_51_2518) with
| (name, args, _51_2515, _51_2517) -> begin
(let _147_1918 = (let _147_1917 = (let _147_1916 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_147_1916), (FStar_ToSMT_Term.Type_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_1917))
in (_147_1918)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = (Prims.parse_int "0")) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _147_1924 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _147_1924 FStar_Option.isNone)))))) then begin
[]
end else begin
(

let _51_2525 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_51_2525) with
| (xxsym, xx) -> begin
(

let _51_2568 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _51_2528 l -> (match (_51_2528) with
| (out, decls) -> begin
(

let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (

let _51_2538 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
((formals), ((FStar_Absyn_Util.comp_result res)))
end
| None -> begin
(([]), (data_t))
end)
in (match (_51_2538) with
| (args, res) -> begin
(

let indices = (match ((let _147_1927 = (FStar_Absyn_Util.compress_typ res)
in _147_1927.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_51_2540, indices) -> begin
indices
end
| _51_2545 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _147_1932 = (let _147_1931 = (let _147_1930 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in ((_147_1930), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _147_1931))
in (push_typ_var env a.FStar_Absyn_Syntax.v _147_1932))
end
| FStar_Util.Inr (x) -> begin
(let _147_1935 = (let _147_1934 = (let _147_1933 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in ((_147_1933), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _147_1934))
in (push_term_var env x.FStar_Absyn_Syntax.v _147_1935))
end)) env))
in (

let _51_2556 = (encode_args indices env)
in (match (_51_2556) with
| (indices, decls') -> begin
(

let _51_2557 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _147_1942 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _147_1939 = (let _147_1938 = (FStar_ToSMT_Term.mkFreeV v)
in ((_147_1938), (a)))
in (FStar_ToSMT_Term.mkEq _147_1939))
end
| FStar_Util.Inr (a) -> begin
(let _147_1941 = (let _147_1940 = (FStar_ToSMT_Term.mkFreeV v)
in ((_147_1940), (a)))
in (FStar_ToSMT_Term.mkEq _147_1941))
end)) vars indices)
in (FStar_All.pipe_right _147_1942 FStar_ToSMT_Term.mk_and_l))
in (let _147_1947 = (let _147_1946 = (let _147_1945 = (let _147_1944 = (let _147_1943 = (mk_data_tester env l xx)
in ((_147_1943), (eqs)))
in (FStar_ToSMT_Term.mkAnd _147_1944))
in ((out), (_147_1945)))
in (FStar_ToSMT_Term.mkOr _147_1946))
in ((_147_1947), ((FStar_List.append decls decls'))))))
end))))
end)))
end)) ((FStar_ToSMT_Term.mkFalse), ([]))))
in (match (_51_2568) with
| (data_ax, decls) -> begin
(

let _51_2571 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_51_2571) with
| (ffsym, ff) -> begin
(

let xx_has_type = (let _147_1948 = (FStar_ToSMT_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_ToSMT_Term.mk_HasTypeFuel _147_1948 xx tapp))
in (let _147_1955 = (let _147_1954 = (let _147_1953 = (let _147_1952 = (let _147_1951 = (let _147_1950 = (add_fuel ((ffsym), (FStar_ToSMT_Term.Fuel_sort)) ((((xxsym), (FStar_ToSMT_Term.Term_sort)))::vars))
in (let _147_1949 = (FStar_ToSMT_Term.mkImp ((xx_has_type), (data_ax)))
in ((((xx_has_type)::[])::[]), (_147_1950), (_147_1949))))
in (FStar_ToSMT_Term.mkForall _147_1951))
in ((_147_1952), (Some ("inversion axiom"))))
in FStar_ToSMT_Term.Assume (_147_1953))
in (_147_1954)::[])
in (FStar_List.append decls _147_1955)))
end))
end))
end))
end)
in (

let k = (FStar_Absyn_Util.close_kind tps k)
in (

let _51_2583 = (match ((let _147_1956 = (FStar_Absyn_Util.compress_kind k)
in _147_1956.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
((true), (bs), (res))
end
| _51_2579 -> begin
((false), ([]), (k))
end)
in (match (_51_2583) with
| (is_kind_arrow, formals, res) -> begin
(

let _51_2590 = (encode_binders None formals env)
in (match (_51_2590) with
| (vars, guards, env', binder_decls, _51_2589) -> begin
(

let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _51_21 -> (match (_51_21) with
| FStar_Absyn_Syntax.Projector (_51_2596) -> begin
true
end
| _51_2599 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(

let rec projectee = (fun i _51_22 -> (match (_51_22) with
| [] -> begin
i
end
| (f)::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_51_2614) -> begin
(projectee (i + (Prims.parse_int "1")) tl)
end
| FStar_Util.Inr (x) -> begin
if (x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "projectee") then begin
i
end else begin
(projectee (i + (Prims.parse_int "1")) tl)
end
end)
end))
in (

let projectee_pos = (projectee (Prims.parse_int "0") formals)
in (

let _51_2629 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_51_2620, (xx)::suffix) -> begin
((xx), (suffix))
end
| _51_2626 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_51_2629) with
| (xx, suffix) -> begin
(

let dproj_app = (let _147_1970 = (let _147_1969 = (let _147_1968 = (mk_typ_projector_name d a)
in (let _147_1967 = (let _147_1966 = (FStar_ToSMT_Term.mkFreeV xx)
in (_147_1966)::[])
in ((_147_1968), (_147_1967))))
in (FStar_ToSMT_Term.mkApp _147_1969))
in (mk_ApplyT _147_1970 suffix))
in (let _147_1975 = (let _147_1974 = (let _147_1973 = (let _147_1972 = (let _147_1971 = (FStar_ToSMT_Term.mkEq ((tapp), (dproj_app)))
in ((((tapp)::[])::[]), (vars), (_147_1971)))
in (FStar_ToSMT_Term.mkForall _147_1972))
in ((_147_1973), (Some ("projector axiom"))))
in FStar_ToSMT_Term.Assume (_147_1974))
in (_147_1975)::[]))
end))))
end
| _51_2632 -> begin
[]
end))
in (

let pretype_axioms = (fun tapp vars -> (

let _51_2638 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_51_2638) with
| (xxsym, xx) -> begin
(

let _51_2641 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_51_2641) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _147_1988 = (let _147_1987 = (let _147_1986 = (let _147_1985 = (let _147_1984 = (let _147_1983 = (let _147_1982 = (let _147_1981 = (let _147_1980 = (FStar_ToSMT_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_147_1980)))
in (FStar_ToSMT_Term.mkEq _147_1981))
in ((xx_has_type), (_147_1982)))
in (FStar_ToSMT_Term.mkImp _147_1983))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_ToSMT_Term.Term_sort)))::(((ffsym), (FStar_ToSMT_Term.Fuel_sort)))::vars), (_147_1984)))
in (FStar_ToSMT_Term.mkForall _147_1985))
in ((_147_1986), (Some ("pretyping"))))
in FStar_ToSMT_Term.Assume (_147_1987))
in (_147_1988)::[]))
end))
end)))
in (

let _51_2646 = (new_typ_constant_and_tok_from_lid env t)
in (match (_51_2646) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_ToSMT_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let tapp = (let _147_1990 = (let _147_1989 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((tname), (_147_1989)))
in (FStar_ToSMT_Term.mkApp _147_1990))
in (

let _51_2667 = (

let tname_decl = (let _147_1994 = (let _147_1993 = (FStar_All.pipe_right vars (FStar_List.map (fun _51_2652 -> (match (_51_2652) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _147_1992 = (varops.next_id ())
in ((tname), (_147_1993), (FStar_ToSMT_Term.Type_sort), (_147_1992))))
in (constructor_or_logic_type_decl _147_1994))
in (

let _51_2664 = (match (vars) with
| [] -> begin
(let _147_1998 = (let _147_1997 = (let _147_1996 = (FStar_ToSMT_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _147_1995 -> Some (_147_1995)) _147_1996))
in (push_free_tvar env t tname _147_1997))
in (([]), (_147_1998)))
end
| _51_2656 -> begin
(

let ttok_decl = FStar_ToSMT_Term.DeclFun (((ttok), ([]), (FStar_ToSMT_Term.Type_sort), (Some ("token"))))
in (

let ttok_fresh = (let _147_1999 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ttok), (FStar_ToSMT_Term.Type_sort)) _147_1999))
in (

let ttok_app = (mk_ApplyT ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _147_2003 = (let _147_2002 = (let _147_2001 = (let _147_2000 = (FStar_ToSMT_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_147_2000)))
in (FStar_ToSMT_Term.mkForall' _147_2001))
in ((_147_2002), (Some ("name-token correspondence"))))
in FStar_ToSMT_Term.Assume (_147_2003))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_51_2664) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_51_2667) with
| (decls, env) -> begin
(

let kindingAx = (

let _51_2670 = (encode_knd res env' tapp)
in (match (_51_2670) with
| (k, decls) -> begin
(

let karr = if is_kind_arrow then begin
(let _147_2007 = (let _147_2006 = (let _147_2005 = (let _147_2004 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _147_2004))
in ((_147_2005), (Some ("kinding"))))
in FStar_ToSMT_Term.Assume (_147_2006))
in (_147_2007)::[])
end else begin
[]
end
in (let _147_2014 = (let _147_2013 = (let _147_2012 = (let _147_2011 = (let _147_2010 = (let _147_2009 = (let _147_2008 = (FStar_ToSMT_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_147_2008)))
in (FStar_ToSMT_Term.mkForall _147_2009))
in ((_147_2010), (Some ("kinding"))))
in FStar_ToSMT_Term.Assume (_147_2011))
in (_147_2012)::[])
in (FStar_List.append karr _147_2013))
in (FStar_List.append decls _147_2014)))
end))
in (

let aux = if is_logical then begin
(let _147_2015 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _147_2015))
end else begin
(let _147_2022 = (let _147_2021 = (primitive_type_axioms t tname tapp)
in (let _147_2020 = (let _147_2019 = (inversion_axioms tapp vars)
in (let _147_2018 = (let _147_2017 = (projection_axioms tapp vars)
in (let _147_2016 = (pretype_axioms tapp vars)
in (FStar_List.append _147_2017 _147_2016)))
in (FStar_List.append _147_2019 _147_2018)))
in (FStar_List.append _147_2021 _147_2020)))
in (FStar_List.append kindingAx _147_2022))
end
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _51_2677, _51_2679, _51_2681, _51_2683, _51_2685) when (FStar_Ident.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_51_2691, tps, _51_2694), quals, _51_2698, drange) -> begin
(

let t = (let _147_2024 = (FStar_List.map (fun _51_2705 -> (match (_51_2705) with
| (x, _51_2704) -> begin
((x), (Some (FStar_Absyn_Syntax.Implicit (true))))
end)) tps)
in (FStar_Absyn_Util.close_typ _147_2024 t))
in (

let _51_2710 = (new_term_constant_and_tok_from_lid env d)
in (match (_51_2710) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_ToSMT_Term.mkApp ((ddtok), ([])))
in (

let _51_2719 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
((f), ((FStar_Absyn_Util.comp_result c)))
end
| None -> begin
(([]), (t))
end)
in (match (_51_2719) with
| (formals, t_res) -> begin
(

let _51_2722 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_51_2722) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_ToSMT_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _51_2729 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_51_2729) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _51_23 -> (match (_51_23) with
| FStar_Util.Inl (a) -> begin
(let _147_2026 = (mk_typ_projector_name d a)
in ((_147_2026), (FStar_ToSMT_Term.Type_sort)))
end
| FStar_Util.Inr (x) -> begin
(let _147_2027 = (mk_term_projector_name d x)
in ((_147_2027), (FStar_ToSMT_Term.Term_sort)))
end))))
in (

let datacons = (let _147_2029 = (let _147_2028 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_ToSMT_Term.Term_sort), (_147_2028)))
in (FStar_All.pipe_right _147_2029 FStar_ToSMT_Term.constructor_to_decl))
in (

let app = (mk_ApplyE ddtok_tm vars)
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _51_2743 = (encode_typ_pred None t env ddtok_tm)
in (match (_51_2743) with
| (tok_typing, decls3) -> begin
(

let _51_2750 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_51_2750) with
| (vars', guards', env'', decls_formals, _51_2749) -> begin
(

let _51_2755 = (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_51_2755) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _51_2759 -> begin
(let _147_2031 = (let _147_2030 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((ddtok), (FStar_ToSMT_Term.Term_sort)) _147_2030))
in (_147_2031)::[])
end)
in (

let encode_elim = (fun _51_2762 -> (match (()) with
| () -> begin
(

let _51_2765 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_51_2765) with
| (head, args) -> begin
(match ((let _147_2034 = (FStar_Absyn_Util.compress_typ head)
in _147_2034.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let encoded_head = (lookup_free_tvar_name env' fv)
in (

let _51_2771 = (encode_args args env')
in (match (_51_2771) with
| (encoded_args, arg_decls) -> begin
(

let _51_2795 = (FStar_List.fold_left (fun _51_2775 arg -> (match (_51_2775) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(

let _51_2783 = (let _147_2037 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _147_2037))
in (match (_51_2783) with
| (_51_2780, tv, env) -> begin
(let _147_2039 = (let _147_2038 = (FStar_ToSMT_Term.mkEq ((targ), (tv)))
in (_147_2038)::eqns)
in ((env), ((tv)::arg_vars), (_147_2039)))
end))
end
| FStar_Util.Inr (varg) -> begin
(

let _51_2790 = (let _147_2040 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _147_2040))
in (match (_51_2790) with
| (_51_2787, xv, env) -> begin
(let _147_2042 = (let _147_2041 = (FStar_ToSMT_Term.mkEq ((varg), (xv)))
in (_147_2041)::eqns)
in ((env), ((xv)::arg_vars), (_147_2042)))
end))
end)
end)) ((env'), ([]), ([])) encoded_args)
in (match (_51_2795) with
| (_51_2792, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_ToSMT_Term.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _147_2049 = (let _147_2048 = (let _147_2047 = (let _147_2046 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _147_2045 = (let _147_2044 = (let _147_2043 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_147_2043)))
in (FStar_ToSMT_Term.mkImp _147_2044))
in ((((ty_pred)::[])::[]), (_147_2046), (_147_2045))))
in (FStar_ToSMT_Term.mkForall _147_2047))
in ((_147_2048), (Some ("data constructor typing elim"))))
in FStar_ToSMT_Term.Assume (_147_2049))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(

let x = (let _147_2050 = (varops.fresh "x")
in ((_147_2050), (FStar_ToSMT_Term.Term_sort)))
in (

let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _147_2060 = (let _147_2059 = (let _147_2058 = (let _147_2057 = (let _147_2052 = (let _147_2051 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_147_2051)::[])
in (_147_2052)::[])
in (let _147_2056 = (let _147_2055 = (let _147_2054 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _147_2053 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in ((_147_2054), (_147_2053))))
in (FStar_ToSMT_Term.mkImp _147_2055))
in ((_147_2057), ((x)::[]), (_147_2056))))
in (FStar_ToSMT_Term.mkForall _147_2058))
in ((_147_2059), (Some ("lextop is top"))))
in FStar_ToSMT_Term.Assume (_147_2060))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _147_2063 = (let _147_2062 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _147_2062 dapp))
in (_147_2063)::[])
end
| _51_2810 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _147_2070 = (let _147_2069 = (let _147_2068 = (let _147_2067 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _147_2066 = (let _147_2065 = (let _147_2064 = (FStar_ToSMT_Term.mk_and_l prec)
in ((ty_pred), (_147_2064)))
in (FStar_ToSMT_Term.mkImp _147_2065))
in ((((ty_pred)::[])::[]), (_147_2067), (_147_2066))))
in (FStar_ToSMT_Term.mkForall _147_2068))
in ((_147_2069), (Some ("subterm ordering"))))
in FStar_ToSMT_Term.Assume (_147_2070)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _51_2814 -> begin
(

let _51_2815 = (let _147_2073 = (let _147_2072 = (FStar_Absyn_Print.sli d)
in (let _147_2071 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _147_2072 _147_2071)))
in (FStar_Tc_Errors.warn drange _147_2073))
in (([]), ([])))
end)
end))
end))
in (

let _51_2819 = (encode_elim ())
in (match (_51_2819) with
| (decls2, elim) -> begin
(

let g = (let _147_2100 = (let _147_2099 = (let _147_2098 = (let _147_2097 = (let _147_2078 = (let _147_2077 = (let _147_2076 = (let _147_2075 = (let _147_2074 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _147_2074))
in Some (_147_2075))
in ((ddtok), ([]), (FStar_ToSMT_Term.Term_sort), (_147_2076)))
in FStar_ToSMT_Term.DeclFun (_147_2077))
in (_147_2078)::[])
in (let _147_2096 = (let _147_2095 = (let _147_2094 = (let _147_2093 = (let _147_2092 = (let _147_2091 = (let _147_2090 = (let _147_2082 = (let _147_2081 = (let _147_2080 = (let _147_2079 = (FStar_ToSMT_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_147_2079)))
in (FStar_ToSMT_Term.mkForall _147_2080))
in ((_147_2081), (Some ("equality for proxy"))))
in FStar_ToSMT_Term.Assume (_147_2082))
in (let _147_2089 = (let _147_2088 = (let _147_2087 = (let _147_2086 = (let _147_2085 = (let _147_2084 = (add_fuel ((fuel_var), (FStar_ToSMT_Term.Fuel_sort)) vars')
in (let _147_2083 = (FStar_ToSMT_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_147_2084), (_147_2083))))
in (FStar_ToSMT_Term.mkForall _147_2085))
in ((_147_2086), (Some ("data constructor typing intro"))))
in FStar_ToSMT_Term.Assume (_147_2087))
in (_147_2088)::[])
in (_147_2090)::_147_2089))
in (FStar_ToSMT_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")))))::_147_2091)
in (FStar_List.append _147_2092 elim))
in (FStar_List.append decls_pred _147_2093))
in (FStar_List.append decls_formals _147_2094))
in (FStar_List.append proxy_fresh _147_2095))
in (FStar_List.append _147_2097 _147_2096)))
in (FStar_List.append decls3 _147_2098))
in (FStar_List.append decls2 _147_2099))
in (FStar_List.append binder_decls _147_2100))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end)))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _51_2823, _51_2825, _51_2827) -> begin
(

let _51_2832 = (encode_signature env ses)
in (match (_51_2832) with
| (g, env) -> begin
(

let _51_2844 = (FStar_All.pipe_right g (FStar_List.partition (fun _51_24 -> (match (_51_24) with
| FStar_ToSMT_Term.Assume (_51_2835, Some ("inversion axiom")) -> begin
false
end
| _51_2841 -> begin
true
end))))
in (match (_51_2844) with
| (g', inversions) -> begin
(

let _51_2853 = (FStar_All.pipe_right g' (FStar_List.partition (fun _51_25 -> (match (_51_25) with
| FStar_ToSMT_Term.DeclFun (_51_2847) -> begin
true
end
| _51_2850 -> begin
false
end))))
in (match (_51_2853) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_51_2855, _51_2857, _51_2859, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_26 -> (match (_51_26) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _51_2871 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _51_2876, _51_2878, quals) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _51_2890 = (FStar_Util.first_N nbinders formals)
in (match (_51_2890) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun formal binder -> (match ((((Prims.fst formal)), ((Prims.fst binder)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _147_2115 = (let _147_2114 = (FStar_Absyn_Util.btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_147_2114)))
in FStar_Util.Inl (_147_2115))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _147_2117 = (let _147_2116 = (FStar_Absyn_Util.bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_147_2116)))
in FStar_Util.Inr (_147_2117))
end
| _51_2904 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (

let extra_formals = (let _147_2118 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _147_2118 FStar_Absyn_Util.name_binders))
in (

let body = (let _147_2124 = (let _147_2120 = (let _147_2119 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _147_2119))
in ((body), (_147_2120)))
in (let _147_2123 = (let _147_2122 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _147_2121 -> Some (_147_2121)) _147_2122))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _147_2124 _147_2123 body.FStar_Absyn_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c)) then begin
(

let _51_2942 = (FStar_Util.first_N nformals binders)
in (match (_51_2942) with
| (bs0, rest) -> begin
(

let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _51_2946 -> begin
(FStar_All.failwith "impossible")
end)
in (

let body = (FStar_Absyn_Syntax.mk_Exp_abs ((rest), (body)) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in ((bs0), (body), (bs0), (tres))))
end))
end else begin
if (nformals > nbinders) then begin
(

let _51_2951 = (eta_expand binders formals body tres)
in (match (_51_2951) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end
| _51_2953 -> begin
(let _147_2133 = (let _147_2132 = (FStar_Absyn_Print.exp_to_string e)
in (let _147_2131 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _147_2132 _147_2131)))
in (FStar_All.failwith _147_2133))
end)
end
| _51_2955 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(

let tres = (FStar_Absyn_Util.comp_result c)
in (

let _51_2963 = (eta_expand [] formals e tres)
in (match (_51_2963) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end
| _51_2965 -> begin
(([]), (e), ([]), (t_norm))
end)
end))
in try
(match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_27 -> (match (_51_27) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _51_2978 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(

let _51_2997 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _51_2984 lb -> (match (_51_2984) with
| (toks, typs, decls, env) -> begin
(

let _51_2986 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (let _147_2139 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _147_2139 FStar_Absyn_Util.compress_typ))
in (

let _51_2992 = (let _147_2140 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _147_2140 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_51_2992) with
| (tok, decl, env) -> begin
(let _147_2143 = (let _147_2142 = (let _147_2141 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in ((_147_2141), (tok)))
in (_147_2142)::toks)
in ((_147_2143), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_51_2997) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_28 -> (match (_51_28) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _51_3004 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _147_2146 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _147_2146))))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Absyn_Syntax.lbname = _51_3012; FStar_Absyn_Syntax.lbtyp = _51_3010; FStar_Absyn_Syntax.lbeff = _51_3008; FStar_Absyn_Syntax.lbdef = e})::[], (t_norm)::[], ((flid, (f, ftok)))::[]) -> begin
(

let _51_3028 = (destruct_bound_function flid t_norm e)
in (match (_51_3028) with
| (binders, body, formals, tres) -> begin
(

let _51_3035 = (encode_binders None binders env)
in (match (_51_3035) with
| (vars, guards, env', binder_decls, _51_3034) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV ((f), (FStar_ToSMT_Term.Term_sort)))
end
| _51_3038 -> begin
(let _147_2148 = (let _147_2147 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((f), (_147_2147)))
in (FStar_ToSMT_Term.mkApp _147_2148))
end)
in (

let _51_3042 = (encode_exp body env')
in (match (_51_3042) with
| (body, decls2) -> begin
(

let eqn = (let _147_2157 = (let _147_2156 = (let _147_2153 = (let _147_2152 = (let _147_2151 = (let _147_2150 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_2149 = (FStar_ToSMT_Term.mkEq ((app), (body)))
in ((_147_2150), (_147_2149))))
in (FStar_ToSMT_Term.mkImp _147_2151))
in ((((app)::[])::[]), (vars), (_147_2152)))
in (FStar_ToSMT_Term.mkForall _147_2153))
in (let _147_2155 = (let _147_2154 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_147_2154))
in ((_147_2156), (_147_2155))))
in FStar_ToSMT_Term.Assume (_147_2157))
in (((FStar_List.append decls (FStar_List.append binder_decls (FStar_List.append decls2 ((eqn)::[]))))), (env)))
end)))
end))
end))
end
| _51_3045 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _147_2158 = (varops.fresh "fuel")
in ((_147_2158), (FStar_ToSMT_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _51_3062 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _51_3051 _51_3056 -> (match (((_51_3051), (_51_3056))) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _147_2163 = (let _147_2162 = (FStar_ToSMT_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _147_2161 -> Some (_147_2161)) _147_2162))
in (push_free_var env flid gtok _147_2163))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env)))))
end)) (([]), (env))))
in (match (_51_3062) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _51_3071 t_norm _51_3080 -> (match (((_51_3071), (_51_3080))) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _51_3079; FStar_Absyn_Syntax.lbtyp = _51_3077; FStar_Absyn_Syntax.lbeff = _51_3075; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let _51_3085 = (destruct_bound_function flid t_norm e)
in (match (_51_3085) with
| (binders, body, formals, tres) -> begin
(

let _51_3092 = (encode_binders None binders env)
in (match (_51_3092) with
| (vars, guards, env', binder_decls, _51_3091) -> begin
(

let decl_g = (let _147_2174 = (let _147_2173 = (let _147_2172 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_147_2172)
in ((g), (_147_2173), (FStar_ToSMT_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_ToSMT_Term.DeclFun (_147_2174))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_ToSMT_Term.DeclFun (((gtok), ([]), (FStar_ToSMT_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let app = (FStar_ToSMT_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _147_2177 = (let _147_2176 = (let _147_2175 = (FStar_ToSMT_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_147_2175)::vars_tm)
in ((g), (_147_2176)))
in (FStar_ToSMT_Term.mkApp _147_2177))
in (

let gmax = (let _147_2180 = (let _147_2179 = (let _147_2178 = (FStar_ToSMT_Term.mkApp (("MaxFuel"), ([])))
in (_147_2178)::vars_tm)
in ((g), (_147_2179)))
in (FStar_ToSMT_Term.mkApp _147_2180))
in (

let _51_3102 = (encode_exp body env')
in (match (_51_3102) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _147_2189 = (let _147_2188 = (let _147_2185 = (let _147_2184 = (let _147_2183 = (let _147_2182 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _147_2181 = (FStar_ToSMT_Term.mkEq ((gsapp), (body_tm)))
in ((_147_2182), (_147_2181))))
in (FStar_ToSMT_Term.mkImp _147_2183))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_147_2184)))
in (FStar_ToSMT_Term.mkForall _147_2185))
in (let _147_2187 = (let _147_2186 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_147_2186))
in ((_147_2188), (_147_2187))))
in FStar_ToSMT_Term.Assume (_147_2189))
in (

let eqn_f = (let _147_2193 = (let _147_2192 = (let _147_2191 = (let _147_2190 = (FStar_ToSMT_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_147_2190)))
in (FStar_ToSMT_Term.mkForall _147_2191))
in ((_147_2192), (Some ("Correspondence of recursive function to instrumented version"))))
in FStar_ToSMT_Term.Assume (_147_2193))
in (

let eqn_g' = (let _147_2202 = (let _147_2201 = (let _147_2200 = (let _147_2199 = (let _147_2198 = (let _147_2197 = (let _147_2196 = (let _147_2195 = (let _147_2194 = (FStar_ToSMT_Term.n_fuel (Prims.parse_int "0"))
in (_147_2194)::vars_tm)
in ((g), (_147_2195)))
in (FStar_ToSMT_Term.mkApp _147_2196))
in ((gsapp), (_147_2197)))
in (FStar_ToSMT_Term.mkEq _147_2198))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_147_2199)))
in (FStar_ToSMT_Term.mkForall _147_2200))
in ((_147_2201), (Some ("Fuel irrelevance"))))
in FStar_ToSMT_Term.Assume (_147_2202))
in (

let _51_3125 = (

let _51_3112 = (encode_binders None formals env0)
in (match (_51_3112) with
| (vars, v_guards, env, binder_decls, _51_3111) -> begin
(

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let gapp = (FStar_ToSMT_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _147_2203 = (FStar_ToSMT_Term.mkFreeV ((gtok), (FStar_ToSMT_Term.Term_sort)))
in (mk_ApplyE _147_2203 ((fuel)::vars)))
in (let _147_2207 = (let _147_2206 = (let _147_2205 = (let _147_2204 = (FStar_ToSMT_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_147_2204)))
in (FStar_ToSMT_Term.mkForall _147_2205))
in ((_147_2206), (Some ("Fuel token correspondence"))))
in FStar_ToSMT_Term.Assume (_147_2207)))
in (

let _51_3122 = (

let _51_3119 = (encode_typ_pred None tres env gapp)
in (match (_51_3119) with
| (g_typing, d3) -> begin
(let _147_2215 = (let _147_2214 = (let _147_2213 = (let _147_2212 = (let _147_2211 = (let _147_2210 = (let _147_2209 = (let _147_2208 = (FStar_ToSMT_Term.mk_and_l v_guards)
in ((_147_2208), (g_typing)))
in (FStar_ToSMT_Term.mkImp _147_2209))
in ((((gapp)::[])::[]), ((fuel)::vars), (_147_2210)))
in (FStar_ToSMT_Term.mkForall _147_2211))
in ((_147_2212), (None)))
in FStar_ToSMT_Term.Assume (_147_2213))
in (_147_2214)::[])
in ((d3), (_147_2215)))
end))
in (match (_51_3122) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_51_3125) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _51_3141 = (let _147_2218 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _51_3129 _51_3133 -> (match (((_51_3129), (_51_3133))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _51_3137 = (encode_one_binding env0 gtok ty bs)
in (match (_51_3137) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _147_2218))
in (match (_51_3141) with
| (decls, eqns, env0) -> begin
(

let _51_3150 = (let _147_2220 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _147_2220 (FStar_List.partition (fun _51_29 -> (match (_51_29) with
| FStar_ToSMT_Term.DeclFun (_51_3144) -> begin
true
end
| _51_3147 -> begin
false
end)))))
in (match (_51_3150) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
end))
end))))
end)))))
end
end)))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _147_2223 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _147_2223 (FStar_String.concat " and ")))
in (

let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((Prims.string * FStar_ToSMT_Term.term Prims.option) * FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(

let _51_3177 = (encode_free_var env x t t_norm [])
in (match (_51_3177) with
| (decls, env) -> begin
(

let _51_3182 = (lookup_lid env x)
in (match (_51_3182) with
| (n, x', _51_3181) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _51_3186) -> begin
((((n), (x))), ([]), (env))
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_ToSMT_Term.decl Prims.list = (fun env lid t -> (

let _51_3194 = (encode_function_type_as_formula None None t env)
in (match (_51_3194) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _147_2236 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _147_2236)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(

let _51_3203 = (new_term_constant_and_tok_from_lid env lid)
in (match (_51_3203) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _51_3206) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _51_30 -> (match (_51_30) with
| (FStar_Util.Inl (_51_3211), _51_3214) -> begin
FStar_ToSMT_Term.Type_sort
end
| _51_3217 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _51_3219 -> begin
[]
end)
in (

let d = FStar_ToSMT_Term.DeclFun (((vname), (arg_sorts), (FStar_ToSMT_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_ToSMT_Term.DeclFun (((vtok), ([]), (FStar_ToSMT_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let definition = (prims.mk lid vname)
in (

let env = (push_free_var env lid vname None)
in ((definition), (env)))))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _51_3236 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _147_2238 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_147_2238)))
end else begin
((args), (((None), ((FStar_Absyn_Util.comp_result comp)))))
end
end
| None -> begin
(([]), (((None), (t_norm))))
end)
in (match (_51_3236) with
| (formals, (pre_opt, res_t)) -> begin
(

let _51_3240 = (new_term_constant_and_tok_from_lid env lid)
in (match (_51_3240) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV ((vname), (FStar_ToSMT_Term.Term_sort)))
end
| _51_3243 -> begin
(FStar_ToSMT_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _51_31 -> (match (_51_31) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(

let _51_3259 = (FStar_Util.prefix vars)
in (match (_51_3259) with
| (_51_3254, (xxsym, _51_3257)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV ((xxsym), (FStar_ToSMT_Term.Term_sort)))
in (let _147_2255 = (let _147_2254 = (let _147_2253 = (let _147_2252 = (let _147_2251 = (let _147_2250 = (let _147_2249 = (let _147_2248 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _147_2248))
in ((vapp), (_147_2249)))
in (FStar_ToSMT_Term.mkEq _147_2250))
in ((((vapp)::[])::[]), (vars), (_147_2251)))
in (FStar_ToSMT_Term.mkForall _147_2252))
in ((_147_2253), (Some ("Discriminator equation"))))
in FStar_ToSMT_Term.Assume (_147_2254))
in (_147_2255)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(

let _51_3272 = (FStar_Util.prefix vars)
in (match (_51_3272) with
| (_51_3267, (xxsym, _51_3270)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV ((xxsym), (FStar_ToSMT_Term.Term_sort)))
in (

let prim_app = (let _147_2257 = (let _147_2256 = (mk_term_projector_name d f)
in ((_147_2256), ((xx)::[])))
in (FStar_ToSMT_Term.mkApp _147_2257))
in (let _147_2262 = (let _147_2261 = (let _147_2260 = (let _147_2259 = (let _147_2258 = (FStar_ToSMT_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_147_2258)))
in (FStar_ToSMT_Term.mkForall _147_2259))
in ((_147_2260), (Some ("Projector equation"))))
in FStar_ToSMT_Term.Assume (_147_2261))
in (_147_2262)::[])))
end))
end
| _51_3276 -> begin
[]
end)))))
in (

let _51_3283 = (encode_binders None formals env)
in (match (_51_3283) with
| (vars, guards, env', decls1, _51_3282) -> begin
(

let _51_3292 = (match (pre_opt) with
| None -> begin
(let _147_2263 = (FStar_ToSMT_Term.mk_and_l guards)
in ((_147_2263), (decls1)))
end
| Some (p) -> begin
(

let _51_3289 = (encode_formula p env')
in (match (_51_3289) with
| (g, ds) -> begin
(let _147_2264 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in ((_147_2264), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_51_3292) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_ApplyE vtok_tm vars)
in (

let vapp = (let _147_2266 = (let _147_2265 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in ((vname), (_147_2265)))
in (FStar_ToSMT_Term.mkApp _147_2266))
in (

let _51_3323 = (

let vname_decl = (let _147_2269 = (let _147_2268 = (FStar_All.pipe_right formals (FStar_List.map (fun _51_32 -> (match (_51_32) with
| (FStar_Util.Inl (_51_3297), _51_3300) -> begin
FStar_ToSMT_Term.Type_sort
end
| _51_3303 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in ((vname), (_147_2268), (FStar_ToSMT_Term.Term_sort), (None)))
in FStar_ToSMT_Term.DeclFun (_147_2269))
in (

let _51_3310 = (

let env = (

let _51_3305 = env
in {bindings = _51_3305.bindings; depth = _51_3305.depth; tcenv = _51_3305.tcenv; warn = _51_3305.warn; cache = _51_3305.cache; nolabels = _51_3305.nolabels; use_zfuel_name = _51_3305.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_51_3310) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_ToSMT_Term.Assume (((tok_typing), (Some ("function token typing"))))
in (

let _51_3320 = (match (formals) with
| [] -> begin
(let _147_2273 = (let _147_2272 = (let _147_2271 = (FStar_ToSMT_Term.mkFreeV ((vname), (FStar_ToSMT_Term.Term_sort)))
in (FStar_All.pipe_left (fun _147_2270 -> Some (_147_2270)) _147_2271))
in (push_free_var env lid vname _147_2272))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_147_2273)))
end
| _51_3314 -> begin
(

let vtok_decl = FStar_ToSMT_Term.DeclFun (((vtok), ([]), (FStar_ToSMT_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _147_2274 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token ((vtok), (FStar_ToSMT_Term.Term_sort)) _147_2274))
in (

let name_tok_corr = (let _147_2278 = (let _147_2277 = (let _147_2276 = (let _147_2275 = (FStar_ToSMT_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::[]), (vars), (_147_2275)))
in (FStar_ToSMT_Term.mkForall _147_2276))
in ((_147_2277), (None)))
in FStar_ToSMT_Term.Assume (_147_2278))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_51_3320) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_51_3323) with
| (decls2, env) -> begin
(

let _51_3331 = (

let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (

let _51_3327 = (encode_typ_term res_t env')
in (match (_51_3327) with
| (encoded_res_t, decls) -> begin
(let _147_2279 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_147_2279), (decls)))
end)))
in (match (_51_3331) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _147_2283 = (let _147_2282 = (let _147_2281 = (let _147_2280 = (FStar_ToSMT_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_147_2280)))
in (FStar_ToSMT_Term.mkForall _147_2281))
in ((_147_2282), (Some ("free var typing"))))
in FStar_ToSMT_Term.Assume (_147_2283))
in (

let g = (let _147_2287 = (let _147_2286 = (let _147_2285 = (let _147_2284 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_147_2284)
in (FStar_List.append decls3 _147_2285))
in (FStar_List.append decls2 _147_2286))
in (FStar_List.append decls1 _147_2287))
in ((g), (env))))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _51_3338 se -> (match (_51_3338) with
| (g, env) -> begin
(

let _51_3342 = (encode_sigelt env se)
in (match (_51_3342) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_Tc_Env.binding Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _51_3349 -> (match (_51_3349) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(

let _51_3357 = (new_term_constant env x)
in (match (_51_3357) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (

let _51_3359 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _147_2302 = (FStar_Absyn_Print.strBvd x)
in (let _147_2301 = (FStar_Absyn_Print.typ_to_string t0)
in (let _147_2300 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _147_2302 _147_2301 _147_2300))))
end else begin
()
end
in (

let _51_3363 = (encode_typ_pred None t1 env xx)
in (match (_51_3363) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _147_2306 = (let _147_2305 = (FStar_Absyn_Print.strBvd x)
in (let _147_2304 = (FStar_Absyn_Print.typ_to_string t0)
in (let _147_2303 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _147_2305 _147_2304 _147_2303))))
in Some (_147_2306))
end else begin
None
end
in (

let g = (FStar_List.append ((FStar_ToSMT_Term.DeclFun (((xxsym), ([]), (FStar_ToSMT_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((FStar_ToSMT_Term.Assume (((t), (None))))::[])))
in (((FStar_List.append decls g)), (env'))))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(

let _51_3373 = (new_typ_constant env a)
in (match (_51_3373) with
| (aasym, aa, env') -> begin
(

let _51_3376 = (encode_knd k env aa)
in (match (_51_3376) with
| (k, decls') -> begin
(

let g = (let _147_2311 = (let _147_2310 = (let _147_2309 = (let _147_2308 = (let _147_2307 = (FStar_Absyn_Print.strBvd a)
in Some (_147_2307))
in ((aasym), ([]), (FStar_ToSMT_Term.Type_sort), (_147_2308)))
in FStar_ToSMT_Term.DeclFun (_147_2309))
in (_147_2310)::[])
in (FStar_List.append _147_2311 (FStar_List.append decls' ((FStar_ToSMT_Term.Assume (((k), (None))))::[]))))
in (((FStar_List.append decls g)), (env')))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(

let t_norm = (whnf env t)
in (

let _51_3385 = (encode_free_var env x t t_norm [])
in (match (_51_3385) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(

let _51_3390 = (encode_sigelt env se)
in (match (_51_3390) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings (([]), (env)))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _51_3397 -> (match (_51_3397) with
| (l, _51_3394, _51_3396) -> begin
FStar_ToSMT_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_ToSMT_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _51_3404 -> (match (_51_3404) with
| (l, _51_3401, _51_3403) -> begin
(let _147_2319 = (FStar_All.pipe_left (fun _147_2315 -> FStar_ToSMT_Term.Echo (_147_2315)) (Prims.fst l))
in (let _147_2318 = (let _147_2317 = (let _147_2316 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_147_2316))
in (_147_2317)::[])
in (_147_2319)::_147_2318))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _147_2324 = (let _147_2323 = (let _147_2322 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _147_2322; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_147_2323)::[])
in (FStar_ST.op_Colon_Equals last_env _147_2324)))


let get_env : FStar_Tc_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_51_3410 -> begin
(

let _51_3413 = e
in {bindings = _51_3413.bindings; depth = _51_3413.depth; tcenv = tcenv; warn = _51_3413.warn; cache = _51_3413.cache; nolabels = _51_3413.nolabels; use_zfuel_name = _51_3413.use_zfuel_name; encode_non_total_function_typ = _51_3413.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_51_3419)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _51_3421 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let _51_3427 = hd
in {bindings = _51_3427.bindings; depth = _51_3427.depth; tcenv = _51_3427.tcenv; warn = _51_3427.warn; cache = refs; nolabels = _51_3427.nolabels; use_zfuel_name = _51_3427.use_zfuel_name; encode_non_total_function_typ = _51_3427.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _51_3430 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_51_3434)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _51_3436 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _51_3437 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _51_3438 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_51_3441)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _51_3446 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (

let _51_3448 = (init_env tcenv)
in (

let _51_3450 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _51_3453 = (push_env ())
in (

let _51_3455 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _51_3458 = (let _147_2345 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _147_2345))
in (

let _51_3460 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _51_3463 = (mark_env ())
in (

let _51_3465 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _51_3468 = (reset_mark_env ())
in (

let _51_3470 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _51_3473 = (commit_mark_env ())
in (

let _51_3475 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))


let encode_sig : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _147_2359 = (let _147_2358 = (let _147_2357 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _147_2357))
in FStar_ToSMT_Term.Caption (_147_2358))
in (_147_2359)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _51_3484 = (encode_sigelt env se)
in (match (_51_3484) with
| (decls, env) -> begin
(

let _51_3485 = (set_env env)
in (let _147_2360 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _147_2360)))
end)))))


let encode_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (

let _51_3490 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _147_2365 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _147_2365))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _51_3497 = (encode_signature (

let _51_3493 = env
in {bindings = _51_3493.bindings; depth = _51_3493.depth; tcenv = _51_3493.tcenv; warn = false; cache = _51_3493.cache; nolabels = _51_3493.nolabels; use_zfuel_name = _51_3493.use_zfuel_name; encode_non_total_function_typ = _51_3493.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_51_3497) with
| (decls, env) -> begin
(

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (

let _51_3503 = (set_env (

let _51_3501 = env
in {bindings = _51_3501.bindings; depth = _51_3501.depth; tcenv = _51_3501.tcenv; warn = true; cache = _51_3501.cache; nolabels = _51_3501.nolabels; use_zfuel_name = _51_3501.use_zfuel_name; encode_non_total_function_typ = _51_3501.encode_non_total_function_typ}))
in (

let _51_3505 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))


let solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (

let _51_3510 = (let _147_2374 = (let _147_2373 = (let _147_2372 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _147_2372))
in (FStar_Util.format1 "Starting query at %s" _147_2373))
in (push _147_2374))
in (

let pop = (fun _51_3513 -> (match (()) with
| () -> begin
(let _147_2379 = (let _147_2378 = (let _147_2377 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _147_2377))
in (FStar_Util.format1 "Ending query at %s" _147_2378))
in (pop _147_2379))
end))
in (

let _51_3572 = (

let env = (get_env tcenv)
in (

let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _51_3546 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Tc_Env.Binding_var (x, t))::rest -> begin
(

let _51_3528 = (aux rest)
in (match (_51_3528) with
| (out, rest) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (let _147_2385 = (let _147_2384 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_147_2384)::out)
in ((_147_2385), (rest))))
end))
end
| (FStar_Tc_Env.Binding_typ (a, k))::rest -> begin
(

let _51_3538 = (aux rest)
in (match (_51_3538) with
| (out, rest) -> begin
(let _147_2387 = (let _147_2386 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_147_2386)::out)
in ((_147_2387), (rest)))
end))
end
| _51_3540 -> begin
(([]), (bindings))
end))
in (

let _51_3543 = (aux bindings)
in (match (_51_3543) with
| (closing, bindings) -> begin
(let _147_2388 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in ((_147_2388), (bindings)))
end)))
in (match (_51_3546) with
| (q, bindings) -> begin
(

let _51_3555 = (let _147_2390 = (FStar_List.filter (fun _51_33 -> (match (_51_33) with
| FStar_Tc_Env.Binding_sig (_51_3549) -> begin
false
end
| _51_3552 -> begin
true
end)) bindings)
in (encode_env_bindings env _147_2390))
in (match (_51_3555) with
| (env_decls, env) -> begin
(

let _51_3556 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _147_2391 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _147_2391))
end else begin
()
end
in (

let _51_3561 = (encode_formula_with_labels q env)
in (match (_51_3561) with
| (phi, labels, qdecls) -> begin
(

let _51_3564 = (encode_labels labels)
in (match (_51_3564) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _147_2393 = (let _147_2392 = (FStar_ToSMT_Term.mkNot phi)
in ((_147_2392), (Some ("query"))))
in FStar_ToSMT_Term.Assume (_147_2393))
in (

let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end)))
end))
end))))
in (match (_51_3572) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _51_3579); FStar_ToSMT_Term.hash = _51_3576; FStar_ToSMT_Term.freevars = _51_3574}, _51_3584) -> begin
(

let _51_3587 = (pop ())
in ())
end
| _51_3590 when tcenv.FStar_Tc_Env.admit -> begin
(

let _51_3591 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _51_3595) -> begin
(

let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= (Prims.parse_int "2048"))
in (

let _51_3599 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (

let with_fuel = (fun p _51_3605 -> (match (_51_3605) with
| (n, i) -> begin
(let _147_2416 = (let _147_2415 = (let _147_2400 = (let _147_2399 = (FStar_Util.string_of_int n)
in (let _147_2398 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _147_2399 _147_2398)))
in FStar_ToSMT_Term.Caption (_147_2400))
in (let _147_2414 = (let _147_2413 = (let _147_2405 = (let _147_2404 = (let _147_2403 = (let _147_2402 = (FStar_ToSMT_Term.mkApp (("MaxFuel"), ([])))
in (let _147_2401 = (FStar_ToSMT_Term.n_fuel n)
in ((_147_2402), (_147_2401))))
in (FStar_ToSMT_Term.mkEq _147_2403))
in ((_147_2404), (None)))
in FStar_ToSMT_Term.Assume (_147_2405))
in (let _147_2412 = (let _147_2411 = (let _147_2410 = (let _147_2409 = (let _147_2408 = (let _147_2407 = (FStar_ToSMT_Term.mkApp (("MaxIFuel"), ([])))
in (let _147_2406 = (FStar_ToSMT_Term.n_fuel i)
in ((_147_2407), (_147_2406))))
in (FStar_ToSMT_Term.mkEq _147_2408))
in ((_147_2409), (None)))
in FStar_ToSMT_Term.Assume (_147_2410))
in (_147_2411)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_147_2413)::_147_2412))
in (_147_2415)::_147_2414))
in (FStar_List.append _147_2416 suffix))
end))
in (

let check = (fun p -> (

let initial_config = (let _147_2420 = (FStar_Options.initial_fuel ())
in (let _147_2419 = (FStar_Options.initial_ifuel ())
in ((_147_2420), (_147_2419))))
in (

let alt_configs = (let _147_2439 = (let _147_2438 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _147_2423 = (let _147_2422 = (FStar_Options.initial_fuel ())
in (let _147_2421 = (FStar_Options.max_ifuel ())
in ((_147_2422), (_147_2421))))
in (_147_2423)::[])
end else begin
[]
end
in (let _147_2437 = (let _147_2436 = if (((FStar_Options.max_fuel ()) / (Prims.parse_int "2")) > (FStar_Options.initial_fuel ())) then begin
(let _147_2426 = (let _147_2425 = ((FStar_Options.max_fuel ()) / (Prims.parse_int "2"))
in (let _147_2424 = (FStar_Options.max_ifuel ())
in ((_147_2425), (_147_2424))))
in (_147_2426)::[])
end else begin
[]
end
in (let _147_2435 = (let _147_2434 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _147_2429 = (let _147_2428 = (FStar_Options.max_fuel ())
in (let _147_2427 = (FStar_Options.max_ifuel ())
in ((_147_2428), (_147_2427))))
in (_147_2429)::[])
end else begin
[]
end
in (let _147_2433 = (let _147_2432 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _147_2431 = (let _147_2430 = (FStar_Options.min_fuel ())
in ((_147_2430), ((Prims.parse_int "1"))))
in (_147_2431)::[])
end else begin
[]
end
in (_147_2432)::[])
in (_147_2434)::_147_2433))
in (_147_2436)::_147_2435))
in (_147_2438)::_147_2437))
in (FStar_List.flatten _147_2439))
in (

let report = (fun errs -> (

let errs = (match (errs) with
| [] -> begin
((("Unknown assertion failed"), (FStar_Absyn_Syntax.dummyRange)))::[]
end
| _51_3614 -> begin
errs
end)
in (

let _51_3616 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _147_2447 = (let _147_2442 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _147_2442))
in (let _147_2446 = (let _147_2443 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _147_2443 FStar_Util.string_of_int))
in (let _147_2445 = (let _147_2444 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _147_2444 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _147_2447 _147_2446 _147_2445))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (

let rec try_alt_configs = (fun p errs _51_34 -> (match (_51_34) with
| [] -> begin
(report errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _147_2458 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _147_2458 (cb mi p [])))
end
| _51_3628 -> begin
(report errs)
end)
end
| (mi)::tl -> begin
(let _147_2460 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _147_2460 (fun _51_3634 -> (match (_51_3634) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl ((ok), (errs')))
end
| _51_3637 -> begin
(cb mi p tl ((ok), (errs)))
end)
end))))
end))
and cb = (fun _51_3640 p alt _51_3645 -> (match (((_51_3640), (_51_3645))) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(let _147_2468 = (let _147_2465 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _147_2465))
in (let _147_2467 = (FStar_Util.string_of_int prev_fuel)
in (let _147_2466 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _147_2468 _147_2467 _147_2466))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _147_2469 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _147_2469 (cb initial_config p alt_configs))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let _51_3650 = (let _147_2475 = (FStar_Options.split_cases ())
in (FStar_ToSMT_SplitQueryCases.can_handle_query _147_2475 q))
in (match (_51_3650) with
| (b, cb) -> begin
if b then begin
(FStar_ToSMT_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (

let _51_3651 = if (FStar_Options.admit_smt_queries ()) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _51_3654 -> begin
(Prims.raise Bad_form)
end)
end)))))


let is_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _51_3658 = (push "query")
in (

let _51_3665 = (encode_formula_with_labels q env)
in (match (_51_3665) with
| (f, _51_3662, _51_3664) -> begin
(

let _51_3666 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _51_3670) -> begin
true
end
| _51_3674 -> begin
false
end))
end)))))


let solver : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}


let dummy : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = (fun _51_3675 -> ()); FStar_Tc_Env.push = (fun _51_3677 -> ()); FStar_Tc_Env.pop = (fun _51_3679 -> ()); FStar_Tc_Env.mark = (fun _51_3681 -> ()); FStar_Tc_Env.reset_mark = (fun _51_3683 -> ()); FStar_Tc_Env.commit_mark = (fun _51_3685 -> ()); FStar_Tc_Env.encode_modul = (fun _51_3687 _51_3689 -> ()); FStar_Tc_Env.encode_sig = (fun _51_3691 _51_3693 -> ()); FStar_Tc_Env.solve = (fun _51_3695 _51_3697 -> ()); FStar_Tc_Env.is_trivial = (fun _51_3699 _51_3701 -> false); FStar_Tc_Env.finish = (fun _51_3703 -> ()); FStar_Tc_Env.refresh = (fun _51_3704 -> ())}




