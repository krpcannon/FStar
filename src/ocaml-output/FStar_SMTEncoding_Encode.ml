
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _89_30 -> (match (_89_30) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _89_1 -> (match (_89_1) with
| (FStar_Util.Inl (_89_34), _89_37) -> begin
false
end
| _89_40 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _185_12 = (let _185_11 = (let _185_10 = (let _185_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _185_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _185_10))
in FStar_Util.Inl (_185_11))
in Some (_185_12))
end
| _89_47 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _89_51 = a
in (let _185_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _185_19; FStar_Syntax_Syntax.index = _89_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _89_51.FStar_Syntax_Syntax.sort}))
in (let _185_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _185_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _89_58 -> (match (()) with
| () -> begin
(let _185_30 = (let _185_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _185_29 lid.FStar_Ident.str))
in (FStar_All.failwith _185_30))
end))
in (

let _89_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_89_62) with
| (_89_60, t) -> begin
(match ((let _185_31 = (FStar_Syntax_Subst.compress t)
in _185_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _89_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_89_70) with
| (binders, _89_69) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _89_73 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _185_37 = (let _185_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _185_36))
in (FStar_All.pipe_left escape _185_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _185_43 = (let _185_42 = (mk_term_projector_name lid a)
in ((_185_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _185_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _185_49 = (let _185_48 = (mk_term_projector_name_by_pos lid i)
in ((_185_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _185_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _89_98 -> (match (()) with
| () -> begin
(let _185_162 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _185_161 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_185_162), (_185_161))))
end))
in (

let scopes = (let _185_164 = (let _185_163 = (new_scope ())
in (_185_163)::[])
in (FStar_Util.mk_ref _185_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _185_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _185_168 (fun _89_106 -> (match (_89_106) with
| (names, _89_105) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_89_109) -> begin
(

let _89_111 = (FStar_Util.incr ctr)
in (let _185_171 = (let _185_170 = (let _185_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _185_169))
in (Prims.strcat "__" _185_170))
in (Prims.strcat y _185_171)))
end)
in (

let top_scope = (let _185_173 = (let _185_172 = (FStar_ST.read scopes)
in (FStar_List.hd _185_172))
in (FStar_All.pipe_left Prims.fst _185_173))
in (

let _89_115 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _185_180 = (let _185_179 = (let _185_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _185_178))
in (Prims.strcat pp.FStar_Ident.idText _185_179))
in (FStar_All.pipe_left mk_unique _185_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _89_123 -> (match (()) with
| () -> begin
(

let _89_124 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _185_188 = (let _185_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _185_187))
in (FStar_Util.format2 "%s_%s" pfx _185_188)))
in (

let string_const = (fun s -> (match ((let _185_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _185_192 (fun _89_133 -> (match (_89_133) with
| (_89_131, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _185_193 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _185_193))
in (

let top_scope = (let _185_195 = (let _185_194 = (FStar_ST.read scopes)
in (FStar_List.hd _185_194))
in (FStar_All.pipe_left Prims.snd _185_195))
in (

let _89_140 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _89_143 -> (match (()) with
| () -> begin
(let _185_200 = (let _185_199 = (new_scope ())
in (let _185_198 = (FStar_ST.read scopes)
in (_185_199)::_185_198))
in (FStar_ST.op_Colon_Equals scopes _185_200))
end))
in (

let pop = (fun _89_145 -> (match (()) with
| () -> begin
(let _185_204 = (let _185_203 = (FStar_ST.read scopes)
in (FStar_List.tl _185_203))
in (FStar_ST.op_Colon_Equals scopes _185_204))
end))
in (

let mark = (fun _89_147 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _89_149 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _89_151 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _89_164 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _89_169 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _89_172 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _89_174 = x
in (let _185_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _185_219; FStar_Syntax_Syntax.index = _89_174.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _89_174.FStar_Syntax_Syntax.sort})))


type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
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


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_89_178) -> begin
_89_178
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_89_181) -> begin
_89_181
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _185_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _89_2 -> (match (_89_2) with
| Binding_var (x, _89_196) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _89_201, _89_203, _89_205) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _185_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _185_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_185_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _185_292 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (_185_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _185_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _185_297))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _89_219 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _89_219.tcenv; warn = _89_219.warn; cache = _89_219.cache; nolabels = _89_219.nolabels; use_zfuel_name = _89_219.use_zfuel_name; encode_non_total_function_typ = _89_219.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _89_225 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _89_225.depth; tcenv = _89_225.tcenv; warn = _89_225.warn; cache = _89_225.cache; nolabels = _89_225.nolabels; use_zfuel_name = _89_225.use_zfuel_name; encode_non_total_function_typ = _89_225.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _89_232 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _89_232.depth; tcenv = _89_232.tcenv; warn = _89_232.warn; cache = _89_232.cache; nolabels = _89_232.nolabels; use_zfuel_name = _89_232.use_zfuel_name; encode_non_total_function_typ = _89_232.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _89_237 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _89_237.depth; tcenv = _89_237.tcenv; warn = _89_237.warn; cache = _89_237.cache; nolabels = _89_237.nolabels; use_zfuel_name = _89_237.use_zfuel_name; encode_non_total_function_typ = _89_237.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _89_3 -> (match (_89_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _89_249 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _185_322 = (let _185_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _185_321))
in (FStar_All.failwith _185_322))
end
| Some (b, t) -> begin
t
end))
end
| Some (b, t) -> begin
t
end)))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _185_333 = (

let _89_265 = env
in (let _185_332 = (let _185_331 = (let _185_330 = (let _185_329 = (let _185_328 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _185_327 -> Some (_185_327)) _185_328))
in ((x), (fname), (_185_329), (None)))
in Binding_fvar (_185_330))
in (_185_331)::env.bindings)
in {bindings = _185_332; depth = _89_265.depth; tcenv = _89_265.tcenv; warn = _89_265.warn; cache = _89_265.cache; nolabels = _89_265.nolabels; use_zfuel_name = _89_265.use_zfuel_name; encode_non_total_function_typ = _89_265.encode_non_total_function_typ}))
in ((fname), (ftok), (_185_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _89_4 -> (match (_89_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _89_277 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _185_344 = (lookup_binding env (fun _89_5 -> (match (_89_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _89_288 -> begin
None
end)))
in (FStar_All.pipe_right _185_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _185_350 = (let _185_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _185_349))
in (FStar_All.failwith _185_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _89_298 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _89_298.depth; tcenv = _89_298.tcenv; warn = _89_298.warn; cache = _89_298.cache; nolabels = _89_298.nolabels; use_zfuel_name = _89_298.use_zfuel_name; encode_non_total_function_typ = _89_298.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _89_307 = (lookup_lid env x)
in (match (_89_307) with
| (t1, t2, _89_306) -> begin
(

let t3 = (let _185_367 = (let _185_366 = (let _185_365 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (_185_365)::[])
in ((f), (_185_366)))
in (FStar_SMTEncoding_Util.mkApp _185_367))
in (

let _89_309 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _89_309.depth; tcenv = _89_309.tcenv; warn = _89_309.warn; cache = _89_309.cache; nolabels = _89_309.nolabels; use_zfuel_name = _89_309.use_zfuel_name; encode_non_total_function_typ = _89_309.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _89_322 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_89_326, (fuel)::[]) -> begin
if (let _185_373 = (let _185_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _185_372 Prims.fst))
in (FStar_Util.starts_with _185_373 "fuel")) then begin
(let _185_376 = (let _185_375 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _185_375 fuel))
in (FStar_All.pipe_left (fun _185_374 -> Some (_185_374)) _185_376))
end else begin
Some (t)
end
end
| _89_332 -> begin
Some (t)
end)
end
| _89_334 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _185_380 = (let _185_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _185_379))
in (FStar_All.failwith _185_380))
end))


let lookup_free_var_name = (fun env a -> (

let _89_347 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_89_347) with
| (x, _89_344, _89_346) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _89_353 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_89_353) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = _89_357; FStar_SMTEncoding_Term.rng = _89_355}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _89_365 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _89_375 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _89_6 -> (match (_89_6) with
| Binding_fvar (_89_380, nm', tok, _89_384) when (nm = nm') -> begin
tok
end
| _89_388 -> begin
None
end))))


let mkForall_fuel' = (fun n _89_393 -> (match (_89_393) with
| (pats, vars, body) -> begin
(

let fallback = (fun _89_395 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _89_398 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_89_398) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _89_408 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _185_397 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l _185_397))
end
| _89_421 -> begin
(let _185_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _185_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| _89_424 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))))))
end))
end)
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _185_404 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _185_404 FStar_Option.isNone))
end
| _89_463 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _185_409 = (FStar_Syntax_Util.un_uinst t)
in _185_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_89_467, _89_469, Some (FStar_Util.Inr (l))) -> begin
((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
end
| FStar_Syntax_Syntax.Tm_abs (_89_476, _89_478, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _185_410 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _185_410 FStar_Option.isSome))
end
| _89_487 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _185_423 = (let _185_421 = (FStar_Syntax_Syntax.null_binder t)
in (_185_421)::[])
in (let _185_422 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _185_423 _185_422 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _185_430 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _185_430))
end
| s -> begin
(

let _89_499 = ()
in (let _185_431 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out _185_431)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _89_7 -> (match (_89_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _89_509 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = _89_520; FStar_SMTEncoding_Term.rng = _89_518})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _89_538) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _89_545 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_89_547, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _89_553 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list


type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))


exception Let_rec_unencodeable


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _89_8 -> (match (_89_8) with
| FStar_Const.Const_unit -> begin
FStar_SMTEncoding_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _185_488 = (let _185_487 = (let _185_486 = (let _185_485 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _185_485))
in (_185_486)::[])
in (("FStar.Char.Char"), (_185_487)))
in (FStar_SMTEncoding_Util.mkApp _185_488))
end
| FStar_Const.Const_int (i, None) -> begin
(let _185_489 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _185_489))
end
| FStar_Const.Const_int (i, Some (_89_573)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _89_579) -> begin
(let _185_490 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _185_490))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _185_492 = (let _185_491 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _185_491))
in (FStar_All.failwith _185_492))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_89_593) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_89_596) -> begin
(let _185_501 = (FStar_Syntax_Util.unrefine t)
in (aux true _185_501))
end
| _89_599 -> begin
if norm then begin
(let _185_502 = (whnf env t)
in (aux false _185_502))
end else begin
(let _185_505 = (let _185_504 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _185_503 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _185_504 _185_503)))
in (FStar_All.failwith _185_505))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _89_607 -> begin
(let _185_508 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_185_508)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _89_611 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _185_556 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _185_556))
end else begin
()
end
in (

let _89_639 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _89_618 b -> (match (_89_618) with
| (vars, guards, env, decls, names) -> begin
(

let _89_633 = (

let x = (unmangle (Prims.fst b))
in (

let _89_624 = (gen_term_var env x)
in (match (_89_624) with
| (xxsym, xx, env') -> begin
(

let _89_627 = (let _185_559 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _185_559 env xx))
in (match (_89_627) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_89_633) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_89_639) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _89_646 = (encode_term t env)
in (match (_89_646) with
| (t, decls) -> begin
(let _185_564 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_185_564), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _89_653 = (encode_term t env)
in (match (_89_653) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _185_569 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_185_569), (decls)))
end
| Some (f) -> begin
(let _185_570 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_185_570), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _89_660 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _185_575 = (FStar_Syntax_Print.tag_of_term t)
in (let _185_574 = (FStar_Syntax_Print.tag_of_term t0)
in (let _185_573 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _185_575 _185_574 _185_573))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _185_580 = (let _185_579 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _185_578 = (FStar_Syntax_Print.tag_of_term t0)
in (let _185_577 = (FStar_Syntax_Print.term_to_string t0)
in (let _185_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _185_579 _185_578 _185_577 _185_576)))))
in (FStar_All.failwith _185_580))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _185_582 = (let _185_581 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _185_581))
in (FStar_All.failwith _185_582))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _89_671) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _89_676) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _185_583 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_185_583), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_89_685) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _89_689) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _185_584 = (encode_const c)
in ((_185_584), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _89_700 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_89_700) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _89_707 = (encode_binders None binders env)
in (match (_89_707) with
| (vars, guards, env', decls, _89_706) -> begin
(

let fsym = (let _185_585 = (varops.fresh "f")
in ((_185_585), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _89_715 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _89_711 = env.tcenv
in {FStar_TypeChecker_Env.solver = _89_711.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _89_711.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _89_711.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _89_711.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _89_711.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _89_711.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _89_711.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _89_711.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _89_711.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _89_711.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _89_711.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _89_711.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _89_711.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _89_711.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _89_711.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _89_711.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _89_711.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _89_711.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _89_711.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _89_711.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _89_711.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _89_711.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _89_711.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_89_715) with
| (pre_opt, res_t) -> begin
(

let _89_718 = (encode_term_pred None res_t env' app)
in (match (_89_718) with
| (res_pred, decls') -> begin
(

let _89_727 = (match (pre_opt) with
| None -> begin
(let _185_586 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_185_586), ([])))
end
| Some (pre) -> begin
(

let _89_724 = (encode_formula pre env')
in (match (_89_724) with
| (guard, decls0) -> begin
(let _185_587 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((_185_587), (decls0)))
end))
end)
in (match (_89_727) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _185_589 = (let _185_588 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_185_588)))
in (FStar_SMTEncoding_Util.mkForall _185_589))
in (

let cvars = (let _185_591 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _185_591 (FStar_List.filter (fun _89_732 -> (match (_89_732) with
| (x, _89_731) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t', sorts, _89_739) -> begin
(let _185_594 = (let _185_593 = (let _185_592 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (_185_592)))
in (FStar_SMTEncoding_Util.mkApp _185_593))
in ((_185_594), ([])))
end
| None -> begin
(

let tsym = (let _185_596 = (let _185_595 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" _185_595))
in (varops.mk_unique _185_596))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _185_597 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_185_597))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _185_599 = (let _185_598 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_185_598)))
in (FStar_SMTEncoding_Util.mkApp _185_599))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _185_601 = (let _185_600 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_185_600), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_185_601)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _185_608 = (let _185_607 = (let _185_606 = (let _185_605 = (let _185_604 = (let _185_603 = (let _185_602 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _185_602))
in ((f_has_t), (_185_603)))
in (FStar_SMTEncoding_Util.mkImp _185_604))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_185_605)))
in (mkForall_fuel _185_606))
in ((_185_607), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_185_608)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _185_612 = (let _185_611 = (let _185_610 = (let _185_609 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_185_609)))
in (FStar_SMTEncoding_Util.mkForall _185_610))
in ((_185_611), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_185_612)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _89_758 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end)))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (let _185_614 = (let _185_613 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_185_613), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_185_614)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _185_621 = (let _185_620 = (let _185_619 = (let _185_618 = (let _185_617 = (let _185_616 = (let _185_615 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _185_615))
in ((f_has_t), (_185_616)))
in (FStar_SMTEncoding_Util.mkImp _185_617))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_185_618)))
in (mkForall_fuel _185_619))
in ((_185_620), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_185_621)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_89_771) -> begin
(

let _89_791 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _89_778; FStar_Syntax_Syntax.pos = _89_776; FStar_Syntax_Syntax.vars = _89_774} -> begin
(

let _89_786 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_89_786) with
| (b, f) -> begin
(let _185_623 = (let _185_622 = (FStar_List.hd b)
in (Prims.fst _185_622))
in ((_185_623), (f)))
end))
end
| _89_788 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_89_791) with
| (x, f) -> begin
(

let _89_794 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_89_794) with
| (base_t, decls) -> begin
(

let _89_798 = (gen_term_var env x)
in (match (_89_798) with
| (x, xtm, env') -> begin
(

let _89_801 = (encode_formula f env')
in (match (_89_801) with
| (refinement, decls') -> begin
(

let _89_804 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_89_804) with
| (fsym, fterm) -> begin
(

let encoding = (let _185_625 = (let _185_624 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_185_624), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd _185_625))
in (

let cvars = (let _185_627 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _185_627 (FStar_List.filter (fun _89_809 -> (match (_89_809) with
| (y, _89_808) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _89_817, _89_819) -> begin
(let _185_630 = (let _185_629 = (let _185_628 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (_185_628)))
in (FStar_SMTEncoding_Util.mkApp _185_629))
in ((_185_630), ([])))
end
| None -> begin
(

let tsym = (let _185_632 = (let _185_631 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" _185_631))
in (varops.mk_unique _185_632))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _185_634 = (let _185_633 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_185_633)))
in (FStar_SMTEncoding_Util.mkApp _185_634))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _185_638 = (let _185_637 = (let _185_636 = (let _185_635 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_185_635)))
in (FStar_SMTEncoding_Util.mkForall _185_636))
in ((_185_637), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_185_638))
in (

let t_kinding = (let _185_640 = (let _185_639 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_185_639), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_185_640))
in (

let t_interp = (let _185_646 = (let _185_645 = (let _185_642 = (let _185_641 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_185_641)))
in (FStar_SMTEncoding_Util.mkForall _185_642))
in (let _185_644 = (let _185_643 = (FStar_Syntax_Print.term_to_string t0)
in Some (_185_643))
in ((_185_645), (_185_644), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_185_646))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _89_835 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end)))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _185_647 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar _185_647))
in (

let _89_844 = (encode_term_pred None k env ttm)
in (match (_89_844) with
| (t_has_k, decls) -> begin
(

let d = (let _185_653 = (let _185_652 = (let _185_651 = (let _185_650 = (let _185_649 = (let _185_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _185_648))
in (FStar_Util.format1 "uvar_typing_%s" _185_649))
in (varops.mk_unique _185_650))
in Some (_185_651))
in ((t_has_k), (Some ("Uvar typing")), (_185_652)))
in FStar_SMTEncoding_Term.Assume (_185_653))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_89_847) -> begin
(

let _89_851 = (FStar_Syntax_Util.head_and_args t0)
in (match (_89_851) with
| (head, args_e) -> begin
(match ((let _185_655 = (let _185_654 = (FStar_Syntax_Subst.compress head)
in _185_654.FStar_Syntax_Syntax.n)
in ((_185_655), (args_e)))) with
| (_89_853, _89_855) when (head_redex env head) -> begin
(let _185_656 = (whnf env t)
in (encode_term _185_656 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _89_895 = (encode_term v1 env)
in (match (_89_895) with
| (v1, decls1) -> begin
(

let _89_898 = (encode_term v2 env)
in (match (_89_898) with
| (v2, decls2) -> begin
(let _185_657 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((_185_657), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_89_907)::(_89_904)::_89_902) -> begin
(

let e0 = (let _185_661 = (let _185_660 = (let _185_659 = (let _185_658 = (FStar_List.hd args_e)
in (_185_658)::[])
in ((head), (_185_659)))
in FStar_Syntax_Syntax.Tm_app (_185_660))
in (FStar_Syntax_Syntax.mk _185_661 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _185_664 = (let _185_663 = (let _185_662 = (FStar_List.tl args_e)
in ((e0), (_185_662)))
in FStar_Syntax_Syntax.Tm_app (_185_663))
in (FStar_Syntax_Syntax.mk _185_664 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _89_916))::[]) -> begin
(

let _89_922 = (encode_term arg env)
in (match (_89_922) with
| (tm, decls) -> begin
(let _185_665 = (FStar_SMTEncoding_Util.mkApp (("Reify"), ((tm)::[])))
in ((_185_665), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_89_924)), ((arg, _89_929))::[]) -> begin
(encode_term arg env)
end
| _89_934 -> begin
(

let _89_937 = (encode_args args_e env)
in (match (_89_937) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _89_942 = (encode_term head env)
in (match (_89_942) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _89_951 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_89_951) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _89_955 _89_959 -> (match (((_89_955), (_89_959))) with
| ((bv, _89_954), (a, _89_958)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _185_670 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _185_670 (FStar_Syntax_Subst.subst subst)))
in (

let _89_964 = (encode_term_pred None ty env app_tm)
in (match (_89_964) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _185_677 = (let _185_676 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _185_675 = (let _185_674 = (let _185_673 = (let _185_672 = (let _185_671 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string _185_671))
in (Prims.strcat "partial_app_typing_" _185_672))
in (varops.mk_unique _185_673))
in Some (_185_674))
in ((_185_676), (Some ("Partial app typing")), (_185_675))))
in FStar_SMTEncoding_Term.Assume (_185_677))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _89_971 = (lookup_free_var_sym env fv)
in (match (_89_971) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Syntax_Subst.compress head)
in (

let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _185_681 = (let _185_680 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _185_680 Prims.snd))
in Some (_185_681))
end
| FStar_Syntax_Syntax.Tm_ascribed (_89_1003, FStar_Util.Inl (t), _89_1007) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_89_1011, FStar_Util.Inr (c), _89_1015) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _89_1019 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _185_682 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _185_682))
in (

let _89_1027 = (curried_arrow_formals_comp head_type)
in (match (_89_1027) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _89_1043 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some (((formals), (c)))))
end else begin
(encode_partial_app None)
end
end)
end)))
end)))))
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _89_1052 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_89_1052) with
| (bs, body, opening) -> begin
(

let fallback = (fun _89_1054 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _185_685 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_185_685), ((decl)::[])))))
end))
in (

let is_impure = (fun _89_9 -> (match (_89_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _185_688 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _185_688 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _185_693 = (let _185_691 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _185_691))
in (FStar_All.pipe_right _185_693 (fun _185_692 -> Some (_185_692))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _89_1070 -> (match (()) with
| () -> begin
(let _185_696 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _185_696 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _185_699 = (let _185_697 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _185_697))
in (FStar_All.pipe_right _185_699 (fun _185_698 -> Some (_185_698))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _185_702 = (let _185_700 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _185_700))
in (FStar_All.pipe_right _185_702 (fun _185_701 -> Some (_185_701))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _89_1072 = (let _185_704 = (let _185_703 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _185_703))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _185_704))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _89_1082 = (encode_binders None bs env)
in (match (_89_1082) with
| (vars, guards, envbody, decls, _89_1081) -> begin
(

let _89_1085 = (encode_term body envbody)
in (match (_89_1085) with
| (body, decls') -> begin
(

let key_body = (let _185_708 = (let _185_707 = (let _185_706 = (let _185_705 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_185_705), (body)))
in (FStar_SMTEncoding_Util.mkImp _185_706))
in (([]), (vars), (_185_707)))
in (FStar_SMTEncoding_Util.mkForall _185_708))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _89_1092, _89_1094) -> begin
(let _185_711 = (let _185_710 = (let _185_709 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (_185_709)))
in (FStar_SMTEncoding_Util.mkApp _185_710))
in ((_185_711), ([])))
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

let fsym = (let _185_713 = (let _185_712 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" _185_712))
in (varops.mk_unique _185_713))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _185_715 = (let _185_714 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (_185_714)))
in (FStar_SMTEncoding_Util.mkApp _185_715))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (match ((codomain_eff lc)) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let _89_1112 = (encode_term_pred None tfun env f)
in (match (_89_1112) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _185_719 = (let _185_718 = (let _185_717 = (let _185_716 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_185_716), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_185_717))
in (_185_718)::[])
in (FStar_List.append decls'' _185_719)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _185_723 = (let _185_722 = (let _185_721 = (let _185_720 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_185_720)))
in (FStar_SMTEncoding_Util.mkForall _185_721))
in ((_185_722), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_185_723)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _89_1118 = (FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end)))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_89_1121, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_89_1133); FStar_Syntax_Syntax.lbunivs = _89_1131; FStar_Syntax_Syntax.lbtyp = _89_1129; FStar_Syntax_Syntax.lbeff = _89_1127; FStar_Syntax_Syntax.lbdef = _89_1125})::_89_1123), _89_1139) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _89_1148; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _89_1145; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_89_1158) -> begin
(

let _89_1160 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _185_724 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_185_724), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _89_1176 = (encode_term e1 env)
in (match (_89_1176) with
| (ee1, decls1) -> begin
(

let _89_1179 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_89_1179) with
| (xs, e2) -> begin
(

let _89_1183 = (FStar_List.hd xs)
in (match (_89_1183) with
| (x, _89_1182) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _89_1187 = (encode_body e2 env')
in (match (_89_1187) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _89_1195 = (encode_term e env)
in (match (_89_1195) with
| (scr, decls) -> begin
(

let _89_1232 = (FStar_List.fold_right (fun b _89_1199 -> (match (_89_1199) with
| (else_case, decls) -> begin
(

let _89_1203 = (FStar_Syntax_Subst.open_branch b)
in (match (_89_1203) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _89_1207 _89_1210 -> (match (((_89_1207), (_89_1210))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _89_1216 -> (match (_89_1216) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _89_1226 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _89_1223 = (encode_term w env)
in (match (_89_1223) with
| (w, decls2) -> begin
(let _185_758 = (let _185_757 = (let _185_756 = (let _185_755 = (let _185_754 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (_185_754)))
in (FStar_SMTEncoding_Util.mkEq _185_755))
in ((guard), (_185_756)))
in (FStar_SMTEncoding_Util.mkAnd _185_757))
in ((_185_758), (decls2)))
end))
end)
in (match (_89_1226) with
| (guard, decls2) -> begin
(

let _89_1229 = (encode_br br env)
in (match (_89_1229) with
| (br, decls3) -> begin
(let _185_759 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((_185_759), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_89_1232) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _89_1238 -> begin
(let _185_762 = (encode_one_pat env pat)
in (_185_762)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _89_1241 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _185_765 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _185_765))
end else begin
()
end
in (

let _89_1245 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_89_1245) with
| (vars, pat_term) -> begin
(

let _89_1257 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _89_1248 v -> (match (_89_1248) with
| (env, vars) -> begin
(

let _89_1254 = (gen_term_var env v)
in (match (_89_1254) with
| (xx, _89_1252, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_89_1257) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_89_1262) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _185_773 = (let _185_772 = (encode_const c)
in ((scrutinee), (_185_772)))
in (FStar_SMTEncoding_Util.mkEq _185_773))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _89_1284 -> (match (_89_1284) with
| (arg, _89_1283) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _185_776 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _185_776)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_89_1291) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_89_1301) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _185_784 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _89_1311 -> (match (_89_1311) with
| (arg, _89_1310) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _185_783 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _185_783)))
end))))
in (FStar_All.pipe_right _185_784 FStar_List.flatten))
end))
in (

let pat_term = (fun _89_1314 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _89_1330 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _89_1320 _89_1324 -> (match (((_89_1320), (_89_1324))) with
| ((tms, decls), (t, _89_1323)) -> begin
(

let _89_1327 = (encode_term t env)
in (match (_89_1327) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_89_1330) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (match ((FStar_Syntax_Util.list_elements e)) with
| Some (l) -> begin
l
end
| None -> begin
(

let _89_1340 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let one_pat = (fun p -> (

let _89_1346 = (let _185_799 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _185_799 FStar_Syntax_Util.head_and_args))
in (match (_89_1346) with
| (head, args) -> begin
(match ((let _185_801 = (let _185_800 = (FStar_Syntax_Util.un_uinst head)
in _185_800.FStar_Syntax_Syntax.n)
in ((_185_801), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_89_1354, _89_1356))::((e, _89_1351))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _89_1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _89_1369 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _89_1377 = (let _185_806 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _185_806 FStar_Syntax_Util.head_and_args))
in (match (_89_1377) with
| (head, args) -> begin
(match ((let _185_808 = (let _185_807 = (FStar_Syntax_Util.un_uinst head)
in _185_807.FStar_Syntax_Syntax.n)
in ((_185_808), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _89_1382))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _89_1387 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _185_811 = (list_elements e)
in (FStar_All.pipe_right _185_811 (FStar_List.map (fun branch -> (let _185_810 = (list_elements branch)
in (FStar_All.pipe_right _185_810 (FStar_List.map one_pat)))))))
end
| _89_1394 -> begin
(let _185_812 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_185_812)::[])
end)
end
| _89_1396 -> begin
(let _185_813 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_185_813)::[])
end))))
in (

let _89_1439 = (match ((let _185_814 = (FStar_Syntax_Subst.compress t)
in _185_814.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _89_1403 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_89_1403) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _89_1424; FStar_Syntax_Syntax.effect_name = _89_1422; FStar_Syntax_Syntax.result_typ = _89_1420; FStar_Syntax_Syntax.effect_args = ((pre, _89_1416))::((post, _89_1412))::((pats, _89_1408))::[]; FStar_Syntax_Syntax.flags = _89_1405}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _185_815 = (lemma_pats pats')
in ((binders), (pre), (post), (_185_815))))
end
| _89_1432 -> begin
(FStar_All.failwith "impos")
end)
end))
end
| _89_1434 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_89_1439) with
| (binders, pre, post, patterns) -> begin
(

let _89_1446 = (encode_binders None binders env)
in (match (_89_1446) with
| (vars, guards, env, decls, _89_1445) -> begin
(

let _89_1459 = (let _185_819 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _89_1456 = (let _185_818 = (FStar_All.pipe_right branch (FStar_List.map (fun _89_1451 -> (match (_89_1451) with
| (t, _89_1450) -> begin
(encode_term t (

let _89_1452 = env
in {bindings = _89_1452.bindings; depth = _89_1452.depth; tcenv = _89_1452.tcenv; warn = _89_1452.warn; cache = _89_1452.cache; nolabels = _89_1452.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _89_1452.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _185_818 FStar_List.unzip))
in (match (_89_1456) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _185_819 FStar_List.unzip))
in (match (_89_1459) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _185_822 = (let _185_821 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes _185_821 e))
in (_185_822)::p))))
end
| _89_1469 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _185_828 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (_185_828)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _185_830 = (let _185_829 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons _185_829 tl))
in (aux _185_830 vars))
end
| _89_1481 -> begin
pats
end))
in (let _185_831 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _185_831 vars)))
end)
end)
in (

let env = (

let _89_1483 = env
in {bindings = _89_1483.bindings; depth = _89_1483.depth; tcenv = _89_1483.tcenv; warn = _89_1483.warn; cache = _89_1483.cache; nolabels = true; use_zfuel_name = _89_1483.use_zfuel_name; encode_non_total_function_typ = _89_1483.encode_non_total_function_typ})
in (

let _89_1488 = (let _185_832 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _185_832 env))
in (match (_89_1488) with
| (pre, decls'') -> begin
(

let _89_1491 = (let _185_833 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _185_833 env))
in (match (_89_1491) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _185_838 = (let _185_837 = (let _185_836 = (let _185_835 = (let _185_834 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((_185_834), (post)))
in (FStar_SMTEncoding_Util.mkImp _185_835))
in ((pats), (vars), (_185_836)))
in (FStar_SMTEncoding_Util.mkForall _185_837))
in ((_185_838), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _185_844 = (FStar_Syntax_Print.tag_of_term phi)
in (let _185_843 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _185_844 _185_843)))
end else begin
()
end)
in (

let enc = (fun f r l -> (

let _89_1508 = (FStar_Util.fold_map (fun decls x -> (

let _89_1505 = (encode_term (Prims.fst x) env)
in (match (_89_1505) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_89_1508) with
| (decls, args) -> begin
(let _185_866 = (

let _89_1509 = (f args)
in {FStar_SMTEncoding_Term.tm = _89_1509.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _89_1509.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_185_866), (decls)))
end)))
in (

let const_op = (fun f r _89_1514 -> (let _185_878 = (f r)
in ((_185_878), ([]))))
in (

let un_op = (fun f l -> (let _185_888 = (FStar_List.hd l)
in (FStar_All.pipe_left f _185_888)))
in (

let bin_op = (fun f _89_10 -> (match (_89_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _89_1525 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let _89_1541 = (FStar_Util.fold_map (fun decls _89_1535 -> (match (_89_1535) with
| (t, _89_1534) -> begin
(

let _89_1538 = (encode_formula t env)
in (match (_89_1538) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_89_1541) with
| (decls, phis) -> begin
(let _185_919 = (

let _89_1542 = (f phis)
in {FStar_SMTEncoding_Term.tm = _89_1542.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _89_1542.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_185_919), (decls)))
end)))
in (

let eq_op = (fun r _89_11 -> (match (_89_11) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r l)
end))
in (

let mk_imp = (fun r _89_12 -> (match (_89_12) with
| ((lhs, _89_1567))::((rhs, _89_1563))::[] -> begin
(

let _89_1572 = (encode_formula rhs env)
in (match (_89_1572) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _89_1575) -> begin
((l1), (decls1))
end
| _89_1579 -> begin
(

let _89_1582 = (encode_formula lhs env)
in (match (_89_1582) with
| (l2, decls2) -> begin
(let _185_936 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((_185_936), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _89_1584 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun r _89_13 -> (match (_89_13) with
| ((guard, _89_1598))::((_then, _89_1594))::((_else, _89_1590))::[] -> begin
(

let _89_1603 = (encode_formula guard env)
in (match (_89_1603) with
| (g, decls1) -> begin
(

let _89_1606 = (encode_formula _then env)
in (match (_89_1606) with
| (t, decls2) -> begin
(

let _89_1609 = (encode_formula _else env)
in (match (_89_1609) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _89_1612 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _185_954 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _185_954)))
in (

let connectives = (let _185_1057 = (let _185_970 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_185_970)))
in (let _185_1056 = (let _185_1055 = (let _185_980 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (_185_980)))
in (let _185_1054 = (let _185_1053 = (let _185_1052 = (let _185_998 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_185_998)))
in (let _185_1051 = (let _185_1050 = (let _185_1049 = (let _185_1016 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (_185_1016)))
in (_185_1049)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_185_1050)
in (_185_1052)::_185_1051))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_185_1053)
in (_185_1055)::_185_1054))
in (_185_1057)::_185_1056))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _89_1629 = (encode_formula phi' env)
in (match (_89_1629) with
| (phi, decls) -> begin
(let _185_1060 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((_185_1060), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_89_1631) -> begin
(let _185_1061 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _185_1061 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _89_1639 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (_89_1639) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _89_1646; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _89_1643; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _89_1657 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_89_1657) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_89_1674)::((x, _89_1671))::((t, _89_1667))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _89_1679 = (encode_term x env)
in (match (_89_1679) with
| (x, decls) -> begin
(

let _89_1682 = (encode_term t env)
in (match (_89_1682) with
| (t, decls') -> begin
(let _185_1062 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_185_1062), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _89_1695))::((msg, _89_1691))::((phi, _89_1687))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _185_1066 = (let _185_1063 = (FStar_Syntax_Subst.compress r)
in _185_1063.FStar_Syntax_Syntax.n)
in (let _185_1065 = (let _185_1064 = (FStar_Syntax_Subst.compress msg)
in _185_1064.FStar_Syntax_Syntax.n)
in ((_185_1066), (_185_1065))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _89_1704))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _89_1711 -> begin
(fallback phi)
end)
end
| _89_1713 when (head_redex env head) -> begin
(let _185_1067 = (whnf env phi)
in (encode_formula _185_1067 env))
end
| _89_1715 -> begin
(

let _89_1718 = (encode_term phi env)
in (match (_89_1718) with
| (tt, decls) -> begin
(let _185_1068 = (FStar_SMTEncoding_Term.mk_Valid (

let _89_1719 = tt
in {FStar_SMTEncoding_Term.tm = _89_1719.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _89_1719.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_185_1068), (decls)))
end))
end))
end
| _89_1722 -> begin
(

let _89_1725 = (encode_term phi env)
in (match (_89_1725) with
| (tt, decls) -> begin
(let _185_1069 = (FStar_SMTEncoding_Term.mk_Valid (

let _89_1726 = tt
in {FStar_SMTEncoding_Term.tm = _89_1726.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _89_1726.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_185_1069), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _89_1739 = (encode_binders None bs env)
in (match (_89_1739) with
| (vars, guards, env, decls, _89_1738) -> begin
(

let _89_1752 = (let _185_1081 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _89_1749 = (let _185_1080 = (FStar_All.pipe_right p (FStar_List.map (fun _89_1744 -> (match (_89_1744) with
| (t, _89_1743) -> begin
(encode_term t (

let _89_1745 = env
in {bindings = _89_1745.bindings; depth = _89_1745.depth; tcenv = _89_1745.tcenv; warn = _89_1745.warn; cache = _89_1745.cache; nolabels = _89_1745.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _89_1745.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _185_1080 FStar_List.unzip))
in (match (_89_1749) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _185_1081 FStar_List.unzip))
in (match (_89_1752) with
| (pats, decls') -> begin
(

let _89_1755 = (encode_formula body env)
in (match (_89_1755) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = _89_1759; FStar_SMTEncoding_Term.rng = _89_1757})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _89_1770 -> begin
guards
end)
in (let _185_1082 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (_185_1082), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _89_1772 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _89_1781 -> (match (_89_1781) with
| (x, _89_1780) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _185_1091 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _185_1090 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _185_1090))) _185_1091 tl))
in (match ((FStar_All.pipe_right vars (FStar_Util.find_opt (fun _89_1793 -> (match (_89_1793) with
| (b, _89_1792) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _89_1797) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _185_1096 = (let _185_1095 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _185_1095))
in (FStar_TypeChecker_Errors.warn pos _185_1096)))
end))
end)))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _89_1812 -> (match (_89_1812) with
| (l, _89_1811) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_89_1815, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _89_1825 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _89_1832 = (encode_q_body env vars pats body)
in (match (_89_1832) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _185_1129 = (let _185_1128 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (_185_1128)))
in (FStar_SMTEncoding_Term.mkForall _185_1129 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _89_1840 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _89_1847 = (encode_q_body env vars pats body)
in (match (_89_1847) with
| (vars, pats, guard, body, decls) -> begin
(let _185_1132 = (let _185_1131 = (let _185_1130 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (_185_1130)))
in (FStar_SMTEncoding_Term.mkExists _185_1131 phi.FStar_Syntax_Syntax.pos))
in ((_185_1132), (decls)))
end)))
end))))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _89_1853 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_89_1853) with
| (asym, a) -> begin
(

let _89_1856 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_89_1856) with
| (xsym, x) -> begin
(

let _89_1859 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_89_1859) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (let _185_1169 = (let _185_1168 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_185_1168), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_185_1169))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _185_1171 = (let _185_1170 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (_185_1170)))
in (FStar_SMTEncoding_Util.mkApp _185_1171))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _185_1185 = (let _185_1184 = (let _185_1183 = (let _185_1182 = (let _185_1175 = (let _185_1174 = (let _185_1173 = (let _185_1172 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_185_1172)))
in (FStar_SMTEncoding_Util.mkForall _185_1173))
in ((_185_1174), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_185_1175))
in (let _185_1181 = (let _185_1180 = (let _185_1179 = (let _185_1178 = (let _185_1177 = (let _185_1176 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_185_1176)))
in (FStar_SMTEncoding_Util.mkForall _185_1177))
in ((_185_1178), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_185_1179))
in (_185_1180)::[])
in (_185_1182)::_185_1181))
in (xtok_decl)::_185_1183)
in (xname_decl)::_185_1184)
in ((xtok), (_185_1185))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _185_1345 = (let _185_1194 = (let _185_1193 = (let _185_1192 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1192))
in (quant axy _185_1193))
in ((FStar_Syntax_Const.op_Eq), (_185_1194)))
in (let _185_1344 = (let _185_1343 = (let _185_1201 = (let _185_1200 = (let _185_1199 = (let _185_1198 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot _185_1198))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1199))
in (quant axy _185_1200))
in ((FStar_Syntax_Const.op_notEq), (_185_1201)))
in (let _185_1342 = (let _185_1341 = (let _185_1210 = (let _185_1209 = (let _185_1208 = (let _185_1207 = (let _185_1206 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1205 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1206), (_185_1205))))
in (FStar_SMTEncoding_Util.mkLT _185_1207))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1208))
in (quant xy _185_1209))
in ((FStar_Syntax_Const.op_LT), (_185_1210)))
in (let _185_1340 = (let _185_1339 = (let _185_1219 = (let _185_1218 = (let _185_1217 = (let _185_1216 = (let _185_1215 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1214 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1215), (_185_1214))))
in (FStar_SMTEncoding_Util.mkLTE _185_1216))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1217))
in (quant xy _185_1218))
in ((FStar_Syntax_Const.op_LTE), (_185_1219)))
in (let _185_1338 = (let _185_1337 = (let _185_1228 = (let _185_1227 = (let _185_1226 = (let _185_1225 = (let _185_1224 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1223 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1224), (_185_1223))))
in (FStar_SMTEncoding_Util.mkGT _185_1225))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1226))
in (quant xy _185_1227))
in ((FStar_Syntax_Const.op_GT), (_185_1228)))
in (let _185_1336 = (let _185_1335 = (let _185_1237 = (let _185_1236 = (let _185_1235 = (let _185_1234 = (let _185_1233 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1232 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1233), (_185_1232))))
in (FStar_SMTEncoding_Util.mkGTE _185_1234))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1235))
in (quant xy _185_1236))
in ((FStar_Syntax_Const.op_GTE), (_185_1237)))
in (let _185_1334 = (let _185_1333 = (let _185_1246 = (let _185_1245 = (let _185_1244 = (let _185_1243 = (let _185_1242 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1241 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1242), (_185_1241))))
in (FStar_SMTEncoding_Util.mkSub _185_1243))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _185_1244))
in (quant xy _185_1245))
in ((FStar_Syntax_Const.op_Subtraction), (_185_1246)))
in (let _185_1332 = (let _185_1331 = (let _185_1253 = (let _185_1252 = (let _185_1251 = (let _185_1250 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus _185_1250))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _185_1251))
in (quant qx _185_1252))
in ((FStar_Syntax_Const.op_Minus), (_185_1253)))
in (let _185_1330 = (let _185_1329 = (let _185_1262 = (let _185_1261 = (let _185_1260 = (let _185_1259 = (let _185_1258 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1257 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1258), (_185_1257))))
in (FStar_SMTEncoding_Util.mkAdd _185_1259))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _185_1260))
in (quant xy _185_1261))
in ((FStar_Syntax_Const.op_Addition), (_185_1262)))
in (let _185_1328 = (let _185_1327 = (let _185_1271 = (let _185_1270 = (let _185_1269 = (let _185_1268 = (let _185_1267 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1266 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1267), (_185_1266))))
in (FStar_SMTEncoding_Util.mkMul _185_1268))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _185_1269))
in (quant xy _185_1270))
in ((FStar_Syntax_Const.op_Multiply), (_185_1271)))
in (let _185_1326 = (let _185_1325 = (let _185_1280 = (let _185_1279 = (let _185_1278 = (let _185_1277 = (let _185_1276 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1275 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1276), (_185_1275))))
in (FStar_SMTEncoding_Util.mkDiv _185_1277))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _185_1278))
in (quant xy _185_1279))
in ((FStar_Syntax_Const.op_Division), (_185_1280)))
in (let _185_1324 = (let _185_1323 = (let _185_1289 = (let _185_1288 = (let _185_1287 = (let _185_1286 = (let _185_1285 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1284 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_185_1285), (_185_1284))))
in (FStar_SMTEncoding_Util.mkMod _185_1286))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _185_1287))
in (quant xy _185_1288))
in ((FStar_Syntax_Const.op_Modulus), (_185_1289)))
in (let _185_1322 = (let _185_1321 = (let _185_1298 = (let _185_1297 = (let _185_1296 = (let _185_1295 = (let _185_1294 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _185_1293 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_185_1294), (_185_1293))))
in (FStar_SMTEncoding_Util.mkAnd _185_1295))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1296))
in (quant xy _185_1297))
in ((FStar_Syntax_Const.op_And), (_185_1298)))
in (let _185_1320 = (let _185_1319 = (let _185_1307 = (let _185_1306 = (let _185_1305 = (let _185_1304 = (let _185_1303 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _185_1302 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_185_1303), (_185_1302))))
in (FStar_SMTEncoding_Util.mkOr _185_1304))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1305))
in (quant xy _185_1306))
in ((FStar_Syntax_Const.op_Or), (_185_1307)))
in (let _185_1318 = (let _185_1317 = (let _185_1314 = (let _185_1313 = (let _185_1312 = (let _185_1311 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot _185_1311))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1312))
in (quant qx _185_1313))
in ((FStar_Syntax_Const.op_Negation), (_185_1314)))
in (_185_1317)::[])
in (_185_1319)::_185_1318))
in (_185_1321)::_185_1320))
in (_185_1323)::_185_1322))
in (_185_1325)::_185_1324))
in (_185_1327)::_185_1326))
in (_185_1329)::_185_1328))
in (_185_1331)::_185_1330))
in (_185_1333)::_185_1332))
in (_185_1335)::_185_1334))
in (_185_1337)::_185_1336))
in (_185_1339)::_185_1338))
in (_185_1341)::_185_1340))
in (_185_1343)::_185_1342))
in (_185_1345)::_185_1344))
in (

let mk = (fun l v -> (let _185_1392 = (let _185_1391 = (FStar_All.pipe_right prims (FStar_List.find (fun _89_1879 -> (match (_89_1879) with
| (l', _89_1878) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _185_1391 (FStar_Option.map (fun _89_1883 -> (match (_89_1883) with
| (_89_1881, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _185_1392 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _89_1889 -> (match (_89_1889) with
| (l', _89_1888) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _89_1895 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_89_1895) with
| (xxsym, xx) -> begin
(

let _89_1898 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_89_1898) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (let _185_1422 = (let _185_1421 = (let _185_1416 = (let _185_1415 = (let _185_1414 = (let _185_1413 = (let _185_1412 = (let _185_1411 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_185_1411)))
in (FStar_SMTEncoding_Util.mkEq _185_1412))
in ((xx_has_type), (_185_1413)))
in (FStar_SMTEncoding_Util.mkImp _185_1414))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_185_1415)))
in (FStar_SMTEncoding_Util.mkForall _185_1416))
in (let _185_1420 = (let _185_1419 = (let _185_1418 = (let _185_1417 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" _185_1417))
in (varops.mk_unique _185_1418))
in Some (_185_1419))
in ((_185_1421), (Some ("pretyping")), (_185_1420))))
in FStar_SMTEncoding_Term.Assume (_185_1422))))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _185_1443 = (let _185_1434 = (let _185_1433 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_185_1433), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_185_1434))
in (let _185_1442 = (let _185_1441 = (let _185_1440 = (let _185_1439 = (let _185_1438 = (let _185_1437 = (let _185_1436 = (let _185_1435 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_185_1435)))
in (FStar_SMTEncoding_Util.mkImp _185_1436))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_185_1437)))
in (mkForall_fuel _185_1438))
in ((_185_1439), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_185_1440))
in (_185_1441)::[])
in (_185_1443)::_185_1442))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _185_1466 = (let _185_1457 = (let _185_1456 = (let _185_1455 = (let _185_1454 = (let _185_1451 = (let _185_1450 = (FStar_SMTEncoding_Term.boxBool b)
in (_185_1450)::[])
in (_185_1451)::[])
in (let _185_1453 = (let _185_1452 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _185_1452 tt))
in ((_185_1454), ((bb)::[]), (_185_1453))))
in (FStar_SMTEncoding_Util.mkForall _185_1455))
in ((_185_1456), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_185_1457))
in (let _185_1465 = (let _185_1464 = (let _185_1463 = (let _185_1462 = (let _185_1461 = (let _185_1460 = (let _185_1459 = (let _185_1458 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_185_1458)))
in (FStar_SMTEncoding_Util.mkImp _185_1459))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_185_1460)))
in (mkForall_fuel _185_1461))
in ((_185_1462), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_185_1463))
in (_185_1464)::[])
in (_185_1466)::_185_1465))))))
in (

let mk_int = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let precedes = (let _185_1480 = (let _185_1479 = (let _185_1478 = (let _185_1477 = (let _185_1476 = (let _185_1475 = (FStar_SMTEncoding_Term.boxInt a)
in (let _185_1474 = (let _185_1473 = (FStar_SMTEncoding_Term.boxInt b)
in (_185_1473)::[])
in (_185_1475)::_185_1474))
in (tt)::_185_1476)
in (tt)::_185_1477)
in (("Prims.Precedes"), (_185_1478)))
in (FStar_SMTEncoding_Util.mkApp _185_1479))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _185_1480))
in (

let precedes_y_x = (let _185_1481 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _185_1481))
in (let _185_1523 = (let _185_1489 = (let _185_1488 = (let _185_1487 = (let _185_1486 = (let _185_1483 = (let _185_1482 = (FStar_SMTEncoding_Term.boxInt b)
in (_185_1482)::[])
in (_185_1483)::[])
in (let _185_1485 = (let _185_1484 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _185_1484 tt))
in ((_185_1486), ((bb)::[]), (_185_1485))))
in (FStar_SMTEncoding_Util.mkForall _185_1487))
in ((_185_1488), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_185_1489))
in (let _185_1522 = (let _185_1521 = (let _185_1495 = (let _185_1494 = (let _185_1493 = (let _185_1492 = (let _185_1491 = (let _185_1490 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_185_1490)))
in (FStar_SMTEncoding_Util.mkImp _185_1491))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_185_1492)))
in (mkForall_fuel _185_1493))
in ((_185_1494), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_185_1495))
in (let _185_1520 = (let _185_1519 = (let _185_1518 = (let _185_1517 = (let _185_1516 = (let _185_1515 = (let _185_1514 = (let _185_1513 = (let _185_1512 = (let _185_1511 = (let _185_1510 = (let _185_1509 = (let _185_1498 = (let _185_1497 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _185_1496 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_185_1497), (_185_1496))))
in (FStar_SMTEncoding_Util.mkGT _185_1498))
in (let _185_1508 = (let _185_1507 = (let _185_1501 = (let _185_1500 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _185_1499 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_185_1500), (_185_1499))))
in (FStar_SMTEncoding_Util.mkGTE _185_1501))
in (let _185_1506 = (let _185_1505 = (let _185_1504 = (let _185_1503 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _185_1502 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_185_1503), (_185_1502))))
in (FStar_SMTEncoding_Util.mkLT _185_1504))
in (_185_1505)::[])
in (_185_1507)::_185_1506))
in (_185_1509)::_185_1508))
in (typing_pred_y)::_185_1510)
in (typing_pred)::_185_1511)
in (FStar_SMTEncoding_Util.mk_and_l _185_1512))
in ((_185_1513), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp _185_1514))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_185_1515)))
in (mkForall_fuel _185_1516))
in ((_185_1517), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_185_1518))
in (_185_1519)::[])
in (_185_1521)::_185_1520))
in (_185_1523)::_185_1522)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _185_1546 = (let _185_1537 = (let _185_1536 = (let _185_1535 = (let _185_1534 = (let _185_1531 = (let _185_1530 = (FStar_SMTEncoding_Term.boxString b)
in (_185_1530)::[])
in (_185_1531)::[])
in (let _185_1533 = (let _185_1532 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _185_1532 tt))
in ((_185_1534), ((bb)::[]), (_185_1533))))
in (FStar_SMTEncoding_Util.mkForall _185_1535))
in ((_185_1536), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_185_1537))
in (let _185_1545 = (let _185_1544 = (let _185_1543 = (let _185_1542 = (let _185_1541 = (let _185_1540 = (let _185_1539 = (let _185_1538 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_185_1538)))
in (FStar_SMTEncoding_Util.mkImp _185_1539))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_185_1540)))
in (mkForall_fuel _185_1541))
in ((_185_1542), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_185_1543))
in (_185_1544)::[])
in (_185_1546)::_185_1545))))))
in (

let mk_ref = (fun env reft_name _89_1938 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _185_1555 = (let _185_1554 = (let _185_1553 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (_185_1553)::[])
in ((reft_name), (_185_1554)))
in (FStar_SMTEncoding_Util.mkApp _185_1555))
in (

let refb = (let _185_1558 = (let _185_1557 = (let _185_1556 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (_185_1556)::[])
in ((reft_name), (_185_1557)))
in (FStar_SMTEncoding_Util.mkApp _185_1558))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _185_1577 = (let _185_1564 = (let _185_1563 = (let _185_1562 = (let _185_1561 = (let _185_1560 = (let _185_1559 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_185_1559)))
in (FStar_SMTEncoding_Util.mkImp _185_1560))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_185_1561)))
in (mkForall_fuel _185_1562))
in ((_185_1563), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_185_1564))
in (let _185_1576 = (let _185_1575 = (let _185_1574 = (let _185_1573 = (let _185_1572 = (let _185_1571 = (let _185_1570 = (let _185_1569 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (let _185_1568 = (let _185_1567 = (let _185_1566 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (let _185_1565 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((_185_1566), (_185_1565))))
in (FStar_SMTEncoding_Util.mkEq _185_1567))
in ((_185_1569), (_185_1568))))
in (FStar_SMTEncoding_Util.mkImp _185_1570))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_185_1571)))
in (mkForall_fuel' (Prims.parse_int "2") _185_1572))
in ((_185_1573), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_185_1574))
in (_185_1575)::[])
in (_185_1577)::_185_1576))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (let _185_1592 = (let _185_1591 = (let _185_1590 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((_185_1590), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1591))
in (_185_1592)::[])))
in (

let mk_and_interp = (fun env conj _89_1960 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _185_1601 = (let _185_1600 = (let _185_1599 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (_185_1599)::[])
in (("Valid"), (_185_1600)))
in (FStar_SMTEncoding_Util.mkApp _185_1601))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _185_1608 = (let _185_1607 = (let _185_1606 = (let _185_1605 = (let _185_1604 = (let _185_1603 = (let _185_1602 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((_185_1602), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1603))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_185_1604)))
in (FStar_SMTEncoding_Util.mkForall _185_1605))
in ((_185_1606), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1607))
in (_185_1608)::[])))))))))
in (

let mk_or_interp = (fun env disj _89_1972 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _185_1617 = (let _185_1616 = (let _185_1615 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (_185_1615)::[])
in (("Valid"), (_185_1616)))
in (FStar_SMTEncoding_Util.mkApp _185_1617))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _185_1624 = (let _185_1623 = (let _185_1622 = (let _185_1621 = (let _185_1620 = (let _185_1619 = (let _185_1618 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((_185_1618), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1619))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_185_1620)))
in (FStar_SMTEncoding_Util.mkForall _185_1621))
in ((_185_1622), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1623))
in (_185_1624)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (let _185_1633 = (let _185_1632 = (let _185_1631 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_185_1631)::[])
in (("Valid"), (_185_1632)))
in (FStar_SMTEncoding_Util.mkApp _185_1633))
in (let _185_1640 = (let _185_1639 = (let _185_1638 = (let _185_1637 = (let _185_1636 = (let _185_1635 = (let _185_1634 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_185_1634), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1635))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_185_1636)))
in (FStar_SMTEncoding_Util.mkForall _185_1637))
in ((_185_1638), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1639))
in (_185_1640)::[])))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (let _185_1649 = (let _185_1648 = (let _185_1647 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_185_1647)::[])
in (("Valid"), (_185_1648)))
in (FStar_SMTEncoding_Util.mkApp _185_1649))
in (let _185_1656 = (let _185_1655 = (let _185_1654 = (let _185_1653 = (let _185_1652 = (let _185_1651 = (let _185_1650 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_185_1650), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1651))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_185_1652)))
in (FStar_SMTEncoding_Util.mkForall _185_1653))
in ((_185_1654), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1655))
in (_185_1656)::[])))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _185_1665 = (let _185_1664 = (let _185_1663 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (_185_1663)::[])
in (("Valid"), (_185_1664)))
in (FStar_SMTEncoding_Util.mkApp _185_1665))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _185_1672 = (let _185_1671 = (let _185_1670 = (let _185_1669 = (let _185_1668 = (let _185_1667 = (let _185_1666 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((_185_1666), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1667))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_185_1668)))
in (FStar_SMTEncoding_Util.mkForall _185_1669))
in ((_185_1670), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1671))
in (_185_1672)::[])))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _185_1681 = (let _185_1680 = (let _185_1679 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (_185_1679)::[])
in (("Valid"), (_185_1680)))
in (FStar_SMTEncoding_Util.mkApp _185_1681))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _185_1688 = (let _185_1687 = (let _185_1686 = (let _185_1685 = (let _185_1684 = (let _185_1683 = (let _185_1682 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((_185_1682), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1683))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_185_1684)))
in (FStar_SMTEncoding_Util.mkForall _185_1685))
in ((_185_1686), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1687))
in (_185_1688)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (let _185_1697 = (let _185_1696 = (let _185_1695 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (_185_1695)::[])
in (("Valid"), (_185_1696)))
in (FStar_SMTEncoding_Util.mkApp _185_1697))
in (

let not_valid_a = (let _185_1698 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _185_1698))
in (let _185_1703 = (let _185_1702 = (let _185_1701 = (let _185_1700 = (let _185_1699 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_185_1699)))
in (FStar_SMTEncoding_Util.mkForall _185_1700))
in ((_185_1701), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1702))
in (_185_1703)::[]))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (let _185_1712 = (let _185_1711 = (let _185_1710 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (_185_1710)::[])
in (("Valid"), (_185_1711)))
in (FStar_SMTEncoding_Util.mkApp _185_1712))
in (

let valid_b_x = (let _185_1715 = (let _185_1714 = (let _185_1713 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_185_1713)::[])
in (("Valid"), (_185_1714)))
in (FStar_SMTEncoding_Util.mkApp _185_1715))
in (let _185_1729 = (let _185_1728 = (let _185_1727 = (let _185_1726 = (let _185_1725 = (let _185_1724 = (let _185_1723 = (let _185_1722 = (let _185_1721 = (let _185_1717 = (let _185_1716 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_185_1716)::[])
in (_185_1717)::[])
in (let _185_1720 = (let _185_1719 = (let _185_1718 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_185_1718), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _185_1719))
in ((_185_1721), ((xx)::[]), (_185_1720))))
in (FStar_SMTEncoding_Util.mkForall _185_1722))
in ((_185_1723), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1724))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_185_1725)))
in (FStar_SMTEncoding_Util.mkForall _185_1726))
in ((_185_1727), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1728))
in (_185_1729)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (let _185_1738 = (let _185_1737 = (let _185_1736 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (_185_1736)::[])
in (("Valid"), (_185_1737)))
in (FStar_SMTEncoding_Util.mkApp _185_1738))
in (

let valid_b_x = (let _185_1741 = (let _185_1740 = (let _185_1739 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_185_1739)::[])
in (("Valid"), (_185_1740)))
in (FStar_SMTEncoding_Util.mkApp _185_1741))
in (let _185_1755 = (let _185_1754 = (let _185_1753 = (let _185_1752 = (let _185_1751 = (let _185_1750 = (let _185_1749 = (let _185_1748 = (let _185_1747 = (let _185_1743 = (let _185_1742 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_185_1742)::[])
in (_185_1743)::[])
in (let _185_1746 = (let _185_1745 = (let _185_1744 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_185_1744), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _185_1745))
in ((_185_1747), ((xx)::[]), (_185_1746))))
in (FStar_SMTEncoding_Util.mkExists _185_1748))
in ((_185_1749), (valid)))
in (FStar_SMTEncoding_Util.mkIff _185_1750))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_185_1751)))
in (FStar_SMTEncoding_Util.mkForall _185_1752))
in ((_185_1753), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_185_1754))
in (_185_1755)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (let _185_1766 = (let _185_1765 = (let _185_1764 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _185_1763 = (let _185_1762 = (varops.mk_unique "typing_range_const")
in Some (_185_1762))
in ((_185_1764), (Some ("Range_const typing")), (_185_1763))))
in FStar_SMTEncoding_Term.Assume (_185_1765))
in (_185_1766)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _89_2073 -> (match (_89_2073) with
| (l, _89_2072) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_89_2076, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _89_2086 = (encode_function_type_as_formula None None t env)
in (match (_89_2086) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _185_1983 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _185_1983)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _89_2096 = (new_term_constant_and_tok_from_lid env lid)
in (match (_89_2096) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _185_1984 = (FStar_Syntax_Subst.compress t_norm)
in _185_1984.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _89_2099) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _89_2102 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _89_2105 -> begin
[]
end)
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let _89_2112 = (prims.mk lid vname)
in (match (_89_2112) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _89_2122 = (

let _89_2117 = (curried_arrow_formals_comp t_norm)
in (match (_89_2117) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _185_1986 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_185_1986)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_89_2122) with
| (formals, (pre_opt, res_t)) -> begin
(

let _89_2126 = (new_term_constant_and_tok_from_lid env lid)
in (match (_89_2126) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _89_2129 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _89_14 -> (match (_89_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _89_2145 = (FStar_Util.prefix vars)
in (match (_89_2145) with
| (_89_2140, (xxsym, _89_2143)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _185_2003 = (let _185_2002 = (let _185_2001 = (let _185_2000 = (let _185_1999 = (let _185_1998 = (let _185_1997 = (let _185_1996 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _185_1996))
in ((vapp), (_185_1997)))
in (FStar_SMTEncoding_Util.mkEq _185_1998))
in ((((vapp)::[])::[]), (vars), (_185_1999)))
in (FStar_SMTEncoding_Util.mkForall _185_2000))
in ((_185_2001), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_185_2002))
in (_185_2003)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _89_2157 = (FStar_Util.prefix vars)
in (match (_89_2157) with
| (_89_2152, (xxsym, _89_2155)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (let _185_2008 = (let _185_2007 = (let _185_2006 = (let _185_2005 = (let _185_2004 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_185_2004)))
in (FStar_SMTEncoding_Util.mkForall _185_2005))
in ((_185_2006), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_185_2007))
in (_185_2008)::[])))))
end))
end
| _89_2163 -> begin
[]
end)))))
in (

let _89_2170 = (encode_binders None formals env)
in (match (_89_2170) with
| (vars, guards, env', decls1, _89_2169) -> begin
(

let _89_2179 = (match (pre_opt) with
| None -> begin
(let _185_2009 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_185_2009), (decls1)))
end
| Some (p) -> begin
(

let _89_2176 = (encode_formula p env')
in (match (_89_2176) with
| (g, ds) -> begin
(let _185_2010 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((_185_2010), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_89_2179) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _185_2012 = (let _185_2011 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (_185_2011)))
in (FStar_SMTEncoding_Util.mkApp _185_2012))
in (

let _89_2203 = (

let vname_decl = (let _185_2015 = (let _185_2014 = (FStar_All.pipe_right formals (FStar_List.map (fun _89_2182 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_185_2014), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_185_2015))
in (

let _89_2190 = (

let env = (

let _89_2185 = env
in {bindings = _89_2185.bindings; depth = _89_2185.depth; tcenv = _89_2185.tcenv; warn = _89_2185.warn; cache = _89_2185.cache; nolabels = _89_2185.nolabels; use_zfuel_name = _89_2185.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_89_2190) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _89_2200 = (match (formals) with
| [] -> begin
(let _185_2019 = (let _185_2018 = (let _185_2017 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _185_2016 -> Some (_185_2016)) _185_2017))
in (push_free_var env lid vname _185_2018))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_185_2019)))
end
| _89_2194 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _185_2020 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _185_2020))
in (

let name_tok_corr = (let _185_2024 = (let _185_2023 = (let _185_2022 = (let _185_2021 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_185_2021)))
in (FStar_SMTEncoding_Util.mkForall _185_2022))
in ((_185_2023), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_185_2024))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_89_2200) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_89_2203) with
| (decls2, env) -> begin
(

let _89_2211 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _89_2207 = (encode_term res_t env')
in (match (_89_2207) with
| (encoded_res_t, decls) -> begin
(let _185_2025 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_185_2025), (decls)))
end)))
in (match (_89_2211) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _185_2029 = (let _185_2028 = (let _185_2027 = (let _185_2026 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_185_2026)))
in (FStar_SMTEncoding_Util.mkForall _185_2027))
in ((_185_2028), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_185_2029))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _185_2035 = (let _185_2032 = (let _185_2031 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _185_2030 = (varops.next_id ())
in ((vname), (_185_2031), (FStar_SMTEncoding_Term.Term_sort), (_185_2030))))
in (FStar_SMTEncoding_Term.fresh_constructor _185_2032))
in (let _185_2034 = (let _185_2033 = (pretype_axiom vapp vars)
in (_185_2033)::[])
in (_185_2035)::_185_2034))
end else begin
[]
end
in (

let g = (let _185_2040 = (let _185_2039 = (let _185_2038 = (let _185_2037 = (let _185_2036 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_185_2036)
in (FStar_List.append freshness _185_2037))
in (FStar_List.append decls3 _185_2038))
in (FStar_List.append decls2 _185_2039))
in (FStar_List.append decls1 _185_2040))
in ((g), (env)))))
end))
end))))
end))
end))))
end))
end)))
end
end))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(

let _89_2222 = (encode_free_var env x t t_norm [])
in (match (_89_2222) with
| (decls, env) -> begin
(

let _89_2227 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_89_2227) with
| (n, x', _89_2226) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _89_2231) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _89_2241 = (encode_free_var env lid t tt quals)
in (match (_89_2241) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _185_2058 = (let _185_2057 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _185_2057))
in ((_185_2058), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _89_2247 lb -> (match (_89_2247) with
| (decls, env) -> begin
(

let _89_2251 = (let _185_2067 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _185_2067 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_89_2251) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _89_2255 quals -> (match (_89_2255) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _89_2265 = (FStar_Util.first_N nbinders formals)
in (match (_89_2265) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _89_2269 _89_2273 -> (match (((_89_2269), (_89_2273))) with
| ((formal, _89_2268), (binder, _89_2272)) -> begin
(let _185_2085 = (let _185_2084 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_185_2084)))
in FStar_Syntax_Syntax.NT (_185_2085))
end)) formals binders)
in (

let extra_formals = (let _185_2089 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _89_2277 -> (match (_89_2277) with
| (x, i) -> begin
(let _185_2088 = (

let _89_2278 = x
in (let _185_2087 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _89_2278.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _89_2278.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _185_2087}))
in ((_185_2088), (i)))
end))))
in (FStar_All.pipe_right _185_2089 FStar_Syntax_Util.name_binders))
in (

let body = (let _185_2096 = (FStar_Syntax_Subst.compress body)
in (let _185_2095 = (let _185_2090 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _185_2090))
in (let _185_2094 = (let _185_2093 = (let _185_2092 = (FStar_Syntax_Subst.subst subst t)
in _185_2092.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _185_2091 -> Some (_185_2091)) _185_2093))
in (FStar_Syntax_Syntax.extend_app_n _185_2096 _185_2095 _185_2094 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _185_2107 = (FStar_Syntax_Util.unascribe e)
in _185_2107.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _89_2297 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_89_2297) with
| (binders, body, opening) -> begin
(match ((let _185_2108 = (FStar_Syntax_Subst.compress t_norm)
in _185_2108.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _89_2304 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_89_2304) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(

let lopt = (subst_lcomp_opt opening lopt)
in (

let _89_2311 = (FStar_Util.first_N nformals binders)
in (match (_89_2311) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _89_2315 _89_2319 -> (match (((_89_2315), (_89_2319))) with
| ((b, _89_2314), (x, _89_2318)) -> begin
(let _185_2112 = (let _185_2111 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_185_2111)))
in FStar_Syntax_Syntax.NT (_185_2112))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _89_2325 = (eta_expand binders formals body tres)
in (match (_89_2325) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end else begin
((((binders), (body), (formals), (tres))), (false))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _89_2328) -> begin
(let _185_2114 = (let _185_2113 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst _185_2113))
in ((_185_2114), (true)))
end
| _89_2332 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _89_2335 -> begin
(let _185_2117 = (let _185_2116 = (FStar_Syntax_Print.term_to_string e)
in (let _185_2115 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _185_2116 _185_2115)))
in (FStar_All.failwith _185_2117))
end)
end))
end
| _89_2337 -> begin
(match ((let _185_2118 = (FStar_Syntax_Subst.compress t_norm)
in _185_2118.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _89_2344 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_89_2344) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _89_2348 = (eta_expand [] formals e tres)
in (match (_89_2348) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| _89_2350 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end)
end))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(

let _89_2378 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _89_2365 lb -> (match (_89_2365) with
| (toks, typs, decls, env) -> begin
(

let _89_2367 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _89_2373 = (let _185_2123 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _185_2123 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_89_2373) with
| (tok, decl, env) -> begin
(let _185_2126 = (let _185_2125 = (let _185_2124 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_185_2124), (tok)))
in (_185_2125)::toks)
in ((_185_2126), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_89_2378) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in (

let mk_app = (fun curry f ftok vars -> (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _89_2389 -> begin
if curry then begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _185_2135 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _185_2135 vars))
end)
end else begin
(let _185_2137 = (let _185_2136 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_185_2136)))
in (FStar_SMTEncoding_Util.mkApp _185_2137))
end
end))
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _89_15 -> (match (_89_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _89_2396 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _185_2140 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _185_2140)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _89_2406; FStar_Syntax_Syntax.lbunivs = _89_2404; FStar_Syntax_Syntax.lbtyp = _89_2402; FStar_Syntax_Syntax.lbeff = _89_2400; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _89_2428 = (destruct_bound_function flid t_norm e)
in (match (_89_2428) with
| ((binders, body, _89_2423, _89_2425), curry) -> begin
(

let _89_2435 = (encode_binders None binders env)
in (match (_89_2435) with
| (vars, guards, env', binder_decls, _89_2434) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let _89_2441 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _185_2142 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _185_2141 = (encode_formula body env')
in ((_185_2142), (_185_2141))))
end else begin
(let _185_2143 = (encode_term body env')
in ((app), (_185_2143)))
end
in (match (_89_2441) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _185_2149 = (let _185_2148 = (let _185_2145 = (let _185_2144 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_185_2144)))
in (FStar_SMTEncoding_Util.mkForall _185_2145))
in (let _185_2147 = (let _185_2146 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_185_2146))
in ((_185_2148), (_185_2147), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_185_2149))
in (let _185_2154 = (let _185_2153 = (let _185_2152 = (let _185_2151 = (let _185_2150 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _185_2150))
in (FStar_List.append decls2 _185_2151))
in (FStar_List.append binder_decls _185_2152))
in (FStar_List.append decls _185_2153))
in ((_185_2154), (env))))
end)))
end))
end))))
end
| _89_2444 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _185_2155 = (varops.fresh "fuel")
in ((_185_2155), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let _89_2462 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _89_2450 _89_2455 -> (match (((_89_2450), (_89_2455))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _185_2158 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _185_2158))
in (

let gtok = (let _185_2159 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _185_2159))
in (

let env = (let _185_2162 = (let _185_2161 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _185_2160 -> Some (_185_2160)) _185_2161))
in (push_free_var env flid gtok _185_2162))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_89_2462) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _89_2471 t_norm _89_2482 -> (match (((_89_2471), (_89_2482))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _89_2481; FStar_Syntax_Syntax.lbunivs = _89_2479; FStar_Syntax_Syntax.lbtyp = _89_2477; FStar_Syntax_Syntax.lbeff = _89_2475; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _89_2489 = (destruct_bound_function flid t_norm e)
in (match (_89_2489) with
| ((binders, body, formals, tres), curry) -> begin
(

let _89_2490 = if curry then begin
(FStar_All.failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end else begin
()
end
in (

let _89_2498 = (encode_binders None binders env)
in (match (_89_2498) with
| (vars, guards, env', binder_decls, _89_2497) -> begin
(

let decl_g = (let _185_2173 = (let _185_2172 = (let _185_2171 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_185_2171)
in ((g), (_185_2172), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_185_2173))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (let _185_2175 = (let _185_2174 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_185_2174)))
in (FStar_SMTEncoding_Util.mkApp _185_2175))
in (

let gsapp = (let _185_2178 = (let _185_2177 = (let _185_2176 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_185_2176)::vars_tm)
in ((g), (_185_2177)))
in (FStar_SMTEncoding_Util.mkApp _185_2178))
in (

let gmax = (let _185_2181 = (let _185_2180 = (let _185_2179 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (_185_2179)::vars_tm)
in ((g), (_185_2180)))
in (FStar_SMTEncoding_Util.mkApp _185_2181))
in (

let _89_2508 = (encode_term body env')
in (match (_89_2508) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _185_2187 = (let _185_2186 = (let _185_2183 = (let _185_2182 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_185_2182)))
in (FStar_SMTEncoding_Util.mkForall' _185_2183))
in (let _185_2185 = (let _185_2184 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_185_2184))
in ((_185_2186), (_185_2185), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_185_2187))
in (

let eqn_f = (let _185_2191 = (let _185_2190 = (let _185_2189 = (let _185_2188 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_185_2188)))
in (FStar_SMTEncoding_Util.mkForall _185_2189))
in ((_185_2190), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_185_2191))
in (

let eqn_g' = (let _185_2200 = (let _185_2199 = (let _185_2198 = (let _185_2197 = (let _185_2196 = (let _185_2195 = (let _185_2194 = (let _185_2193 = (let _185_2192 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_185_2192)::vars_tm)
in ((g), (_185_2193)))
in (FStar_SMTEncoding_Util.mkApp _185_2194))
in ((gsapp), (_185_2195)))
in (FStar_SMTEncoding_Util.mkEq _185_2196))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_185_2197)))
in (FStar_SMTEncoding_Util.mkForall _185_2198))
in ((_185_2199), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_185_2200))
in (

let _89_2531 = (

let _89_2518 = (encode_binders None formals env0)
in (match (_89_2518) with
| (vars, v_guards, env, binder_decls, _89_2517) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _185_2201 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _185_2201 ((fuel)::vars)))
in (let _185_2205 = (let _185_2204 = (let _185_2203 = (let _185_2202 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_185_2202)))
in (FStar_SMTEncoding_Util.mkForall _185_2203))
in ((_185_2204), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_185_2205)))
in (

let _89_2528 = (

let _89_2525 = (encode_term_pred None tres env gapp)
in (match (_89_2525) with
| (g_typing, d3) -> begin
(let _185_2213 = (let _185_2212 = (let _185_2211 = (let _185_2210 = (let _185_2209 = (let _185_2208 = (let _185_2207 = (let _185_2206 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((_185_2206), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp _185_2207))
in ((((gapp)::[])::[]), ((fuel)::vars), (_185_2208)))
in (FStar_SMTEncoding_Util.mkForall _185_2209))
in ((_185_2210), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_185_2211))
in (_185_2212)::[])
in ((d3), (_185_2213)))
end))
in (match (_89_2528) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_89_2531) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end)))
end))
end))
in (

let _89_2547 = (let _185_2216 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _89_2535 _89_2539 -> (match (((_89_2535), (_89_2539))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _89_2543 = (encode_one_binding env0 gtok ty bs)
in (match (_89_2543) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _185_2216))
in (match (_89_2547) with
| (decls, eqns, env0) -> begin
(

let _89_2556 = (let _185_2218 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _185_2218 (FStar_List.partition (fun _89_16 -> (match (_89_16) with
| FStar_SMTEncoding_Term.DeclFun (_89_2550) -> begin
true
end
| _89_2553 -> begin
false
end)))))
in (match (_89_2556) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
end))
end))))
end)))))
end
end))))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _185_2221 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _185_2221 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _89_2560 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _185_2230 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _185_2230))
end else begin
()
end
in (

let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let _89_2568 = (encode_sigelt' env se)
in (match (_89_2568) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _185_2233 = (let _185_2232 = (let _185_2231 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_185_2231))
in (_185_2232)::[])
in ((_185_2233), (e)))
end
| _89_2571 -> begin
(let _185_2240 = (let _185_2239 = (let _185_2235 = (let _185_2234 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_185_2234))
in (_185_2235)::g)
in (let _185_2238 = (let _185_2237 = (let _185_2236 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_185_2236))
in (_185_2237)::[])
in (FStar_List.append _185_2239 _185_2238)))
in ((_185_2240), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_89_2577) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _89_2593) -> begin
if (let _185_2245 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _185_2245 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _89_2600 -> begin
(let _185_2251 = (let _185_2250 = (let _185_2249 = (FStar_All.pipe_left (fun _185_2248 -> Some (_185_2248)) (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_185_2249)))
in FStar_Syntax_Syntax.Tm_abs (_185_2250))
in (FStar_Syntax_Syntax.mk _185_2251 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _89_2607 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_89_2607) with
| (aname, atok, env) -> begin
(

let _89_2611 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_89_2611) with
| (formals, _89_2610) -> begin
(

let _89_2614 = (let _185_2256 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _185_2256 env))
in (match (_89_2614) with
| (tm, decls) -> begin
(

let a_decls = (let _185_2260 = (let _185_2259 = (let _185_2258 = (FStar_All.pipe_right formals (FStar_List.map (fun _89_2615 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_185_2258), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_185_2259))
in (_185_2260)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _89_2629 = (let _185_2262 = (FStar_All.pipe_right formals (FStar_List.map (fun _89_2621 -> (match (_89_2621) with
| (bv, _89_2620) -> begin
(

let _89_2626 = (gen_term_var env bv)
in (match (_89_2626) with
| (xxsym, xx, _89_2625) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _185_2262 FStar_List.split))
in (match (_89_2629) with
| (xs_sorts, xs) -> begin
(

let app = (let _185_2265 = (let _185_2264 = (let _185_2263 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (_185_2263)::[])
in (("Reify"), (_185_2264)))
in (FStar_SMTEncoding_Util.mkApp _185_2265))
in (

let a_eq = (let _185_2271 = (let _185_2270 = (let _185_2269 = (let _185_2268 = (let _185_2267 = (let _185_2266 = (mk_Apply tm xs_sorts)
in ((app), (_185_2266)))
in (FStar_SMTEncoding_Util.mkEq _185_2267))
in ((((app)::[])::[]), (xs_sorts), (_185_2268)))
in (FStar_SMTEncoding_Util.mkForall _185_2269))
in ((_185_2270), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_185_2271))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _185_2275 = (let _185_2274 = (let _185_2273 = (let _185_2272 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_185_2272)))
in (FStar_SMTEncoding_Util.mkForall _185_2273))
in ((_185_2274), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_185_2275))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _89_2637 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_89_2637) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _89_2640, _89_2642, _89_2644, _89_2646) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _89_2652 = (new_term_constant_and_tok_from_lid env lid)
in (match (_89_2652) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _89_2655, t, quals, _89_2659) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _89_17 -> (match (_89_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _89_2672 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _89_2677 = (encode_top_level_val env fv t quals)
in (match (_89_2677) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _185_2278 = (let _185_2277 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _185_2277))
in ((_185_2278), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _89_2683, _89_2685) -> begin
(

let _89_2690 = (encode_formula f env)
in (match (_89_2690) with
| (f, decls) -> begin
(

let g = (let _185_2285 = (let _185_2284 = (let _185_2283 = (let _185_2280 = (let _185_2279 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _185_2279))
in Some (_185_2280))
in (let _185_2282 = (let _185_2281 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_185_2281))
in ((f), (_185_2283), (_185_2282))))
in FStar_SMTEncoding_Term.Assume (_185_2284))
in (_185_2285)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _89_2695, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _89_2708 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _185_2289 = (let _185_2288 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _185_2288.FStar_Syntax_Syntax.fv_name)
in _185_2289.FStar_Syntax_Syntax.v)
in if (let _185_2290 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _185_2290)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _89_2705 = (encode_sigelt' env val_decl)
in (match (_89_2705) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_89_2708) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_89_2710, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _89_2718; FStar_Syntax_Syntax.lbtyp = _89_2716; FStar_Syntax_Syntax.lbeff = _89_2714; FStar_Syntax_Syntax.lbdef = _89_2712})::[]), _89_2725, _89_2727, _89_2729) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _89_2735 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_89_2735) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (let _185_2293 = (let _185_2292 = (let _185_2291 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (_185_2291)::[])
in (("Valid"), (_185_2292)))
in (FStar_SMTEncoding_Util.mkApp _185_2293))
in (

let decls = (let _185_2301 = (let _185_2300 = (let _185_2299 = (let _185_2298 = (let _185_2297 = (let _185_2296 = (let _185_2295 = (let _185_2294 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_185_2294)))
in (FStar_SMTEncoding_Util.mkEq _185_2295))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_185_2296)))
in (FStar_SMTEncoding_Util.mkForall _185_2297))
in ((_185_2298), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_185_2299))
in (_185_2300)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_185_2301)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_89_2741, _89_2743, _89_2745, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _89_18 -> (match (_89_18) with
| FStar_Syntax_Syntax.Discriminator (_89_2751) -> begin
true
end
| _89_2754 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_89_2756, _89_2758, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _185_2304 = (FStar_List.hd l.FStar_Ident.ns)
in _185_2304.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _89_19 -> (match (_89_19) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| _89_2767 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _89_2773, _89_2775, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _89_20 -> (match (_89_20) with
| FStar_Syntax_Syntax.Projector (_89_2781) -> begin
true
end
| _89_2784 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_89_2788) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _89_2797, _89_2799, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _185_2307 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _185_2307.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _89_2806) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _89_2814 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_89_2814) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _89_2815 = env.tcenv
in {FStar_TypeChecker_Env.solver = _89_2815.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _89_2815.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _89_2815.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _89_2815.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _89_2815.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _89_2815.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _89_2815.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _89_2815.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _89_2815.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _89_2815.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _89_2815.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _89_2815.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _89_2815.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _89_2815.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _89_2815.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _89_2815.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _89_2815.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _89_2815.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _89_2815.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _89_2815.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _89_2815.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _89_2815.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _89_2815.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _185_2308 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _185_2308)))
end))
in (

let lb = (

let _89_2819 = lb
in {FStar_Syntax_Syntax.lbname = _89_2819.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _89_2819.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _89_2819.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _89_2823 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _89_2828, _89_2830, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _89_2836, _89_2838, _89_2840) -> begin
(

let _89_2845 = (encode_signature env ses)
in (match (_89_2845) with
| (g, env) -> begin
(

let _89_2859 = (FStar_All.pipe_right g (FStar_List.partition (fun _89_21 -> (match (_89_21) with
| FStar_SMTEncoding_Term.Assume (_89_2848, Some ("inversion axiom"), _89_2852) -> begin
false
end
| _89_2856 -> begin
true
end))))
in (match (_89_2859) with
| (g', inversions) -> begin
(

let _89_2868 = (FStar_All.pipe_right g' (FStar_List.partition (fun _89_22 -> (match (_89_22) with
| FStar_SMTEncoding_Term.DeclFun (_89_2862) -> begin
true
end
| _89_2865 -> begin
false
end))))
in (match (_89_2868) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _89_2871, tps, k, _89_2875, datas, quals, _89_2879) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _89_23 -> (match (_89_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _89_2886 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _89_2898 = c
in (match (_89_2898) with
| (name, args, _89_2893, _89_2895, _89_2897) -> begin
(let _185_2316 = (let _185_2315 = (let _185_2314 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_185_2314), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_185_2315))
in (_185_2316)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _185_2322 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _185_2322 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _89_2905 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_89_2905) with
| (xxsym, xx) -> begin
(

let _89_2941 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _89_2908 l -> (match (_89_2908) with
| (out, decls) -> begin
(

let _89_2913 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_89_2913) with
| (_89_2911, data_t) -> begin
(

let _89_2916 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_89_2916) with
| (args, res) -> begin
(

let indices = (match ((let _185_2325 = (FStar_Syntax_Subst.compress res)
in _185_2325.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_89_2918, indices) -> begin
indices
end
| _89_2923 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _89_2929 -> (match (_89_2929) with
| (x, _89_2928) -> begin
(let _185_2330 = (let _185_2329 = (let _185_2328 = (mk_term_projector_name l x)
in ((_185_2328), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp _185_2329))
in (push_term_var env x _185_2330))
end)) env))
in (

let _89_2933 = (encode_args indices env)
in (match (_89_2933) with
| (indices, decls') -> begin
(

let _89_2934 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _185_2335 = (FStar_List.map2 (fun v a -> (let _185_2334 = (let _185_2333 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((_185_2333), (a)))
in (FStar_SMTEncoding_Util.mkEq _185_2334))) vars indices)
in (FStar_All.pipe_right _185_2335 FStar_SMTEncoding_Util.mk_and_l))
in (let _185_2340 = (let _185_2339 = (let _185_2338 = (let _185_2337 = (let _185_2336 = (mk_data_tester env l xx)
in ((_185_2336), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd _185_2337))
in ((out), (_185_2338)))
in (FStar_SMTEncoding_Util.mkOr _185_2339))
in ((_185_2340), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (_89_2941) with
| (data_ax, decls) -> begin
(

let _89_2944 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_89_2944) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > (Prims.parse_int "1")) then begin
(let _185_2341 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _185_2341 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _185_2348 = (let _185_2347 = (let _185_2344 = (let _185_2343 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _185_2342 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_185_2343), (_185_2342))))
in (FStar_SMTEncoding_Util.mkForall _185_2344))
in (let _185_2346 = (let _185_2345 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_185_2345))
in ((_185_2347), (Some ("inversion axiom")), (_185_2346))))
in FStar_SMTEncoding_Term.Assume (_185_2348)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1"))) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _185_2356 = (let _185_2355 = (let _185_2354 = (let _185_2351 = (let _185_2350 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _185_2349 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_185_2350), (_185_2349))))
in (FStar_SMTEncoding_Util.mkForall _185_2351))
in (let _185_2353 = (let _185_2352 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_185_2352))
in ((_185_2354), (Some ("inversion axiom")), (_185_2353))))
in FStar_SMTEncoding_Term.Assume (_185_2355))
in (_185_2356)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _89_2958 = (match ((let _185_2357 = (FStar_Syntax_Subst.compress k)
in _185_2357.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _89_2955 -> begin
((tps), (k))
end)
in (match (_89_2958) with
| (formals, res) -> begin
(

let _89_2961 = (FStar_Syntax_Subst.open_term formals res)
in (match (_89_2961) with
| (formals, res) -> begin
(

let _89_2968 = (encode_binders None formals env)
in (match (_89_2968) with
| (vars, guards, env', binder_decls, _89_2967) -> begin
(

let _89_2972 = (new_term_constant_and_tok_from_lid env t)
in (match (_89_2972) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (let _185_2359 = (let _185_2358 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (_185_2358)))
in (FStar_SMTEncoding_Util.mkApp _185_2359))
in (

let _89_2993 = (

let tname_decl = (let _185_2363 = (let _185_2362 = (FStar_All.pipe_right vars (FStar_List.map (fun _89_2978 -> (match (_89_2978) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _185_2361 = (varops.next_id ())
in ((tname), (_185_2362), (FStar_SMTEncoding_Term.Term_sort), (_185_2361), (false))))
in (constructor_or_logic_type_decl _185_2363))
in (

let _89_2990 = (match (vars) with
| [] -> begin
(let _185_2367 = (let _185_2366 = (let _185_2365 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _185_2364 -> Some (_185_2364)) _185_2365))
in (push_free_var env t tname _185_2366))
in (([]), (_185_2367)))
end
| _89_2982 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _185_2368 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _185_2368))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _185_2372 = (let _185_2371 = (let _185_2370 = (let _185_2369 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_185_2369)))
in (FStar_SMTEncoding_Util.mkForall' _185_2370))
in ((_185_2371), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_185_2372))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_89_2990) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_89_2993) with
| (decls, env) -> begin
(

let kindingAx = (

let _89_2996 = (encode_term_pred None res env' tapp)
in (match (_89_2996) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > (Prims.parse_int "0")) then begin
(let _185_2376 = (let _185_2375 = (let _185_2374 = (let _185_2373 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _185_2373))
in ((_185_2374), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_185_2375))
in (_185_2376)::[])
end else begin
[]
end
in (let _185_2383 = (let _185_2382 = (let _185_2381 = (let _185_2380 = (let _185_2379 = (let _185_2378 = (let _185_2377 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_185_2377)))
in (FStar_SMTEncoding_Util.mkForall _185_2378))
in ((_185_2379), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_185_2380))
in (_185_2381)::[])
in (FStar_List.append karr _185_2382))
in (FStar_List.append decls _185_2383)))
end))
in (

let aux = (let _185_2387 = (let _185_2386 = (inversion_axioms tapp vars)
in (let _185_2385 = (let _185_2384 = (pretype_axiom tapp vars)
in (_185_2384)::[])
in (FStar_List.append _185_2386 _185_2385)))
in (FStar_List.append kindingAx _185_2387))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _89_3003, _89_3005, _89_3007, _89_3009, _89_3011, _89_3013, _89_3015) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _89_3020, t, _89_3023, n_tps, quals, _89_3027, drange) -> begin
(

let _89_3034 = (new_term_constant_and_tok_from_lid env d)
in (match (_89_3034) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let _89_3038 = (FStar_Syntax_Util.arrow_formals t)
in (match (_89_3038) with
| (formals, t_res) -> begin
(

let _89_3041 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_89_3041) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _89_3048 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_89_3048) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _185_2389 = (mk_term_projector_name d x)
in ((_185_2389), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _185_2391 = (let _185_2390 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_185_2390), (true)))
in (FStar_All.pipe_right _185_2391 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let _89_3058 = (encode_term_pred None t env ddtok_tm)
in (match (_89_3058) with
| (tok_typing, decls3) -> begin
(

let _89_3065 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_89_3065) with
| (vars', guards', env'', decls_formals, _89_3064) -> begin
(

let _89_3070 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_89_3070) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _89_3074 -> begin
(let _185_2393 = (let _185_2392 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _185_2392))
in (_185_2393)::[])
end)
in (

let encode_elim = (fun _89_3077 -> (match (()) with
| () -> begin
(

let _89_3080 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_89_3080) with
| (head, args) -> begin
(match ((let _185_2396 = (FStar_Syntax_Subst.compress head)
in _185_2396.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _89_3098 = (encode_args args env')
in (match (_89_3098) with
| (encoded_args, arg_decls) -> begin
(

let _89_3113 = (FStar_List.fold_left (fun _89_3102 arg -> (match (_89_3102) with
| (env, arg_vars, eqns) -> begin
(

let _89_3108 = (let _185_2399 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _185_2399))
in (match (_89_3108) with
| (_89_3105, xv, env) -> begin
(let _185_2401 = (let _185_2400 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (_185_2400)::eqns)
in ((env), ((xv)::arg_vars), (_185_2401)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_89_3113) with
| (_89_3110, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _185_2408 = (let _185_2407 = (let _185_2406 = (let _185_2405 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _185_2404 = (let _185_2403 = (let _185_2402 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_185_2402)))
in (FStar_SMTEncoding_Util.mkImp _185_2403))
in ((((ty_pred)::[])::[]), (_185_2405), (_185_2404))))
in (FStar_SMTEncoding_Util.mkForall _185_2406))
in ((_185_2407), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_185_2408))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _185_2409 = (varops.fresh "x")
in ((_185_2409), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (let _185_2421 = (let _185_2420 = (let _185_2417 = (let _185_2416 = (let _185_2411 = (let _185_2410 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (_185_2410)::[])
in (_185_2411)::[])
in (let _185_2415 = (let _185_2414 = (let _185_2413 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _185_2412 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((_185_2413), (_185_2412))))
in (FStar_SMTEncoding_Util.mkImp _185_2414))
in ((_185_2416), ((x)::[]), (_185_2415))))
in (FStar_SMTEncoding_Util.mkForall _185_2417))
in (let _185_2419 = (let _185_2418 = (varops.mk_unique "lextop")
in Some (_185_2418))
in ((_185_2420), (Some ("lextop is top")), (_185_2419))))
in FStar_SMTEncoding_Term.Assume (_185_2421))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _185_2424 = (let _185_2423 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes _185_2423 dapp))
in (_185_2424)::[])
end
| _89_3127 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _185_2431 = (let _185_2430 = (let _185_2429 = (let _185_2428 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _185_2427 = (let _185_2426 = (let _185_2425 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (_185_2425)))
in (FStar_SMTEncoding_Util.mkImp _185_2426))
in ((((ty_pred)::[])::[]), (_185_2428), (_185_2427))))
in (FStar_SMTEncoding_Util.mkForall _185_2429))
in ((_185_2430), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_185_2431)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _89_3131 -> begin
(

let _89_3132 = (let _185_2434 = (let _185_2433 = (FStar_Syntax_Print.lid_to_string d)
in (let _185_2432 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _185_2433 _185_2432)))
in (FStar_TypeChecker_Errors.warn drange _185_2434))
in (([]), ([])))
end)
end))
end))
in (

let _89_3136 = (encode_elim ())
in (match (_89_3136) with
| (decls2, elim) -> begin
(

let g = (let _185_2461 = (let _185_2460 = (let _185_2459 = (let _185_2458 = (let _185_2439 = (let _185_2438 = (let _185_2437 = (let _185_2436 = (let _185_2435 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _185_2435))
in Some (_185_2436))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_185_2437)))
in FStar_SMTEncoding_Term.DeclFun (_185_2438))
in (_185_2439)::[])
in (let _185_2457 = (let _185_2456 = (let _185_2455 = (let _185_2454 = (let _185_2453 = (let _185_2452 = (let _185_2451 = (let _185_2443 = (let _185_2442 = (let _185_2441 = (let _185_2440 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_185_2440)))
in (FStar_SMTEncoding_Util.mkForall _185_2441))
in ((_185_2442), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_185_2443))
in (let _185_2450 = (let _185_2449 = (let _185_2448 = (let _185_2447 = (let _185_2446 = (let _185_2445 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _185_2444 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_185_2445), (_185_2444))))
in (FStar_SMTEncoding_Util.mkForall _185_2446))
in ((_185_2447), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_185_2448))
in (_185_2449)::[])
in (_185_2451)::_185_2450))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_185_2452)
in (FStar_List.append _185_2453 elim))
in (FStar_List.append decls_pred _185_2454))
in (FStar_List.append decls_formals _185_2455))
in (FStar_List.append proxy_fresh _185_2456))
in (FStar_List.append _185_2458 _185_2457)))
in (FStar_List.append decls3 _185_2459))
in (FStar_List.append decls2 _185_2460))
in (FStar_List.append binder_decls _185_2461))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _89_3142 se -> (match (_89_3142) with
| (g, env) -> begin
(

let _89_3146 = (encode_sigelt env se)
in (match (_89_3146) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _89_3154 -> (match (_89_3154) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_89_3156) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _89_3161 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _185_2476 = (FStar_Syntax_Print.bv_to_string x)
in (let _185_2475 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _185_2474 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _185_2476 _185_2475 _185_2474))))
end else begin
()
end
in (

let _89_3165 = (encode_term t1 env)
in (match (_89_3165) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let _89_3170 = (let _185_2481 = (let _185_2480 = (let _185_2479 = (FStar_Util.digest_of_string t_hash)
in (let _185_2478 = (let _185_2477 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _185_2477))
in (Prims.strcat _185_2479 _185_2478)))
in (Prims.strcat "x_" _185_2480))
in (new_term_constant_from_string env x _185_2481))
in (match (_89_3170) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _185_2485 = (let _185_2484 = (FStar_Syntax_Print.bv_to_string x)
in (let _185_2483 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _185_2482 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _185_2484 _185_2483 _185_2482))))
in Some (_185_2485))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end))))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_89_3178, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _89_3187 = (encode_free_var env fv t t_norm [])
in (match (_89_3187) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _89_3201 = (encode_sigelt env se)
in (match (_89_3201) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _89_3206 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (_89_3206) with
| (_89_3203, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _89_3213 -> (match (_89_3213) with
| (l, _89_3210, _89_3212) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _89_3220 -> (match (_89_3220) with
| (l, _89_3217, _89_3219) -> begin
(let _185_2493 = (FStar_All.pipe_left (fun _185_2489 -> FStar_SMTEncoding_Term.Echo (_185_2489)) (Prims.fst l))
in (let _185_2492 = (let _185_2491 = (let _185_2490 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_185_2490))
in (_185_2491)::[])
in (_185_2493)::_185_2492))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _185_2498 = (let _185_2497 = (let _185_2496 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _185_2496; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_185_2497)::[])
in (FStar_ST.op_Colon_Equals last_env _185_2498)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_89_3226 -> begin
(

let _89_3229 = e
in {bindings = _89_3229.bindings; depth = _89_3229.depth; tcenv = tcenv; warn = _89_3229.warn; cache = _89_3229.cache; nolabels = _89_3229.nolabels; use_zfuel_name = _89_3229.use_zfuel_name; encode_non_total_function_typ = _89_3229.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_89_3235)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _89_3237 -> (match (()) with
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

let _89_3243 = hd
in {bindings = _89_3243.bindings; depth = _89_3243.depth; tcenv = _89_3243.tcenv; warn = _89_3243.warn; cache = refs; nolabels = _89_3243.nolabels; use_zfuel_name = _89_3243.use_zfuel_name; encode_non_total_function_typ = _89_3243.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _89_3246 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_89_3250)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _89_3252 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _89_3253 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _89_3254 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_89_3257)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _89_3262 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _89_3264 = (init_env tcenv)
in (

let _89_3266 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _89_3269 = (push_env ())
in (

let _89_3271 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _89_3274 = (let _185_2519 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _185_2519))
in (

let _89_3276 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _89_3279 = (mark_env ())
in (

let _89_3281 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _89_3284 = (reset_mark_env ())
in (

let _89_3286 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _89_3289 = (commit_mark_env ())
in (

let _89_3291 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _185_2535 = (let _185_2534 = (let _185_2533 = (let _185_2532 = (let _185_2531 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _185_2531 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _185_2532 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _185_2533))
in FStar_SMTEncoding_Term.Caption (_185_2534))
in (_185_2535)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _89_3300 = (encode_sigelt env se)
in (match (_89_3300) with
| (decls, env) -> begin
(

let _89_3301 = (set_env env)
in (let _185_2536 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _185_2536)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _89_3306 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _185_2541 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _185_2541))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _89_3313 = (encode_signature (

let _89_3309 = env
in {bindings = _89_3309.bindings; depth = _89_3309.depth; tcenv = _89_3309.tcenv; warn = false; cache = _89_3309.cache; nolabels = _89_3309.nolabels; use_zfuel_name = _89_3309.use_zfuel_name; encode_non_total_function_typ = _89_3309.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_89_3313) with
| (decls, env) -> begin
(

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (

let _89_3319 = (set_env (

let _89_3317 = env
in {bindings = _89_3317.bindings; depth = _89_3317.depth; tcenv = _89_3317.tcenv; warn = true; cache = _89_3317.cache; nolabels = _89_3317.nolabels; use_zfuel_name = _89_3317.use_zfuel_name; encode_non_total_function_typ = _89_3317.encode_non_total_function_typ}))
in (

let _89_3321 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _89_3327 = (let _185_2559 = (let _185_2558 = (FStar_TypeChecker_Env.current_module tcenv)
in _185_2558.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _185_2559))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _89_3352 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _89_3341 = (aux rest)
in (match (_89_3341) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _185_2565 = (let _185_2564 = (FStar_Syntax_Syntax.mk_binder (

let _89_3343 = x
in {FStar_Syntax_Syntax.ppname = _89_3343.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _89_3343.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_185_2564)::out)
in ((_185_2565), (rest))))
end))
end
| _89_3346 -> begin
(([]), (bindings))
end))
in (

let _89_3349 = (aux bindings)
in (match (_89_3349) with
| (closing, bindings) -> begin
(let _185_2566 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_185_2566), (bindings)))
end)))
in (match (_89_3352) with
| (q, bindings) -> begin
(

let _89_3361 = (let _185_2568 = (FStar_List.filter (fun _89_24 -> (match (_89_24) with
| FStar_TypeChecker_Env.Binding_sig (_89_3355) -> begin
false
end
| _89_3358 -> begin
true
end)) bindings)
in (encode_env_bindings env _185_2568))
in (match (_89_3361) with
| (env_decls, env) -> begin
(

let _89_3362 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _185_2569 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _185_2569))
end else begin
()
end
in (

let _89_3366 = (encode_formula q env)
in (match (_89_3366) with
| (phi, qdecls) -> begin
(

let _89_3369 = (let _185_2570 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _185_2570 phi))
in (match (_89_3369) with
| (labels, phi) -> begin
(

let _89_3372 = (encode_labels labels)
in (match (_89_3372) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _185_2574 = (let _185_2573 = (FStar_SMTEncoding_Util.mkNot phi)
in (let _185_2572 = (let _185_2571 = (varops.mk_unique "@query")
in Some (_185_2571))
in ((_185_2573), (Some ("query")), (_185_2572))))
in FStar_SMTEncoding_Term.Assume (_185_2574))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end))))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _89_3379 = (push "query")
in (

let _89_3384 = (encode_formula q env)
in (match (_89_3384) with
| (f, _89_3383) -> begin
(

let _89_3385 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _89_3389) -> begin
true
end
| _89_3393 -> begin
false
end))
end)))))




