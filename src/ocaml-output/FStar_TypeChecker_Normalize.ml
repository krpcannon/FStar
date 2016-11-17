
open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Primops
| Eager_unfolding
| Inlining
| NoDeltaSteps
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| PureSubtermsWithinComputations
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars 
 and steps =
step Prims.list


let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Iota = (fun _discr_ -> (match (_discr_) with
| Iota (_) -> begin
true
end
| _ -> begin
false
end))


let is_Zeta = (fun _discr_ -> (match (_discr_) with
| Zeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exclude = (fun _discr_ -> (match (_discr_) with
| Exclude (_) -> begin
true
end
| _ -> begin
false
end))


let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))


let is_Primops = (fun _discr_ -> (match (_discr_) with
| Primops (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eager_unfolding = (fun _discr_ -> (match (_discr_) with
| Eager_unfolding (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inlining = (fun _discr_ -> (match (_discr_) with
| Inlining (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoDeltaSteps = (fun _discr_ -> (match (_discr_) with
| NoDeltaSteps (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnfoldUntil = (fun _discr_ -> (match (_discr_) with
| UnfoldUntil (_) -> begin
true
end
| _ -> begin
false
end))


let is_PureSubtermsWithinComputations = (fun _discr_ -> (match (_discr_) with
| PureSubtermsWithinComputations (_) -> begin
true
end
| _ -> begin
false
end))


let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))


let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_AllowUnboundUniverses = (fun _discr_ -> (match (_discr_) with
| AllowUnboundUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reify = (fun _discr_ -> (match (_discr_) with
| Reify (_) -> begin
true
end
| _ -> begin
false
end))


let is_CompressUvars = (fun _discr_ -> (match (_discr_) with
| CompressUvars (_) -> begin
true
end
| _ -> begin
false
end))


let ___Exclude____0 = (fun projectee -> (match (projectee) with
| Exclude (_54_11) -> begin
_54_11
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_54_14) -> begin
_54_14
end))


type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy 
 and env =
closure Prims.list


let is_Clos = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))


let is_Univ = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))


let ___Clos____0 = (fun projectee -> (match (projectee) with
| Clos (_54_17) -> begin
_54_17
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_54_20) -> begin
_54_20
end))


let closure_to_string : closure  ->  Prims.string = (fun _54_1 -> (match (_54_1) with
| Clos (_54_23, t, _54_26, _54_28) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _54_32 -> begin
"dummy"
end))


type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list}


let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list


type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of FStar_Syntax_Syntax.term


let is_Arg = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnivArgs = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))


let is_MemoLazy = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))


let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))


let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
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


let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_Steps = (fun _discr_ -> (match (_discr_) with
| Steps (_) -> begin
true
end
| _ -> begin
false
end))


let is_Debug = (fun _discr_ -> (match (_discr_) with
| Debug (_) -> begin
true
end
| _ -> begin
false
end))


let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_54_39) -> begin
_54_39
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_54_42) -> begin
_54_42
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_54_45) -> begin
_54_45
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_54_48) -> begin
_54_48
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_54_51) -> begin
_54_51
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_54_54) -> begin
_54_54
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_54_57) -> begin
_54_57
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_54_60) -> begin
_54_60
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_54_63) -> begin
_54_63
end))


let ___Debug____0 = (fun projectee -> (match (projectee) with
| Debug (_54_66) -> begin
_54_66
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_54_72) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _150_230 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _150_230 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _54_2 -> (match (_54_2) with
| Arg (c, _54_79, _54_81) -> begin
(closure_to_string c)
end
| MemoLazy (_54_85) -> begin
"MemoLazy"
end
| Abs (_54_88, bs, _54_91, _54_93, _54_95) -> begin
(let _150_233 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _150_233))
end
| _54_99 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _150_236 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _150_236 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _54_3 -> (match (_54_3) with
| [] -> begin
true
end
| _54_106 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _54_113 -> begin
(let _150_252 = (let _150_251 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _150_251))
in (FStar_All.failwith _150_252))
end)


let comp_to_comp_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (Some (u))))
end
| _54_129 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c)))


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _54_141 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_54_141) with
| (binders, cdef) -> begin
(

let _54_142 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let inst = (let _150_264 = (let _150_263 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_150_263)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _54_147 _54_151 -> (match (((_54_147), (_54_151))) with
| ((x, _54_146), (t, _54_150)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _150_264))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _150_265 = (

let _54_154 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _54_154.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _54_154.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _54_154.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _54_154.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _150_265 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c)))))
end))
end)))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun l -> if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid) then begin
Some (FStar_Syntax_Const.effect_Pure_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid) then begin
Some (FStar_Syntax_Const.effect_Tot_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
Some (FStar_Syntax_Const.effect_PURE_lid)
end else begin
None
end
end
end)


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let _54_176 = (FStar_List.fold_left (fun _54_167 u -> (match (_54_167) with
| (cur_kernel, cur_max, out) -> begin
(

let _54_171 = (FStar_Syntax_Util.univ_kernel u)
in (match (_54_171) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_54_176) with
| (_54_173, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
try
(match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(aux u)
end
| Dummy -> begin
(u)::[]
end
| _54_193 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _54_186 -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses)) then begin
(FStar_Syntax_Syntax.U_unknown)::[]
end else begin
(FStar_All.failwith "Universe variable not found")
end
end
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us = (let _150_282 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _150_282 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _54_220 = (FStar_Syntax_Util.univ_kernel u)
in (match (_54_220) with
| (_54_218, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _54_222 -> begin
us
end))
end
| _54_224 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _150_285 = (aux u)
in (FStar_List.map (fun _150_284 -> FStar_Syntax_Syntax.U_succ (_150_284)) _150_285))
end)))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
FStar_Syntax_Syntax.U_unknown
end else begin
(match ((aux u)) with
| ([]) | ((FStar_Syntax_Syntax.U_zero)::[]) -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u)::[] -> begin
u
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u)::[] -> begin
u
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end)
end)))


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (

let _54_243 = (log cfg (fun _54_242 -> (match (()) with
| () -> begin
(let _150_309 = (FStar_Syntax_Print.tag_of_term t)
in (let _150_308 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _150_309 _150_308)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _54_247 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_54_250) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_54_263) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _150_314 = (let _150_313 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_150_313))
in (mk _150_314 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _150_315 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _150_315))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_54_274) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _54_281) -> begin
(closure_as_term cfg env t0)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _54_297 = (closures_as_binders_delayed cfg env bs)
in (match (_54_297) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _150_318 = (let _150_317 = (let _150_316 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_150_316)))
in FStar_Syntax_Syntax.Tm_abs (_150_317))
in (mk _150_318 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _54_305 = (closures_as_binders_delayed cfg env bs)
in (match (_54_305) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _54_313 = (let _150_320 = (let _150_319 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_319)::[])
in (closures_as_binders_delayed cfg env _150_320))
in (match (_54_313) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _150_324 = (let _150_323 = (let _150_322 = (let _150_321 = (FStar_List.hd x)
in (FStar_All.pipe_right _150_321 Prims.fst))
in ((_150_322), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_150_323))
in (mk _150_324 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _150_330 = (let _150_329 = (let _150_328 = (closure_as_term_delayed cfg env t1)
in (let _150_327 = (let _150_326 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _150_325 -> FStar_Util.Inl (_150_325)) _150_326))
in ((_150_328), (_150_327), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_150_329))
in (mk _150_330 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _150_336 = (let _150_335 = (let _150_334 = (closure_as_term_delayed cfg env t1)
in (let _150_333 = (let _150_332 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _150_331 -> FStar_Util.Inr (_150_331)) _150_332))
in ((_150_334), (_150_333), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_150_335))
in (mk _150_336 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _150_341 = (let _150_340 = (let _150_339 = (closure_as_term_delayed cfg env t')
in (let _150_338 = (let _150_337 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_150_337))
in ((_150_339), (_150_338))))
in FStar_Syntax_Syntax.Tm_meta (_150_340))
in (mk _150_341 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _150_347 = (let _150_346 = (let _150_345 = (closure_as_term_delayed cfg env t')
in (let _150_344 = (let _150_343 = (let _150_342 = (closure_as_term_delayed cfg env tbody)
in ((m), (_150_342)))
in FStar_Syntax_Syntax.Meta_monadic (_150_343))
in ((_150_345), (_150_344))))
in FStar_Syntax_Syntax.Tm_meta (_150_346))
in (mk _150_347 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _150_350 = (let _150_349 = (let _150_348 = (closure_as_term_delayed cfg env t')
in ((_150_348), (m)))
in FStar_Syntax_Syntax.Tm_meta (_150_349))
in (mk _150_350 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _54_352 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_54_358) -> begin
body
end
| FStar_Util.Inl (_54_361) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _54_364 = lb
in {FStar_Syntax_Syntax.lbname = _54_364.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _54_364.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _54_364.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_54_368, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _54_377 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _54_381 env -> (Dummy)::env) lbs env_univs)
end
in (

let _54_385 = lb
in (let _150_362 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _150_361 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _54_385.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _54_385.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _150_362; FStar_Syntax_Syntax.lbeff = _54_385.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _150_361}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _54_388 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _54_403 -> (match (_54_403) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_54_408) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _54_418 = (norm_pat env hd)
in (match (_54_418) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _150_374 = (norm_pat env p)
in (Prims.fst _150_374)))))
in (((

let _54_421 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _54_421.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_421.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _54_438 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _54_429 _54_432 -> (match (((_54_429), (_54_432))) with
| ((pats, env), (p, b)) -> begin
(

let _54_435 = (norm_pat env p)
in (match (_54_435) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_54_438) with
| (pats, env) -> begin
(((

let _54_439 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _54_439.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_439.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _54_443 = x
in (let _150_377 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_443.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_443.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_377}))
in (((

let _54_446 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _54_446.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_446.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _54_450 = x
in (let _150_378 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_450.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_450.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_378}))
in (((

let _54_453 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _54_453.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_453.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _54_459 = x
in (let _150_379 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_379}))
in (

let t = (closure_as_term cfg env t)
in (((

let _54_463 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _54_463.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_463.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _54_467 = (norm_pat env pat)
in (match (_54_467) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _150_380 = (closure_as_term cfg env w)
in Some (_150_380))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _150_383 = (let _150_382 = (let _150_381 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_150_381)))
in FStar_Syntax_Syntax.Tm_match (_150_382))
in (mk _150_383 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _54_478 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _54_484 -> begin
(FStar_List.map (fun _54_487 -> (match (_54_487) with
| (x, imp) -> begin
(let _150_391 = (closure_as_term_delayed cfg env x)
in ((_150_391), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _54_503 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _54_493 _54_496 -> (match (((_54_493), (_54_496))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _54_497 = b
in (let _150_397 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_497.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_497.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_397}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_54_503) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _54_509 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _150_402 = (closure_as_term_delayed cfg env t)
in (let _150_401 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _150_402 _150_401)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _150_404 = (closure_as_term_delayed cfg env t)
in (let _150_403 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _150_404 _150_403)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _54_4 -> (match (_54_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _150_406 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_150_406))
end
| f -> begin
f
end))))
in (let _150_408 = (

let _54_527 = c
in (let _150_407 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _150_407; FStar_Syntax_Syntax.effect_name = _54_527.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _150_408)))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_total_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid))
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
end
| _54_536 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _150_421 = (let _150_420 = (FStar_Util.string_of_int i)
in ((_150_420), (None)))
in FStar_Const.Const_int (_150_421)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _150_617 = (let _150_616 = (FStar_List.map (fun m -> (let _150_615 = (let _150_584 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_150_584), ((fun x y -> (int_as_const (x + y))))))
in (let _150_614 = (let _150_613 = (let _150_595 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_150_595), ((fun x y -> (int_as_const (x - y))))))
in (let _150_612 = (let _150_611 = (let _150_606 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_150_606), ((fun x y -> (int_as_const (x * y))))))
in (_150_611)::[])
in (_150_613)::_150_612))
in (_150_615)::_150_614))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _150_616))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _150_617))))


let un_ops : (FStar_Ident.lident * (Prims.string  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) Prims.list = (

let mk = (fun x -> (mk x FStar_Range.dummyRange))
in (

let name = (fun x -> (let _150_627 = (let _150_626 = (let _150_625 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _150_625 FStar_Syntax_Syntax.Delta_constant None))
in FStar_Syntax_Syntax.Tm_fvar (_150_626))
in (mk _150_627)))
in (

let ctor = (fun x -> (let _150_632 = (let _150_631 = (let _150_630 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _150_630 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in FStar_Syntax_Syntax.Tm_fvar (_150_631))
in (mk _150_632)))
in (let _150_662 = (let _150_659 = (FStar_Syntax_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((_150_659), ((fun s -> (let _150_658 = (FStar_String.list_of_string s)
in (let _150_657 = (let _150_656 = (let _150_655 = (let _150_654 = (let _150_650 = (ctor (("Prims")::("Nil")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_650 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _150_653 = (let _150_652 = (let _150_651 = (name (("FStar")::("Char")::("char")::[]))
in ((_150_651), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (_150_652)::[])
in ((_150_654), (_150_653))))
in FStar_Syntax_Syntax.Tm_app (_150_655))
in (mk _150_656))
in (FStar_List.fold_right (fun c a -> (let _150_649 = (let _150_648 = (let _150_647 = (let _150_640 = (ctor (("Prims")::("Cons")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _150_640 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _150_646 = (let _150_645 = (let _150_641 = (name (("FStar")::("Char")::("char")::[]))
in ((_150_641), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (let _150_644 = (let _150_643 = (let _150_642 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))))
in ((_150_642), (None)))
in (_150_643)::(((a), (None)))::[])
in (_150_645)::_150_644))
in ((_150_647), (_150_646))))
in FStar_Syntax_Syntax.Tm_app (_150_648))
in (mk _150_649))) _150_658 _150_657)))))))
in (_150_662)::[]))))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let find = (fun fv ops -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _54_586 -> (match (_54_586) with
| (l, _54_585) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) ops)
end
| _54_588 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _54_596))::((a2, _54_592))::[]) -> begin
(match ((find fv arith_ops)) with
| None -> begin
tm
end
| Some (_54_603, op) -> begin
(

let norm = (fun i j -> (

let c = (let _150_679 = (FStar_Util.int_of_string i)
in (let _150_678 = (FStar_Util.int_of_string j)
in (op _150_679 _150_678)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _150_683 = (let _150_680 = (FStar_Syntax_Subst.compress a1)
in _150_680.FStar_Syntax_Syntax.n)
in (let _150_682 = (let _150_681 = (FStar_Syntax_Subst.compress a2)
in _150_681.FStar_Syntax_Syntax.n)
in ((_150_683), (_150_682))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _54_614))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _54_622))::[])) -> begin
(match ((let _150_691 = (let _150_684 = (FStar_Syntax_Subst.compress head1)
in _150_684.FStar_Syntax_Syntax.n)
in (let _150_690 = (let _150_685 = (FStar_Syntax_Subst.compress head2)
in _150_685.FStar_Syntax_Syntax.n)
in (let _150_689 = (let _150_686 = (FStar_Syntax_Subst.compress arg1)
in _150_686.FStar_Syntax_Syntax.n)
in (let _150_688 = (let _150_687 = (FStar_Syntax_Subst.compress arg2)
in _150_687.FStar_Syntax_Syntax.n)
in ((_150_691), (_150_690), (_150_689), (_150_688))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _150_695 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _150_694 = (let _150_693 = (let _150_692 = (norm i j)
in ((_150_692), (None)))
in (_150_693)::[])
in (FStar_Syntax_Util.mk_app _150_695 _150_694)))
end
| _54_644 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _54_657 -> begin
tm
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _54_661))::[]) -> begin
(match ((find fv un_ops)) with
| None -> begin
tm
end
| Some (_54_668, op) -> begin
(match ((let _150_698 = (FStar_Syntax_Subst.compress a1)
in _150_698.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (b, _54_674)) -> begin
(let _150_699 = (FStar_Bytes.unicode_bytes_as_string b)
in (op _150_699))
end
| _54_679 -> begin
tm
end)
end)
end
| _54_681 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _54_686 = t
in {FStar_Syntax_Syntax.n = _54_686.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _54_686.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _54_686.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _54_695 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
(reduce_primops steps tm)
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| _54_773 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (((Some (false), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (false), _))::[]) -> begin
arg
end
| _54_816 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _54_843))::((_54_834, (arg, _54_837)))::[] -> begin
arg
end
| _54_847 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _54_851))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _54_857))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _54_861 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _150_710 = (FStar_Syntax_Subst.compress t)
in _150_710.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_54_879)::[], body, _54_883) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _54_891 -> begin
tm
end)
end
| _54_893 -> begin
tm
end)
end
| _54_895 -> begin
tm
end)
end else begin
tm
end
end
end
end
end
end
| _54_897 -> begin
tm
end)
end))))


let is_norm_request = (fun hd args -> (match ((let _150_714 = (let _150_713 = (FStar_Syntax_Util.un_uinst hd)
in _150_713.FStar_Syntax_Syntax.n)
in ((_150_714), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_54_905)::(_54_903)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_54_911)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize)
end
| _54_915 -> begin
false
end))


let get_norm_request = (fun args -> (match (args) with
| ((_)::((tm, _))::[]) | (((tm, _))::[]) -> begin
tm
end
| _54_929 -> begin
(FStar_All.failwith "Impossible")
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _54_936 = (log cfg (fun _54_935 -> (match (()) with
| () -> begin
(let _150_748 = (FStar_Syntax_Print.tag_of_term t)
in (let _150_747 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _150_748 _150_747)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_54_939) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app (hd, args) when ((is_norm_request hd args) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _54_982 = cfg
in {steps = s; tcenv = _54_982.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _54_991; FStar_Syntax_Syntax.pos = _54_989; FStar_Syntax_Syntax.vars = _54_987}, (a1)::(a2)::rest) -> begin
(

let _54_1005 = (FStar_Syntax_Util.head_and_args t)
in (match (_54_1005) with
| (hd, _54_1004) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _54_1013; FStar_Syntax_Syntax.pos = _54_1011; FStar_Syntax_Syntax.vars = _54_1009}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _54_1024 = (FStar_Syntax_Util.head_and_args t)
in (match (_54_1024) with
| (reify_head, _54_1023) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _150_752 = (FStar_Syntax_Subst.compress e)
in _150_752.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _54_1044 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_54_1044) with
| (_54_1042, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _150_757 = (let _150_756 = (let _150_755 = (let _150_753 = (FStar_Syntax_Syntax.mk_binder x)
in (_150_753)::[])
in (let _150_754 = (FStar_Syntax_Util.mk_reify body)
in ((_150_755), (_150_754), (None))))
in FStar_Syntax_Syntax.Tm_abs (_150_756))
in (FStar_Syntax_Syntax.mk _150_757 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _150_771 = (let _150_770 = (let _150_769 = (let _150_768 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _150_767 = (let _150_766 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _150_765 = (let _150_764 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _150_763 = (let _150_762 = (FStar_Syntax_Syntax.as_arg head)
in (let _150_761 = (let _150_760 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _150_759 = (let _150_758 = (FStar_Syntax_Syntax.as_arg body)
in (_150_758)::[])
in (_150_760)::_150_759))
in (_150_762)::_150_761))
in (_150_764)::_150_763))
in (_150_766)::_150_765))
in (_150_768)::_150_767))
in ((bind_repr), (_150_769)))
in FStar_Syntax_Syntax.Tm_app (_150_770))
in (FStar_Syntax_Syntax.mk _150_771 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_54_1051) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_54_1054) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _54_1057 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_54_1066)); FStar_Syntax_Syntax.tk = _54_1064; FStar_Syntax_Syntax.pos = _54_1062; FStar_Syntax_Syntax.vars = _54_1060}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _54_1082 -> (match (_54_1082) with
| (pat, wopt, tm) -> begin
(let _150_773 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_150_773)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _54_1086 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _150_774 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _150_774)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _150_776 = (let _150_775 = (FStar_List.map (norm_universe cfg env) us)
in ((_150_775), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_150_776))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun _54_5 -> (match (_54_5) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end))))
in if (not (should_delta)) then begin
(rebuild cfg env stack t)
end else begin
(

let r_env = (let _150_778 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv _150_778))
in (match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(

let _54_1114 = (log cfg (fun _54_1113 -> (match (()) with
| () -> begin
(let _150_781 = (FStar_Syntax_Print.term_to_string t0)
in (let _150_780 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _150_781 _150_780)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _54_1120))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _54_1128 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _54_1130 -> begin
(let _150_785 = (let _150_784 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _150_784))
in (FStar_All.failwith _150_785))
end)
end else begin
(norm cfg env stack t)
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_54_1134) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r, fix) -> begin
if ((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps)))) then begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(

let _54_1148 = (log cfg (fun _54_1147 -> (match (()) with
| () -> begin
(let _150_788 = (FStar_Syntax_Print.term_to_string t)
in (let _150_787 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _150_788 _150_787)))
end)))
in (match ((let _150_789 = (FStar_Syntax_Subst.compress t')
in _150_789.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_54_1151) -> begin
(norm cfg env stack t')
end
| _54_1154 -> begin
(rebuild cfg env stack t')
end))
end
| None -> begin
(norm cfg env ((MemoLazy (r))::stack) t0)
end)
end else begin
(norm cfg env stack t0)
end
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (_54_1164))::_54_1162 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_54_1170))::_54_1168 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _54_1176, _54_1178))::stack_rest -> begin
(match (c) with
| Univ (_54_1183) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _54_1186 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_54_1189)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _54_1193 = (log cfg (fun _54_1192 -> (match (()) with
| () -> begin
(let _150_791 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _150_791))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _54_1199 = (log cfg (fun _54_1198 -> (match (()) with
| () -> begin
(let _150_793 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _150_793))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _54_1205 = (log cfg (fun _54_1204 -> (match (()) with
| () -> begin
(let _150_795 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _150_795))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _54_1208 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _54_1210 -> begin
(

let cfg = (

let _54_1211 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _54_1211.tcenv; delta_level = _54_1211.delta_level})
in (let _150_796 = (closure_as_term cfg env t)
in (rebuild cfg env stack _150_796)))
end)
end
| (_54_1216)::tl -> begin
(

let _54_1219 = (log cfg (fun _54_1218 -> (match (()) with
| () -> begin
(let _150_798 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _150_798))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _54_1228 = cfg
in {steps = s; tcenv = _54_1228.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _54_1234 = (set_memo r ((env), (t)))
in (

let _54_1237 = (log cfg (fun _54_1236 -> (match (()) with
| () -> begin
(let _150_800 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _150_800))
end)))
in (norm cfg env stack t)))
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _150_801 = (closure_as_term cfg env t)
in (rebuild cfg env stack _150_801))
end else begin
(

let _54_1273 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_54_1273) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _150_807 = (let _150_805 = (let _150_803 = (let _150_802 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _150_802))
in (FStar_All.pipe_right _150_803 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _150_805 (fun _150_804 -> FStar_Util.Inl (_150_804))))
in (FStar_All.pipe_right _150_807 (fun _150_806 -> Some (_150_806))))
end
| _54_1278 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _54_1281 -> (Dummy)::env) env))
in (

let _54_1285 = (log cfg (fun _54_1284 -> (match (()) with
| () -> begin
(let _150_811 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _150_811))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _54_1293 stack -> (match (_54_1293) with
| (a, aq) -> begin
(let _150_818 = (let _150_817 = (let _150_816 = (let _150_815 = (let _150_814 = (FStar_Util.mk_ref None)
in ((env), (a), (_150_814), (false)))
in Clos (_150_815))
in ((_150_816), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_150_817))
in (_150_818)::stack)
end)) args))
in (

let _54_1297 = (log cfg (fun _54_1296 -> (match (()) with
| () -> begin
(let _150_820 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _150_820))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let _54_1307 = x
in {FStar_Syntax_Syntax.ppname = _54_1307.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_1307.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _54_1311 -> begin
(let _150_821 = (closure_as_term cfg env t)
in (rebuild cfg env stack _150_821))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _54_1315 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_54_1315) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _150_824 = (let _150_823 = (let _150_822 = (FStar_Syntax_Subst.close closing f)
in (((

let _54_1317 = x
in {FStar_Syntax_Syntax.ppname = _54_1317.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_1317.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_150_822)))
in FStar_Syntax_Syntax.Tm_refine (_150_823))
in (mk _150_824 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _150_825 = (closure_as_term cfg env t)
in (rebuild cfg env stack _150_825))
end else begin
(

let _54_1326 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_54_1326) with
| (bs, c) -> begin
(

let c = (let _150_828 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _54_1328 -> (Dummy)::env) env))
in (norm_comp cfg _150_828 c))
in (

let t = (let _150_829 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _150_829 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _54_1356 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _54_1359 = (log cfg (fun _54_1358 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _150_831 = (norm cfg env [] t)
in FStar_Util.Inl (_150_831))
end
| FStar_Util.Inr (c) -> begin
(let _150_832 = (norm_comp cfg env c)
in FStar_Util.Inr (_150_832))
end)
in (let _150_833 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _150_833)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_54_1372, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_54_1384); FStar_Syntax_Syntax.lbunivs = _54_1382; FStar_Syntax_Syntax.lbtyp = _54_1380; FStar_Syntax_Syntax.lbeff = _54_1378; FStar_Syntax_Syntax.lbdef = _54_1376})::_54_1374), _54_1390) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || ((FStar_Syntax_Util.is_ghost_effect n) && (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))))))) then begin
(

let env = (let _150_836 = (let _150_835 = (let _150_834 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_150_834), (false)))
in Clos (_150_835))
in (_150_836)::env)
in (norm cfg env stack body))
end else begin
(

let _54_1404 = (let _150_839 = (let _150_838 = (let _150_837 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _150_837 FStar_Syntax_Syntax.mk_binder))
in (_150_838)::[])
in (FStar_Syntax_Subst.open_term _150_839 body))
in (match (_54_1404) with
| (bs, body) -> begin
(

let lb = (

let _54_1405 = lb
in (let _150_845 = (let _150_842 = (let _150_840 = (FStar_List.hd bs)
in (FStar_All.pipe_right _150_840 Prims.fst))
in (FStar_All.pipe_right _150_842 (fun _150_841 -> FStar_Util.Inl (_150_841))))
in (let _150_844 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _150_843 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _150_845; FStar_Syntax_Syntax.lbunivs = _54_1405.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _150_844; FStar_Syntax_Syntax.lbeff = _54_1405.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _150_843}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _54_1409 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _150_848 = (closure_as_term cfg env t)
in (rebuild cfg env stack _150_848))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _54_1435 = (FStar_List.fold_right (fun lb _54_1424 -> (match (_54_1424) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _150_851 = (

let _54_1425 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _54_1425.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _54_1425.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _150_851))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_54_1435) with
| (rec_env, memos, _54_1434) -> begin
(

let _54_1438 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _150_858 = (let _150_857 = (let _150_856 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_150_856), (false)))
in Clos (_150_857))
in (_150_858)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let t = (norm cfg env [] t)
in (

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _54_1453 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _54_1453.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m') -> begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _54_1461 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _54_1461.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end
| _54_1465 -> begin
(match (stack) with
| (_54_1469)::_54_1467 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _54_1474) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _54_1481 -> begin
(norm cfg env stack head)
end)
end
| _54_1483 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _150_859 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_150_859))
end
| _54_1488 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _54_1496 -> (match (_54_1496) with
| (a, imp) -> begin
(let _150_864 = (norm cfg env [] a)
in ((_150_864), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _54_1505 = comp
in (let _150_871 = (let _150_870 = (let _150_869 = (norm cfg env [] t)
in (let _150_868 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_150_869), (_150_868))))
in FStar_Syntax_Syntax.Total (_150_870))
in {FStar_Syntax_Syntax.n = _150_871; FStar_Syntax_Syntax.tk = _54_1505.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _54_1505.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _54_1505.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _54_1511 = comp
in (let _150_875 = (let _150_874 = (let _150_873 = (norm cfg env [] t)
in (let _150_872 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_150_873), (_150_872))))
in FStar_Syntax_Syntax.GTotal (_150_874))
in {FStar_Syntax_Syntax.n = _150_875; FStar_Syntax_Syntax.tk = _54_1511.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _54_1511.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _54_1511.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _54_1519 -> (match (_54_1519) with
| (a, i) -> begin
(let _150_879 = (norm cfg env [] a)
in ((_150_879), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _54_6 -> (match (_54_6) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _150_881 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (_150_881))
end
| f -> begin
f
end))))
in (

let _54_1525 = comp
in (let _150_886 = (let _150_885 = (

let _54_1527 = ct
in (let _150_884 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _150_883 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _150_882 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _150_884; FStar_Syntax_Syntax.effect_name = _54_1527.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _150_883; FStar_Syntax_Syntax.effect_args = _150_882; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (_150_885))
in {FStar_Syntax_Syntax.n = _150_886; FStar_Syntax_Syntax.tk = _54_1525.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _54_1525.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _54_1525.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _54_1534 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _54_1534.tcenv; delta_level = _54_1534.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _150_894 = (norm t)
in (FStar_Syntax_Util.non_informative _150_894)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_54_1539) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _54_1545 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _54_1545.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _54_1545.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _54_1545.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _54_1552 = ct
in {FStar_Syntax_Syntax.comp_univs = _54_1552.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _54_1552.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _54_1552.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _54_1552.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _54_1556 = ct
in {FStar_Syntax_Syntax.comp_univs = _54_1556.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _54_1556.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _54_1556.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _54_1556.FStar_Syntax_Syntax.flags}))
end)
in (

let _54_1559 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _54_1559.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _54_1559.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _54_1559.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _54_1562 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _54_1567 -> (match (_54_1567) with
| (x, imp) -> begin
(let _150_899 = (

let _54_1568 = x
in (let _150_898 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_1568.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_1568.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_898}))
in ((_150_899), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _54_1581 = (FStar_List.fold_left (fun _54_1575 b -> (match (_54_1575) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_54_1581) with
| (nbs, _54_1580) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _150_910 = (let _150_909 = (let _150_908 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _150_908))
in FStar_Util.Inl (_150_909))
in Some (_150_910))
end else begin
(let _150_913 = (let _150_912 = (let _150_911 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _150_911))
in FStar_Util.Inl (_150_912))
in Some (_150_913))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _54_1590 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
(

let _54_1600 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms"))) then begin
(let _150_919 = (FStar_Syntax_Print.term_to_string tm)
in (let _150_918 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" _150_919 _150_918)))
end else begin
()
end
in (rebuild cfg env stack t))
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _54_1608 = cfg
in {steps = s; tcenv = _54_1608.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _54_1621 = (set_memo r ((env), (t)))
in (

let _54_1624 = (log cfg (fun _54_1623 -> (match (()) with
| () -> begin
(let _150_921 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _150_921))
end)))
in (rebuild cfg env stack t)))
end
| (Let (env', bs, lb, r))::stack -> begin
(

let body = (FStar_Syntax_Subst.close bs t)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) None r)
in (rebuild cfg env' stack t)))
end
| (Abs (env', bs, env'', lopt, r))::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (norm_lcomp_opt cfg env'' lopt)
in (let _150_922 = (

let _54_1647 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _54_1647.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _54_1647.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _54_1647.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _150_922))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _54_1683), aq, r))::stack -> begin
(

let _54_1692 = (log cfg (fun _54_1691 -> (match (()) with
| () -> begin
(let _150_924 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _150_924))
end)))
in if (FStar_List.contains (Exclude (Iota)) cfg.steps) then begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end else begin
(match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (MemoLazy (m))::(App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end
| Some (_54_1702, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _150_925 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _150_925)))
end
| (Match (env, branches, r))::stack -> begin
(

let _54_1723 = (log cfg (fun _54_1722 -> (match (()) with
| () -> begin
(let _150_927 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _150_927))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _54_1727 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun _54_7 -> (match (_54_7) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| _54_1733 -> begin
false
end))))
in (

let steps' = if (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)) then begin
(Exclude (Zeta))::[]
end else begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end
in (

let _54_1736 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = _54_1736.tcenv; delta_level = new_delta})))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg_exclude_iota_zeta env t)
end else begin
(norm cfg_exclude_iota_zeta env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_54_1746) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _54_1756 = (norm_pat env hd)
in (match (_54_1756) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _150_940 = (norm_pat env p)
in (Prims.fst _150_940)))))
in (((

let _54_1759 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _54_1759.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_1759.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _54_1776 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _54_1767 _54_1770 -> (match (((_54_1767), (_54_1770))) with
| ((pats, env), (p, b)) -> begin
(

let _54_1773 = (norm_pat env p)
in (match (_54_1773) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_54_1776) with
| (pats, env) -> begin
(((

let _54_1777 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _54_1777.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_1777.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _54_1781 = x
in (let _150_943 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_1781.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_1781.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_943}))
in (((

let _54_1784 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _54_1784.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_1784.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _54_1788 = x
in (let _150_944 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_1788.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_1788.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_944}))
in (((

let _54_1791 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _54_1791.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_1791.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _54_1797 = x
in (let _150_945 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _54_1797.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _54_1797.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _150_945}))
in (

let t = (norm_or_whnf env t)
in (((

let _54_1801 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _54_1801.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _54_1801.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _54_1805 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _54_1810 = (FStar_Syntax_Subst.open_branch branch)
in (match (_54_1810) with
| (p, wopt, e) -> begin
(

let _54_1813 = (norm_pat env p)
in (match (_54_1813) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _150_947 = (norm_or_whnf env w)
in Some (_150_947))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _150_948 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _150_948)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _54_1824) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _54_1849 -> begin
false
end))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee p -> (

let scrutinee = (FStar_Syntax_Util.unmeta scrutinee)
in (

let _54_1866 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_54_1866) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_54_1872) -> begin
Some (m)
end
| FStar_Util.Inr (true) -> begin
Some (m)
end
| FStar_Util.Inr (false) -> begin
None
end))))
in (match (mopt) with
| None -> begin
FStar_Util.Inr (false)
end
| Some (m) -> begin
m
end))
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
FStar_Util.Inl ((scrutinee)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (_54_1889) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _54_1896 -> begin
(let _150_965 = (not ((is_cons head)))
in FStar_Util.Inr (_150_965))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _150_966 = (FStar_Syntax_Util.un_uinst head)
in _150_966.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _54_1904 -> begin
(let _150_967 = (not ((is_cons head)))
in FStar_Util.Inr (_150_967))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _54_1914))::rest_a, ((p, _54_1920))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _54_1928 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(match ((matches_pat scrutinee p)) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
(

let _54_1946 = (log cfg (fun _54_1945 -> (match (()) with
| () -> begin
(let _150_978 = (FStar_Syntax_Print.pat_to_string p)
in (let _150_977 = (let _150_976 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _150_976 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _150_978 _150_977)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _150_983 = (let _150_982 = (let _150_981 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_150_981), (false)))
in Clos (_150_982))
in (_150_983)::env)) env s)
in (let _150_984 = (guard_when_clause wopt b rest)
in (norm cfg env stack _150_984))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches scrutinee branches)
end)))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun _54_8 -> (match (_54_8) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| _54_1959 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| _54_1963 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _150_996 = (config s e)
in (norm _150_996 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _150_1003 = (config s e)
in (norm_comp _150_1003 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _150_1008 = (config [] env)
in (norm_universe _150_1008 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _150_1013 = (config [] env)
in (ghost_to_pure_aux _150_1013 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _150_1020 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _150_1020)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _54_1982 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _54_1982.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _54_1982.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _54_1984 -> (match (()) with
| () -> begin
(let _150_1022 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _150_1022))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _150_1027 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _150_1027)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _150_1033 = (let _150_1032 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _150_1032 [] c))
in (FStar_Syntax_Print.comp_to_string _150_1033)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _150_1044 = (let _150_1043 = (let _150_1042 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_150_1042)))
in FStar_Syntax_Syntax.Tm_refine (_150_1043))
in (mk _150_1044 t0.FStar_Syntax_Syntax.pos))
end
| _54_2007 -> begin
t
end))
end
| _54_2009 -> begin
t
end)))
in (aux t))))


let eta_expand_with_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun t sort -> (

let _54_2014 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_54_2014) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _54_2017 -> begin
(

let _54_2020 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_54_2020) with
| (binders, args) -> begin
(let _150_1053 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _150_1052 = (let _150_1051 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _150_1049 -> FStar_Util.Inl (_150_1049)))
in (FStar_All.pipe_right _150_1051 (fun _150_1050 -> Some (_150_1050))))
in (FStar_Syntax_Util.abs binders _150_1053 _150_1052)))
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match ((let _150_1058 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_150_1058), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _54_2026) -> begin
(let _150_1059 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type t _150_1059))
end
| (_54_2029, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type t x.FStar_Syntax_Syntax.sort)
end
| _54_2034 -> begin
(

let _54_2037 = (FStar_Syntax_Util.head_and_args t)
in (match (_54_2037) with
| (head, args) -> begin
(match ((let _150_1060 = (FStar_Syntax_Subst.compress head)
in _150_1060.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_54_2039, thead) -> begin
(

let _54_2045 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_54_2045) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _54_2053 = (env.FStar_TypeChecker_Env.type_of (

let _54_2046 = env
in {FStar_TypeChecker_Env.solver = _54_2046.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _54_2046.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _54_2046.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _54_2046.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _54_2046.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _54_2046.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _54_2046.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _54_2046.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _54_2046.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _54_2046.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _54_2046.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _54_2046.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _54_2046.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _54_2046.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _54_2046.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _54_2046.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _54_2046.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _54_2046.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _54_2046.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _54_2046.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _54_2046.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_54_2053) with
| (_54_2049, ty, _54_2052) -> begin
(eta_expand_with_type t ty)
end))
end
end))
end
| _54_2055 -> begin
(

let _54_2063 = (env.FStar_TypeChecker_Env.type_of (

let _54_2056 = env
in {FStar_TypeChecker_Env.solver = _54_2056.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _54_2056.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _54_2056.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _54_2056.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _54_2056.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _54_2056.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _54_2056.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _54_2056.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _54_2056.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _54_2056.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _54_2056.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _54_2056.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _54_2056.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _54_2056.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _54_2056.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _54_2056.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _54_2056.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _54_2056.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _54_2056.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _54_2056.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _54_2056.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_54_2063) with
| (_54_2059, ty, _54_2062) -> begin
(eta_expand_with_type t ty)
end))
end)
end))
end))




