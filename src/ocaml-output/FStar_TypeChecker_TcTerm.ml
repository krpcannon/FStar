
open Prims

let instantiate_both : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _59_7 = env
in {FStar_TypeChecker_Env.solver = _59_7.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_7.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_7.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_7.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_7.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_7.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_7.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_7.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_7.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = true; FStar_TypeChecker_Env.effects = _59_7.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_7.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_7.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_7.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_7.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_7.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_7.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_7.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_7.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_7.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_7.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_7.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_7.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_7.FStar_TypeChecker_Env.qname_and_index}))


let no_inst : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.env = (fun env -> (

let _59_10 = env
in {FStar_TypeChecker_Env.solver = _59_10.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_10.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_10.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_10.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_10.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_10.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_10.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_10.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_10.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = false; FStar_TypeChecker_Env.effects = _59_10.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_10.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_10.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_10.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_10.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_10.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_10.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_10.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_10.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_10.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_10.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_10.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_10.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_10.FStar_TypeChecker_Env.qname_and_index}))


let mk_lex_list : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun vs -> (FStar_List.fold_right (fun v tl -> (

let r = if (tl.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
v.FStar_Syntax_Syntax.pos
end else begin
(FStar_Range.union_ranges v.FStar_Syntax_Syntax.pos tl.FStar_Syntax_Syntax.pos)
end
in (let _155_12 = (let _155_11 = (FStar_Syntax_Syntax.as_arg v)
in (let _155_10 = (let _155_9 = (FStar_Syntax_Syntax.as_arg tl)
in (_155_9)::[])
in (_155_11)::_155_10))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair _155_12 (Some (FStar_Syntax_Util.lex_t.FStar_Syntax_Syntax.n)) r)))) vs FStar_Syntax_Util.lex_top))


let is_eq : FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.bool = (fun _59_1 -> (match (_59_1) with
| Some (FStar_Syntax_Syntax.Equality) -> begin
true
end
| _59_20 -> begin
false
end))


let steps = (fun env -> (FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[])


let unfold_whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Beta)::[]) env t))


let norm : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize (steps env) env t))


let norm_c : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (FStar_TypeChecker_Normalize.normalize_comp (steps env) env c))


let check_no_escape : FStar_Syntax_Syntax.term Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.bv Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun head_opt env fvs kt -> (

let rec aux = (fun try_norm t -> (match (fvs) with
| [] -> begin
t
end
| _59_37 -> begin
(

let t = if try_norm then begin
(norm env t)
end else begin
t
end
in (

let fvs' = (FStar_Syntax_Free.names t)
in (match ((FStar_List.tryFind (fun x -> (FStar_Util.set_mem x fvs')) fvs)) with
| None -> begin
t
end
| Some (x) -> begin
if (not (try_norm)) then begin
(aux true t)
end else begin
(

let fail = (fun _59_45 -> (match (()) with
| () -> begin
(

let msg = (match (head_opt) with
| None -> begin
(let _155_43 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Bound variables \'%s\' escapes; add a type annotation" _155_43))
end
| Some (head) -> begin
(let _155_45 = (FStar_Syntax_Print.bv_to_string x)
in (let _155_44 = (FStar_TypeChecker_Normalize.term_to_string env head)
in (FStar_Util.format2 "Bound variables \'%s\' in the type of \'%s\' escape because of impure applications; add explicit let-bindings" _155_45 _155_44)))
end)
in (let _155_48 = (let _155_47 = (let _155_46 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_155_46)))
in FStar_Syntax_Syntax.Error (_155_47))
in (Prims.raise _155_48)))
end))
in (

let s = (let _155_50 = (let _155_49 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _155_49))
in (FStar_TypeChecker_Util.new_uvar env _155_50))
in (match ((FStar_TypeChecker_Rel.try_teq env t s)) with
| Some (g) -> begin
(

let _59_53 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in s)
end
| _59_56 -> begin
(fail ())
end)))
end
end)))
end))
in (aux false kt)))


let push_binding = (fun env b -> (FStar_TypeChecker_Env.push_bv env (Prims.fst b)))


let maybe_extend_subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.subst_t = (fun s b v -> if (FStar_Syntax_Syntax.is_null_binder b) then begin
s
end else begin
(FStar_Syntax_Syntax.NT ((((Prims.fst b)), (v))))::s
end)


let set_lcomp_result : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.lcomp = (fun lc t -> (

let _59_64 = lc
in {FStar_Syntax_Syntax.eff_name = _59_64.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_64.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _59_66 -> (match (()) with
| () -> begin
(let _155_64 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.set_result_typ _155_64 t))
end))}))


let memo_tk : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun e t -> (

let _59_69 = (FStar_ST.op_Colon_Equals e.FStar_Syntax_Syntax.tk (Some (t.FStar_Syntax_Syntax.n)))
in e))


let value_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.lcomp) FStar_Util.either  ->  FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e tlc guard -> (

let should_return = (fun t -> (match ((let _155_79 = (FStar_Syntax_Subst.compress t)
in _155_79.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_59_78, c) -> begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(

let t = (FStar_All.pipe_left FStar_Syntax_Util.unrefine (FStar_Syntax_Util.comp_result c))
in (match ((let _155_80 = (FStar_Syntax_Subst.compress t)
in _155_80.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) -> begin
false
end
| FStar_Syntax_Syntax.Tm_constant (_59_86) -> begin
false
end
| _59_89 -> begin
true
end))
end else begin
false
end
end
| _59_91 -> begin
true
end))
in (

let lc = (match (tlc) with
| FStar_Util.Inl (t) -> begin
(let _155_81 = if ((not ((should_return t))) || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(FStar_Syntax_Syntax.mk_Total t)
end else begin
(FStar_TypeChecker_Util.return_value env t e)
end
in (FStar_Syntax_Util.lcomp_of_comp _155_81))
end
| FStar_Util.Inr (lc) -> begin
lc
end)
in (

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _59_120 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(let _155_82 = (memo_tk e t)
in ((_155_82), (lc), (guard)))
end
| Some (t') -> begin
(

let _59_101 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_84 = (FStar_Syntax_Print.term_to_string t)
in (let _155_83 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Computed return type %s; expected type %s\n" _155_84 _155_83)))
end else begin
()
end
in (

let _59_105 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t')
in (match (_59_105) with
| (e, lc) -> begin
(

let t = lc.FStar_Syntax_Syntax.res_typ
in (

let _59_109 = (FStar_TypeChecker_Util.check_and_ascribe env e t t')
in (match (_59_109) with
| (e, g) -> begin
(

let _59_110 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_88 = (FStar_Syntax_Print.term_to_string t)
in (let _155_87 = (FStar_Syntax_Print.term_to_string t')
in (let _155_86 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (let _155_85 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_Util.print4 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n" _155_88 _155_87 _155_86 _155_85)))))
end else begin
()
end
in (

let msg = if (FStar_TypeChecker_Rel.is_trivial g) then begin
None
end else begin
(FStar_All.pipe_left (fun _155_98 -> Some (_155_98)) (FStar_TypeChecker_Errors.subtyping_failed env t t'))
end
in (

let g = (FStar_TypeChecker_Rel.conj_guard g guard)
in (

let _59_116 = (FStar_TypeChecker_Util.strengthen_precondition msg env e lc g)
in (match (_59_116) with
| (lc, g) -> begin
(let _155_99 = (memo_tk e t')
in ((_155_99), ((set_lcomp_result lc t')), (g)))
end)))))
end)))
end)))
end)
in (match (_59_120) with
| (e, lc, g) -> begin
(

let _59_121 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_100 = (FStar_Syntax_Print.lcomp_to_string lc)
in (FStar_Util.print1 "Return comp type is %s\n" _155_100))
end else begin
()
end
in ((e), (lc), (g)))
end))))))


let comp_check_expected_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e lc -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
((e), (lc), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (t) -> begin
(

let _59_131 = (FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t)
in (match (_59_131) with
| (e, lc) -> begin
(FStar_TypeChecker_Util.weaken_result_typ env e lc t)
end))
end))


let check_expected_effect : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp)  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp * FStar_TypeChecker_Env.guard_t) = (fun env copt _59_136 -> (match (_59_136) with
| (e, c) -> begin
(

let expected_c_opt = (match (copt) with
| Some (_59_138) -> begin
copt
end
| None -> begin
if ((FStar_Options.ml_ish ()) && (FStar_Ident.lid_equals FStar_Syntax_Const.effect_ALL_lid (FStar_Syntax_Util.comp_effect_name c))) then begin
(let _155_113 = (FStar_Syntax_Util.ml_comp (FStar_Syntax_Util.comp_result c) e.FStar_Syntax_Syntax.pos)
in Some (_155_113))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_comp c) then begin
None
end else begin
if (FStar_Syntax_Util.is_pure_comp c) then begin
(let _155_114 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in Some (_155_114))
end else begin
if (FStar_Syntax_Util.is_pure_or_ghost_comp c) then begin
(let _155_115 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in Some (_155_115))
end else begin
None
end
end
end
end
end)
in (match (expected_c_opt) with
| None -> begin
(let _155_116 = (norm_c env c)
in ((e), (_155_116), (FStar_TypeChecker_Rel.trivial_guard)))
end
| Some (expected_c) -> begin
(

let _59_145 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_119 = (FStar_Syntax_Print.term_to_string e)
in (let _155_118 = (FStar_Syntax_Print.comp_to_string c)
in (let _155_117 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\n(%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _155_119 _155_118 _155_117))))
end else begin
()
end
in (

let c = (norm_c env c)
in (

let _59_148 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_122 = (FStar_Syntax_Print.term_to_string e)
in (let _155_121 = (FStar_Syntax_Print.comp_to_string c)
in (let _155_120 = (FStar_Syntax_Print.comp_to_string expected_c)
in (FStar_Util.print3 "\n\nAfter normalization (%s) About to check\n\t%s\nagainst expected effect\n\t%s\n" _155_122 _155_121 _155_120))))
end else begin
()
end
in (

let _59_154 = (FStar_TypeChecker_Util.check_comp env e c expected_c)
in (match (_59_154) with
| (e, _59_152, g) -> begin
(

let g = (let _155_123 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Util.label_guard _155_123 "could not prove post-condition" g))
in (

let _59_156 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_125 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _155_124 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print2 "(%s) DONE check_expected_effect; guard is: %s\n" _155_125 _155_124)))
end else begin
()
end
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e (FStar_Syntax_Util.comp_effect_name c) (FStar_Syntax_Util.comp_effect_name expected_c))
in ((e), (expected_c), (g)))))
end)))))
end))
end))


let no_logical_guard = (fun env _59_163 -> (match (_59_163) with
| (te, kt, f) -> begin
(match ((FStar_TypeChecker_Rel.guard_form f)) with
| FStar_TypeChecker_Common.Trivial -> begin
((te), (kt), (f))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _155_131 = (let _155_130 = (let _155_129 = (FStar_TypeChecker_Errors.unexpected_non_trivial_precondition_on_term env f)
in (let _155_128 = (FStar_TypeChecker_Env.get_range env)
in ((_155_129), (_155_128))))
in FStar_Syntax_Syntax.Error (_155_130))
in (Prims.raise _155_131))
end)
end))


let print_expected_ty : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun env -> (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(FStar_Util.print_string "Expected type is None")
end
| Some (t) -> begin
(let _155_134 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Expected type is %s" _155_134))
end))


let check_smt_pat = (fun env t bs c -> if (FStar_Syntax_Util.is_smt_lemma t) then begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _59_189; FStar_Syntax_Syntax.effect_name = _59_187; FStar_Syntax_Syntax.result_typ = _59_185; FStar_Syntax_Syntax.effect_args = (_pre)::(_post)::((pats, _59_179))::[]; FStar_Syntax_Syntax.flags = _59_176}) -> begin
(

let pat_vars = (let _155_139 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env pats)
in (FStar_Syntax_Free.names _155_139))
in (match ((FStar_All.pipe_right bs (FStar_Util.find_opt (fun _59_196 -> (match (_59_196) with
| (b, _59_195) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _59_200) -> begin
(let _155_142 = (let _155_141 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _155_141))
in (FStar_TypeChecker_Errors.warn t.FStar_Syntax_Syntax.pos _155_142))
end))
end
| _59_204 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
()
end)


let guard_letrecs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun env actuals expected_c -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
env.FStar_TypeChecker_Env.letrecs
end else begin
(match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
[]
end
| letrecs -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let env = (

let _59_211 = env
in {FStar_TypeChecker_Env.solver = _59_211.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_211.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_211.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_211.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_211.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_211.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_211.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_211.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_211.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_211.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_211.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_211.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _59_211.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_211.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_211.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_211.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_211.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_211.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_211.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_211.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_211.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_211.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_211.FStar_TypeChecker_Env.qname_and_index})
in (

let precedes = (FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.precedes_lid)
in (

let decreases_clause = (fun bs c -> (

let filter_types_and_functions = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun _59_223 -> (match (_59_223) with
| (b, _59_222) -> begin
(

let t = (let _155_156 = (FStar_Syntax_Util.unrefine b.FStar_Syntax_Syntax.sort)
in (unfold_whnf env _155_156))
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
[]
end
| _59_232 -> begin
(let _155_157 = (FStar_Syntax_Syntax.bv_to_name b)
in (_155_157)::[])
end))
end)))))
in (

let as_lex_list = (fun dec -> (

let _59_238 = (FStar_Syntax_Util.head_and_args dec)
in (match (_59_238) with
| (head, _59_237) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
dec
end
| _59_242 -> begin
(mk_lex_list ((dec)::[]))
end)
end)))
in (

let cflags = (FStar_Syntax_Util.comp_flags c)
in (match ((FStar_All.pipe_right cflags (FStar_List.tryFind (fun _59_2 -> (match (_59_2) with
| FStar_Syntax_Syntax.DECREASES (_59_246) -> begin
true
end
| _59_249 -> begin
false
end))))) with
| Some (FStar_Syntax_Syntax.DECREASES (dec)) -> begin
(as_lex_list dec)
end
| _59_254 -> begin
(

let xs = (FStar_All.pipe_right bs filter_types_and_functions)
in (match (xs) with
| (x)::[] -> begin
x
end
| _59_259 -> begin
(mk_lex_list xs)
end))
end)))))
in (

let previous_dec = (decreases_clause actuals expected_c)
in (

let guard_one_letrec = (fun _59_264 -> (match (_59_264) with
| (l, t) -> begin
(match ((let _155_163 = (FStar_Syntax_Subst.compress t)
in _155_163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let formals = (FStar_All.pipe_right formals (FStar_List.map (fun _59_271 -> (match (_59_271) with
| (x, imp) -> begin
if (FStar_Syntax_Syntax.is_null_bv x) then begin
(let _155_167 = (let _155_166 = (let _155_165 = (FStar_Syntax_Syntax.range_of_bv x)
in Some (_155_165))
in (FStar_Syntax_Syntax.new_bv _155_166 x.FStar_Syntax_Syntax.sort))
in ((_155_167), (imp)))
end else begin
((x), (imp))
end
end))))
in (

let _59_275 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_59_275) with
| (formals, c) -> begin
(

let dec = (decreases_clause formals c)
in (

let precedes = (let _155_171 = (let _155_170 = (FStar_Syntax_Syntax.as_arg dec)
in (let _155_169 = (let _155_168 = (FStar_Syntax_Syntax.as_arg previous_dec)
in (_155_168)::[])
in (_155_170)::_155_169))
in (FStar_Syntax_Syntax.mk_Tm_app precedes _155_171 None r))
in (

let _59_282 = (FStar_Util.prefix formals)
in (match (_59_282) with
| (bs, (last, imp)) -> begin
(

let last = (

let _59_283 = last
in (let _155_172 = (FStar_Syntax_Util.refine last precedes)
in {FStar_Syntax_Syntax.ppname = _59_283.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_283.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_172}))
in (

let refined_formals = (FStar_List.append bs ((((last), (imp)))::[]))
in (

let t' = (FStar_Syntax_Util.arrow refined_formals c)
in (

let _59_288 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_175 = (FStar_Syntax_Print.lbname_to_string l)
in (let _155_174 = (FStar_Syntax_Print.term_to_string t)
in (let _155_173 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print3 "Refined let rec %s\n\tfrom type %s\n\tto type %s\n" _155_175 _155_174 _155_173))))
end else begin
()
end
in ((l), (t'))))))
end))))
end)))
end
| _59_291 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Annotated type of \'let rec\' must be an arrow"), (t.FStar_Syntax_Syntax.pos)))))
end)
end))
in (FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec))))))))
end)
end)


let rec tc_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (tc_maybe_toplevel_term (

let _59_294 = env
in {FStar_TypeChecker_Env.solver = _59_294.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_294.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_294.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_294.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_294.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_294.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_294.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_294.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_294.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_294.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_294.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_294.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_294.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_294.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_294.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_294.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_294.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_294.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_294.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_294.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_294.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_294.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_294.FStar_TypeChecker_Env.qname_and_index}) e))
and tc_maybe_toplevel_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = if (e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange) then begin
env
end else begin
(FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
end
in (

let _59_299 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_245 = (let _155_243 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _155_243))
in (let _155_244 = (FStar_Syntax_Print.tag_of_term e)
in (FStar_Util.print2 "%s (%s)\n" _155_245 _155_244)))
end else begin
()
end
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_59_303) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(tc_value env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)) -> begin
(

let _59_344 = (tc_tot_or_gtot_term env e)
in (match (_59_344) with
| (e, c, g) -> begin
(

let g = (

let _59_345 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_345.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_345.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_345.FStar_TypeChecker_Env.implicits})
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_pattern (pats)) -> begin
(

let _59_355 = (FStar_Syntax_Util.type_u ())
in (match (_59_355) with
| (t, u) -> begin
(

let _59_359 = (tc_check_tot_or_gtot_term env e t)
in (match (_59_359) with
| (e, c, g) -> begin
(

let _59_366 = (

let _59_363 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_363) with
| (env, _59_362) -> begin
(tc_pats env pats)
end))
in (match (_59_366) with
| (pats, g') -> begin
(

let g' = (

let _59_367 = g'
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_367.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_367.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_367.FStar_TypeChecker_Env.implicits})
in (let _155_250 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_pattern (pats))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _155_249 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((_155_250), (c), (_155_249)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)) -> begin
(match ((let _155_251 = (FStar_Syntax_Subst.compress e)
in _155_251.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((_59_376, ({FStar_Syntax_Syntax.lbname = x; FStar_Syntax_Syntax.lbunivs = _59_383; FStar_Syntax_Syntax.lbtyp = _59_381; FStar_Syntax_Syntax.lbeff = _59_379; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _59_394 = (let _155_252 = (FStar_TypeChecker_Env.set_expected_typ env FStar_TypeChecker_Common.t_unit)
in (tc_term _155_252 e1))
in (match (_59_394) with
| (e1, c1, g1) -> begin
(

let _59_398 = (tc_term env e2)
in (match (_59_398) with
| (e2, c2, g2) -> begin
(

let c = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((None), (c2)))
in (

let e = (let _155_257 = (let _155_256 = (let _155_255 = (let _155_254 = (let _155_253 = (FStar_Syntax_Syntax.mk_lb ((x), ([]), (c1.FStar_Syntax_Syntax.eff_name), (FStar_TypeChecker_Common.t_unit), (e1)))
in (_155_253)::[])
in ((false), (_155_254)))
in ((_155_255), (e2)))
in FStar_Syntax_Syntax.Tm_let (_155_256))
in (FStar_Syntax_Syntax.mk _155_257 (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _155_258 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in ((e), (c), (_155_258))))))
end))
end))
end
| _59_403 -> begin
(

let _59_407 = (tc_term env e)
in (match (_59_407) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (_59_411)) -> begin
(tc_term env e)
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let _59_422 = (tc_term env e)
in (match (_59_422) with
| (e, c, g) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e), (m)))) (Some (c.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in ((e), (c), (g)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (expected_c), _59_428) -> begin
(

let _59_434 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_434) with
| (env0, _59_433) -> begin
(

let _59_439 = (tc_comp env0 expected_c)
in (match (_59_439) with
| (expected_c, _59_437, g) -> begin
(

let t_res = (FStar_Syntax_Util.comp_result expected_c)
in (

let _59_444 = (let _155_259 = (FStar_TypeChecker_Env.set_expected_typ env0 t_res)
in (tc_term _155_259 e))
in (match (_59_444) with
| (e, c', g') -> begin
(

let _59_448 = (let _155_261 = (let _155_260 = (c'.FStar_Syntax_Syntax.comp ())
in ((e), (_155_260)))
in (check_expected_effect env0 (Some (expected_c)) _155_261))
in (match (_59_448) with
| (e, expected_c, g'') -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t_res)), (Some ((FStar_Syntax_Util.comp_effect_name expected_c)))))) (Some (t_res.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let lc = (FStar_Syntax_Util.lcomp_of_comp expected_c)
in (

let f = (let _155_262 = (FStar_TypeChecker_Rel.conj_guard g' g'')
in (FStar_TypeChecker_Rel.conj_guard g _155_262))
in (

let _59_455 = (comp_check_expected_typ env e lc)
in (match (_59_455) with
| (e, c, f2) -> begin
(let _155_263 = (FStar_TypeChecker_Rel.conj_guard f f2)
in ((e), (c), (_155_263)))
end)))))
end))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), _59_460) -> begin
(

let _59_465 = (FStar_Syntax_Util.type_u ())
in (match (_59_465) with
| (k, u) -> begin
(

let _59_470 = (tc_check_tot_or_gtot_term env t k)
in (match (_59_470) with
| (t, _59_468, f) -> begin
(

let _59_474 = (let _155_264 = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_term _155_264 e))
in (match (_59_474) with
| (e, c, g) -> begin
(

let _59_478 = (let _155_268 = (FStar_TypeChecker_Env.set_range env t.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _59_475 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _155_268 e c f))
in (match (_59_478) with
| (c, f) -> begin
(

let _59_482 = (let _155_269 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (t)), (Some (c.FStar_Syntax_Syntax.eff_name))))) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (comp_check_expected_typ env _155_269 c))
in (match (_59_482) with
| (e, c, f2) -> begin
(let _155_271 = (let _155_270 = (FStar_TypeChecker_Rel.conj_guard g f2)
in (FStar_TypeChecker_Rel.conj_guard f _155_270))
in ((e), (c), (_155_271)))
end))
end))
end))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_)); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, (a)::(hd)::rest)) -> begin
(

let rest = (hd)::rest
in (

let _59_518 = (FStar_Syntax_Util.head_and_args top)
in (match (_59_518) with
| (unary_op, _59_517) -> begin
(

let head = (let _155_272 = (FStar_Range.union_ranges unary_op.FStar_Syntax_Syntax.pos (Prims.fst a).FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((unary_op), ((a)::[])))) None _155_272))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((head), (rest)))) None top.FStar_Syntax_Syntax.pos)
in (tc_term env t)))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _59_526; FStar_Syntax_Syntax.pos = _59_524; FStar_Syntax_Syntax.vars = _59_522}, ((e, aqual))::[]) -> begin
(

let _59_536 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reify is irrelevant and will be ignored")
end else begin
()
end
in (

let _59_545 = (

let _59_541 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_541) with
| (env0, _59_540) -> begin
(tc_term env0 e)
end))
in (match (_59_545) with
| (e, c, g) -> begin
(

let _59_549 = (FStar_Syntax_Util.head_and_args top)
in (match (_59_549) with
| (reify_op, _59_548) -> begin
(

let u_c = (

let _59_555 = (tc_term env c.FStar_Syntax_Syntax.res_typ)
in (match (_59_555) with
| (_59_551, c, _59_554) -> begin
(match ((let _155_273 = (FStar_Syntax_Subst.compress c.FStar_Syntax_Syntax.res_typ)
in _155_273.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
u
end
| _59_559 -> begin
(FStar_All.failwith "Unexpected result type of computation")
end)
end))
in (

let repr = (FStar_TypeChecker_Util.reify_comp env c u_c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reify_op), ((((e), (aqual)))::[])))) (Some (repr.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let c = (let _155_274 = (FStar_Syntax_Syntax.mk_Total repr)
in (FStar_All.pipe_right _155_274 FStar_Syntax_Util.lcomp_of_comp))
in (

let _59_567 = (comp_check_expected_typ env e c)
in (match (_59_567) with
| (e, c, g') -> begin
(let _155_275 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), (c), (_155_275)))
end))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (l)); FStar_Syntax_Syntax.tk = _59_573; FStar_Syntax_Syntax.pos = _59_571; FStar_Syntax_Syntax.vars = _59_569}, ((e, aqual))::[]) -> begin
(

let _59_584 = if (FStar_Option.isSome aqual) then begin
(FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "Qualifier on argument to reflect is irrelevant and will be ignored")
end else begin
()
end
in (

let no_reflect = (fun _59_587 -> (match (()) with
| () -> begin
(let _155_280 = (let _155_279 = (let _155_278 = (FStar_Util.format1 "Effect %s cannot be reified" l.FStar_Ident.str)
in ((_155_278), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_155_279))
in (Prims.raise _155_280))
end))
in (

let _59_591 = (FStar_Syntax_Util.head_and_args top)
in (match (_59_591) with
| (reflect_op, _59_590) -> begin
(match ((FStar_TypeChecker_Env.effect_decl_opt env l)) with
| None -> begin
(no_reflect ())
end
| Some (ed) -> begin
if (not ((FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))) then begin
(no_reflect ())
end else begin
(

let _59_597 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_597) with
| (env_no_ex, topt) -> begin
(

let _59_625 = (

let u = (FStar_TypeChecker_Env.new_u_univ ())
in (

let repr = (FStar_TypeChecker_Env.inst_effect_fun_with ((u)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let t = (let _155_286 = (let _155_285 = (let _155_284 = (let _155_283 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _155_282 = (let _155_281 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (_155_281)::[])
in (_155_283)::_155_282))
in ((repr), (_155_284)))
in FStar_Syntax_Syntax.Tm_app (_155_285))
in (FStar_Syntax_Syntax.mk _155_286 None top.FStar_Syntax_Syntax.pos))
in (

let _59_605 = (let _155_288 = (let _155_287 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _155_287 Prims.fst))
in (tc_tot_or_gtot_term _155_288 t))
in (match (_59_605) with
| (t, _59_603, g) -> begin
(match ((let _155_289 = (FStar_Syntax_Subst.compress t)
in _155_289.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_59_607, ((res, _59_614))::((wp, _59_610))::[]) -> begin
((t), (res), (wp), (g))
end
| _59_620 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))
in (match (_59_625) with
| (expected_repr_typ, res_typ, wp, g0) -> begin
(

let _59_639 = (

let _59_629 = (tc_tot_or_gtot_term env_no_ex e)
in (match (_59_629) with
| (e, c, g) -> begin
(

let _59_630 = if (let _155_290 = (FStar_Syntax_Util.is_total_lcomp c)
in (FStar_All.pipe_left Prims.op_Negation _155_290)) then begin
(FStar_TypeChecker_Errors.add_errors env (((("Expected Tot, got a GTot computation"), (e.FStar_Syntax_Syntax.pos)))::[]))
end else begin
()
end
in (match ((FStar_TypeChecker_Rel.try_teq env_no_ex c.FStar_Syntax_Syntax.res_typ expected_repr_typ)) with
| None -> begin
(

let _59_633 = (let _155_295 = (let _155_294 = (let _155_293 = (let _155_292 = (FStar_Syntax_Print.term_to_string ed.FStar_Syntax_Syntax.repr)
in (let _155_291 = (FStar_Syntax_Print.term_to_string c.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "Expected an instance of %s; got %s" _155_292 _155_291)))
in ((_155_293), (e.FStar_Syntax_Syntax.pos)))
in (_155_294)::[])
in (FStar_TypeChecker_Errors.add_errors env _155_295))
in (let _155_296 = (FStar_TypeChecker_Rel.conj_guard g g0)
in ((e), (_155_296))))
end
| Some (g') -> begin
(let _155_298 = (let _155_297 = (FStar_TypeChecker_Rel.conj_guard g g0)
in (FStar_TypeChecker_Rel.conj_guard g' _155_297))
in ((e), (_155_298)))
end))
end))
in (match (_59_639) with
| (e, g) -> begin
(

let c = (let _155_304 = (let _155_303 = (let _155_302 = (let _155_299 = (env.FStar_TypeChecker_Env.universe_of env res_typ)
in (_155_299)::[])
in (let _155_301 = (let _155_300 = (FStar_Syntax_Syntax.as_arg wp)
in (_155_300)::[])
in {FStar_Syntax_Syntax.comp_univs = _155_302; FStar_Syntax_Syntax.effect_name = ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.result_typ = res_typ; FStar_Syntax_Syntax.effect_args = _155_301; FStar_Syntax_Syntax.flags = []}))
in (FStar_Syntax_Syntax.mk_Comp _155_303))
in (FStar_All.pipe_right _155_304 FStar_Syntax_Util.lcomp_of_comp))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((reflect_op), ((((e), (aqual)))::[])))) (Some (res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (

let _59_645 = (comp_check_expected_typ env e c)
in (match (_59_645) with
| (e, c, g') -> begin
(let _155_305 = (FStar_TypeChecker_Rel.conj_guard g' g)
in ((e), (c), (_155_305)))
end))))
end))
end))
end))
end
end)
end))))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let env0 = env
in (

let env = (let _155_307 = (let _155_306 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _155_306 Prims.fst))
in (FStar_All.pipe_right _155_307 instantiate_both))
in (

let _59_652 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_309 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _155_308 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print2 "(%s) Checking app %s\n" _155_309 _155_308)))
end else begin
()
end
in (

let _59_657 = (tc_term (no_inst env) head)
in (match (_59_657) with
| (head, chead, g_head) -> begin
(

let _59_661 = if (FStar_TypeChecker_Util.short_circuit_head head) then begin
(let _155_310 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_short_circuit_args env head chead g_head args _155_310))
end else begin
(let _155_311 = (FStar_TypeChecker_Env.expected_typ env0)
in (check_application_args env head chead g_head args _155_311))
end
in (match (_59_661) with
| (e, c, g) -> begin
(

let _59_662 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_312 = (FStar_TypeChecker_Rel.print_pending_implicits g)
in (FStar_Util.print1 "Introduced {%s} implicits in application\n" _155_312))
end else begin
()
end
in (

let c = if (((FStar_TypeChecker_Env.should_verify env) && (not ((FStar_Syntax_Util.is_lcomp_partial_return c)))) && (FStar_Syntax_Util.is_pure_or_ghost_lcomp c)) then begin
(FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env e c)
end else begin
c
end
in (

let _59_668 = (comp_check_expected_typ env0 e c)
in (match (_59_668) with
| (e, c, g') -> begin
(

let gimp = (match ((let _155_313 = (FStar_Syntax_Subst.compress head)
in _155_313.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, _59_671) -> begin
(

let imp = (("head of application is a uvar"), (env0), (u), (e), (c.FStar_Syntax_Syntax.res_typ), (head.FStar_Syntax_Syntax.pos))
in (

let _59_675 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _59_675.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _59_675.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_675.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end
| _59_678 -> begin
FStar_TypeChecker_Rel.trivial_guard
end)
in (

let gres = (let _155_314 = (FStar_TypeChecker_Rel.conj_guard g' gimp)
in (FStar_TypeChecker_Rel.conj_guard g _155_314))
in (

let _59_681 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_316 = (FStar_Syntax_Print.term_to_string e)
in (let _155_315 = (FStar_TypeChecker_Rel.guard_to_string env gres)
in (FStar_Util.print2 "Guard from application node %s is %s\n" _155_316 _155_315)))
end else begin
()
end
in ((e), (c), (gres)))))
end))))
end))
end)))))
end
| FStar_Syntax_Syntax.Tm_match (e1, eqns) -> begin
(

let _59_689 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_689) with
| (env1, topt) -> begin
(

let env1 = (instantiate_both env1)
in (

let _59_694 = (tc_term env1 e1)
in (match (_59_694) with
| (e1, c1, g1) -> begin
(

let _59_705 = (match (topt) with
| Some (t) -> begin
((env), (t))
end
| None -> begin
(

let _59_701 = (FStar_Syntax_Util.type_u ())
in (match (_59_701) with
| (k, _59_700) -> begin
(

let res_t = (FStar_TypeChecker_Util.new_uvar env k)
in (let _155_317 = (FStar_TypeChecker_Env.set_expected_typ env res_t)
in ((_155_317), (res_t))))
end))
end)
in (match (_59_705) with
| (env_branches, res_t) -> begin
(

let _59_706 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_318 = (FStar_Syntax_Print.term_to_string res_t)
in (FStar_Util.print1 "Tm_match: expected type of branches is %s\n" _155_318))
end else begin
()
end
in (

let guard_x = (FStar_Syntax_Syntax.gen_bv "scrutinee" (Some (e1.FStar_Syntax_Syntax.pos)) c1.FStar_Syntax_Syntax.res_typ)
in (

let t_eqns = (FStar_All.pipe_right eqns (FStar_List.map (tc_eqn guard_x env_branches)))
in (

let _59_724 = (

let _59_721 = (FStar_List.fold_right (fun _59_715 _59_718 -> (match (((_59_715), (_59_718))) with
| ((_59_711, f, c, g), (caccum, gaccum)) -> begin
(let _155_321 = (FStar_TypeChecker_Rel.conj_guard g gaccum)
in (((((f), (c)))::caccum), (_155_321)))
end)) t_eqns (([]), (FStar_TypeChecker_Rel.trivial_guard)))
in (match (_59_721) with
| (cases, g) -> begin
(let _155_322 = (FStar_TypeChecker_Util.bind_cases env res_t cases)
in ((_155_322), (g)))
end))
in (match (_59_724) with
| (c_branches, g_branches) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (guard_x)), (c_branches)))
in (

let e = (

let mk_match = (fun scrutinee -> (

let scrutinee = (FStar_TypeChecker_Util.maybe_lift env scrutinee c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let branches = (FStar_All.pipe_right t_eqns (FStar_List.map (fun _59_738 -> (match (_59_738) with
| ((pat, wopt, br), _59_734, lc, _59_737) -> begin
(let _155_326 = (FStar_TypeChecker_Util.maybe_lift env br lc.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in ((pat), (wopt), (_155_326)))
end))))
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (FStar_Util.Inl (cres.FStar_Syntax_Syntax.res_typ)), (Some (cres.FStar_Syntax_Syntax.eff_name))))) None e.FStar_Syntax_Syntax.pos)))))
in if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c1.FStar_Syntax_Syntax.eff_name) then begin
(mk_match e1)
end else begin
(

let e_match = (let _155_327 = (FStar_Syntax_Syntax.bv_to_name guard_x)
in (mk_match _155_327))
in (

let lb = (let _155_328 = (FStar_TypeChecker_Env.norm_eff_name env c1.FStar_Syntax_Syntax.eff_name)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (guard_x); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = c1.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.lbeff = _155_328; FStar_Syntax_Syntax.lbdef = e1})
in (

let e = (let _155_333 = (let _155_332 = (let _155_331 = (let _155_330 = (let _155_329 = (FStar_Syntax_Syntax.mk_binder guard_x)
in (_155_329)::[])
in (FStar_Syntax_Subst.close _155_330 e_match))
in ((((false), ((lb)::[]))), (_155_331)))
in FStar_Syntax_Syntax.Tm_let (_155_332))
in (FStar_Syntax_Syntax.mk _155_333 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos))
in (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ))))
end)
in (

let _59_745 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_336 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _155_335 = (let _155_334 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _155_334))
in (FStar_Util.print2 "(%s) comp type = %s\n" _155_336 _155_335)))
end else begin
()
end
in (let _155_337 = (FStar_TypeChecker_Rel.conj_guard g1 g_branches)
in ((e), (cres), (_155_337))))))
end)))))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_59_757); FStar_Syntax_Syntax.lbunivs = _59_755; FStar_Syntax_Syntax.lbtyp = _59_753; FStar_Syntax_Syntax.lbeff = _59_751; FStar_Syntax_Syntax.lbdef = _59_749})::[]), _59_763) -> begin
(

let _59_766 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_338 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _155_338))
end else begin
()
end
in (check_top_level_let env top))
end
| FStar_Syntax_Syntax.Tm_let ((false, _59_770), _59_773) -> begin
(check_inner_let env top)
end
| FStar_Syntax_Syntax.Tm_let ((true, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_59_788); FStar_Syntax_Syntax.lbunivs = _59_786; FStar_Syntax_Syntax.lbtyp = _59_784; FStar_Syntax_Syntax.lbeff = _59_782; FStar_Syntax_Syntax.lbdef = _59_780})::_59_778), _59_794) -> begin
(

let _59_797 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_339 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.print1 "%s\n" _155_339))
end else begin
()
end
in (check_top_level_let_rec env top))
end
| FStar_Syntax_Syntax.Tm_let ((true, _59_801), _59_804) -> begin
(check_inner_let_rec env top)
end)))))
and tc_value : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let check_instantiated_fvar = (fun env v dc e t -> (

let _59_818 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_59_818) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _155_353 = (let _155_352 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_352))
in FStar_Util.Inr (_155_353))
end
in (

let is_data_ctor = (fun _59_3 -> (match (_59_3) with
| (Some (FStar_Syntax_Syntax.Data_ctor)) | (Some (FStar_Syntax_Syntax.Record_ctor (_))) -> begin
true
end
| _59_828 -> begin
false
end))
in if ((is_data_ctor dc) && (not ((FStar_TypeChecker_Env.is_datacon env v.FStar_Syntax_Syntax.v)))) then begin
(let _155_359 = (let _155_358 = (let _155_357 = (FStar_Util.format1 "Expected a data constructor; got %s" v.FStar_Syntax_Syntax.v.FStar_Ident.str)
in (let _155_356 = (FStar_TypeChecker_Env.get_range env)
in ((_155_357), (_155_356))))
in FStar_Syntax_Syntax.Error (_155_358))
in (Prims.raise _155_359))
end else begin
(value_check_expected_typ env e tc implicits)
end))
end)))
in (

let env = (FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos)
in (

let top = (FStar_Syntax_Subst.compress e)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _155_361 = (let _155_360 = (FStar_Syntax_Print.term_to_string top)
in (FStar_Util.format1 "Impossible: Violation of locally nameless convention: %s" _155_360))
in (FStar_All.failwith _155_361))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t1) -> begin
(

let g = (match ((let _155_362 = (FStar_Syntax_Subst.compress t1)
in _155_362.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_59_839) -> begin
FStar_TypeChecker_Rel.trivial_guard
end
| _59_842 -> begin
(

let imp = (("uvar in term"), (env), (u), (top), (t1), (top.FStar_Syntax_Syntax.pos))
in (

let _59_844 = FStar_TypeChecker_Rel.trivial_guard
in {FStar_TypeChecker_Env.guard_f = _59_844.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _59_844.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_844.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = (imp)::[]}))
end)
in (value_check_expected_typ env e (FStar_Util.Inl (t1)) g))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _59_859 = (match ((FStar_TypeChecker_Env.expected_typ env)) with
| None -> begin
(

let _59_852 = (FStar_Syntax_Util.type_u ())
in (match (_59_852) with
| (k, u) -> begin
(FStar_TypeChecker_Util.new_implicit_var "type of user-provided implicit term" r env k)
end))
end
| Some (t) -> begin
((t), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end)
in (match (_59_859) with
| (t, _59_857, g0) -> begin
(

let _59_864 = (FStar_TypeChecker_Util.new_implicit_var "user-provided implicit term" r env t)
in (match (_59_864) with
| (e, _59_862, g1) -> begin
(let _155_365 = (let _155_363 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_right _155_363 FStar_Syntax_Util.lcomp_of_comp))
in (let _155_364 = (FStar_TypeChecker_Rel.conj_guard g0 g1)
in ((e), (_155_365), (_155_364))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = if env.FStar_TypeChecker_Env.use_bv_sorts then begin
x.FStar_Syntax_Syntax.sort
end else begin
(FStar_TypeChecker_Env.lookup_bv env x)
end
in (

let e = (FStar_Syntax_Syntax.bv_to_name (

let _59_868 = x
in {FStar_Syntax_Syntax.ppname = _59_868.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_868.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (

let _59_874 = (FStar_TypeChecker_Util.maybe_instantiate env e t)
in (match (_59_874) with
| (e, t, implicits) -> begin
(

let tc = if (FStar_TypeChecker_Env.should_verify env) then begin
FStar_Util.Inl (t)
end else begin
(let _155_367 = (let _155_366 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_366))
in FStar_Util.Inr (_155_367))
end
in (value_check_expected_typ env e tc implicits))
end))))
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _59_881; FStar_Syntax_Syntax.pos = _59_879; FStar_Syntax_Syntax.vars = _59_877}, us) -> begin
(

let us = (FStar_List.map (tc_universe env) us)
in (

let _59_891 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_59_891) with
| (us', t) -> begin
(

let _59_898 = if ((FStar_List.length us) <> (FStar_List.length us')) then begin
(let _155_370 = (let _155_369 = (let _155_368 = (FStar_TypeChecker_Env.get_range env)
in (("Unexpected number of universe instantiations"), (_155_368)))
in FStar_Syntax_Syntax.Error (_155_369))
in (Prims.raise _155_370))
end else begin
(FStar_List.iter2 (fun u' u -> (match (u') with
| FStar_Syntax_Syntax.U_unif (u'') -> begin
(FStar_Unionfind.change u'' (Some (u)))
end
| _59_897 -> begin
(FStar_All.failwith "Impossible")
end)) us' us)
end
in (

let fv' = (

let _59_900 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _59_902 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _59_902.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _59_902.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _59_900.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _59_900.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _155_373 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _155_373 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let _59_910 = (FStar_TypeChecker_Env.lookup_lid env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_59_910) with
| (us, t) -> begin
(

let _59_911 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Range"))) then begin
(let _155_383 = (let _155_374 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Syntax_Print.lid_to_string _155_374))
in (let _155_382 = (FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos)
in (let _155_381 = (let _155_376 = (let _155_375 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _155_375))
in (FStar_Range.string_of_range _155_376))
in (let _155_380 = (let _155_378 = (let _155_377 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.range_of_lid _155_377))
in (FStar_Range.string_of_use_range _155_378))
in (let _155_379 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print5 "Lookup up fvar %s at location %s (lid range = %s, %s); got type %s" _155_383 _155_382 _155_381 _155_380 _155_379))))))
end else begin
()
end
in (

let fv' = (

let _59_913 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _59_915 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _59_915.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = t; FStar_Syntax_Syntax.p = _59_915.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _59_913.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _59_913.FStar_Syntax_Syntax.fv_qual})
in (

let e = (let _155_384 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv')) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _155_384 us))
in (check_instantiated_fvar env fv'.FStar_Syntax_Syntax.fv_name fv'.FStar_Syntax_Syntax.fv_qual e t))))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let t = (tc_constant top.FStar_Syntax_Syntax.pos c)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (c)) (Some (t.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_929 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_929) with
| (bs, c) -> begin
(

let env0 = env
in (

let _59_934 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_934) with
| (env, _59_933) -> begin
(

let _59_939 = (tc_binders env bs)
in (match (_59_939) with
| (bs, env, g, us) -> begin
(

let _59_943 = (tc_comp env c)
in (match (_59_943) with
| (c, uc, f) -> begin
(

let e = (

let _59_944 = (FStar_Syntax_Util.arrow bs c)
in {FStar_Syntax_Syntax.n = _59_944.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _59_944.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_944.FStar_Syntax_Syntax.vars})
in (

let _59_947 = (check_smt_pat env e bs c)
in (

let u = FStar_Syntax_Syntax.U_max ((uc)::us)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _155_385 = (FStar_TypeChecker_Rel.close_guard bs f)
in (FStar_TypeChecker_Rel.conj_guard g _155_385))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (tc_universe env u)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ (u))) None top.FStar_Syntax_Syntax.pos)
in (

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) (Some (t.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (value_check_expected_typ env e (FStar_Util.Inl (t)) FStar_TypeChecker_Rel.trivial_guard))))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _59_963 = (let _155_387 = (let _155_386 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_386)::[])
in (FStar_Syntax_Subst.open_term _155_387 phi))
in (match (_59_963) with
| (x, phi) -> begin
(

let env0 = env
in (

let _59_968 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_968) with
| (env, _59_967) -> begin
(

let _59_973 = (let _155_388 = (FStar_List.hd x)
in (tc_binder env _155_388))
in (match (_59_973) with
| (x, env, f1, u) -> begin
(

let _59_974 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_391 = (FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos)
in (let _155_390 = (FStar_Syntax_Print.term_to_string phi)
in (let _155_389 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (FStar_Util.print3 "(%s) Checking refinement formula %s; binder is %s\n" _155_391 _155_390 _155_389))))
end else begin
()
end
in (

let _59_979 = (FStar_Syntax_Util.type_u ())
in (match (_59_979) with
| (t_phi, _59_978) -> begin
(

let _59_984 = (tc_check_tot_or_gtot_term env phi t_phi)
in (match (_59_984) with
| (phi, _59_982, f2) -> begin
(

let e = (

let _59_985 = (FStar_Syntax_Util.refine (Prims.fst x) phi)
in {FStar_Syntax_Syntax.n = _59_985.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _59_985.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_985.FStar_Syntax_Syntax.vars})
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (u)) None top.FStar_Syntax_Syntax.pos)
in (

let g = (let _155_392 = (FStar_TypeChecker_Rel.close_guard ((x)::[]) f2)
in (FStar_TypeChecker_Rel.conj_guard f1 _155_392))
in (value_check_expected_typ env0 e (FStar_Util.Inl (t)) g))))
end))
end)))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, _59_993) -> begin
(

let bs = (FStar_TypeChecker_Util.maybe_add_implicit_binders env bs)
in (

let _59_999 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_393 = (FStar_Syntax_Print.term_to_string (

let _59_997 = top
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))); FStar_Syntax_Syntax.tk = _59_997.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_997.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_997.FStar_Syntax_Syntax.vars}))
in (FStar_Util.print1 "Abstraction is: %s\n" _155_393))
end else begin
()
end
in (

let _59_1003 = (FStar_Syntax_Subst.open_term bs body)
in (match (_59_1003) with
| (bs, body) -> begin
(tc_abs env top bs body)
end))))
end
| _59_1005 -> begin
(let _155_396 = (let _155_395 = (FStar_Syntax_Print.term_to_string top)
in (let _155_394 = (FStar_Syntax_Print.tag_of_term top)
in (FStar_Util.format2 "Unexpected value: %s (%s)" _155_395 _155_394)))
in (FStar_All.failwith _155_396))
end)))))
and tc_constant : FStar_Range.range  ->  FStar_Const.sconst  ->  FStar_Syntax_Syntax.typ = (fun r c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_TypeChecker_Common.t_unit
end
| FStar_Const.Const_bool (_59_1010) -> begin
FStar_TypeChecker_Common.t_bool
end
| FStar_Const.Const_int (_59_1013, None) -> begin
FStar_TypeChecker_Common.t_int
end
| FStar_Const.Const_int (_59_1018, Some (_59_1020)) -> begin
(FStar_All.failwith "machine integers should be desugared")
end
| FStar_Const.Const_string (_59_1025) -> begin
FStar_TypeChecker_Common.t_string
end
| FStar_Const.Const_float (_59_1028) -> begin
FStar_TypeChecker_Common.t_float
end
| FStar_Const.Const_char (_59_1031) -> begin
FStar_TypeChecker_Common.t_char
end
| FStar_Const.Const_effect -> begin
FStar_Syntax_Util.ktype0
end
| FStar_Const.Const_range (_59_1035) -> begin
FStar_TypeChecker_Common.t_range
end
| _59_1038 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported constant"), (r)))))
end))
and tc_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe * FStar_TypeChecker_Env.guard_t) = (fun env c -> (

let c0 = c
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, _59_1044) -> begin
(

let _59_1049 = (FStar_Syntax_Util.type_u ())
in (match (_59_1049) with
| (k, u) -> begin
(

let _59_1054 = (tc_check_tot_or_gtot_term env t k)
in (match (_59_1054) with
| (t, _59_1052, g) -> begin
(let _155_401 = (FStar_Syntax_Syntax.mk_Total' t (Some (u)))
in ((_155_401), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (t, _59_1057) -> begin
(

let _59_1062 = (FStar_Syntax_Util.type_u ())
in (match (_59_1062) with
| (k, u) -> begin
(

let _59_1067 = (tc_check_tot_or_gtot_term env t k)
in (match (_59_1067) with
| (t, _59_1065, g) -> begin
(let _155_402 = (FStar_Syntax_Syntax.mk_GTotal' t (Some (u)))
in ((_155_402), (u), (g)))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let head = (FStar_Syntax_Syntax.fvar c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Syntax.Delta_constant None)
in (

let head = (match (c.FStar_Syntax_Syntax.comp_univs) with
| [] -> begin
head
end
| us -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst (((head), (us)))) None c0.FStar_Syntax_Syntax.pos)
end)
in (

let tc = (let _155_404 = (let _155_403 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_155_403)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_Syntax_Syntax.mk_Tm_app head _155_404 None c.FStar_Syntax_Syntax.result_typ.FStar_Syntax_Syntax.pos))
in (

let _59_1079 = (tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff)
in (match (_59_1079) with
| (tc, _59_1077, f) -> begin
(

let _59_1082 = (FStar_Syntax_Util.head_and_args tc)
in (match (_59_1082) with
| (head, args) -> begin
(

let comp_univs = (match ((let _155_405 = (FStar_Syntax_Subst.compress head)
in _155_405.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (_59_1084, us) -> begin
us
end
| _59_1089 -> begin
[]
end)
in (

let _59_1094 = (FStar_Syntax_Util.head_and_args tc)
in (match (_59_1094) with
| (_59_1092, args) -> begin
(

let _59_1097 = (let _155_407 = (FStar_List.hd args)
in (let _155_406 = (FStar_List.tl args)
in ((_155_407), (_155_406))))
in (match (_59_1097) with
| (res, args) -> begin
(

let _59_1113 = (let _155_409 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _59_4 -> (match (_59_4) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let _59_1104 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_1104) with
| (env, _59_1103) -> begin
(

let _59_1109 = (tc_tot_or_gtot_term env e)
in (match (_59_1109) with
| (e, _59_1107, g) -> begin
((FStar_Syntax_Syntax.DECREASES (e)), (g))
end))
end))
end
| f -> begin
((f), (FStar_TypeChecker_Rel.trivial_guard))
end))))
in (FStar_All.pipe_right _155_409 FStar_List.unzip))
in (match (_59_1113) with
| (flags, guards) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env (Prims.fst res))
in (

let c = (FStar_Syntax_Syntax.mk_Comp (

let _59_1115 = c
in {FStar_Syntax_Syntax.comp_univs = comp_univs; FStar_Syntax_Syntax.effect_name = _59_1115.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = (Prims.fst res); FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = _59_1115.FStar_Syntax_Syntax.flags}))
in (

let u_c = (match ((FStar_TypeChecker_Util.effect_repr env c u)) with
| None -> begin
u
end
| Some (tm) -> begin
(env.FStar_TypeChecker_Env.universe_of env tm)
end)
in (let _155_410 = (FStar_List.fold_left FStar_TypeChecker_Rel.conj_guard f guards)
in ((c), (u_c), (_155_410))))))
end))
end))
end)))
end))
end)))))
end)))
and tc_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (_59_1128) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| FStar_Syntax_Syntax.U_unknown -> begin
(FStar_All.failwith "Unknown universe")
end
| (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_zero) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _155_415 = (aux u)
in FStar_Syntax_Syntax.U_succ (_155_415))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _155_416 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_155_416))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
if (env.FStar_TypeChecker_Env.use_bv_sorts || (FStar_TypeChecker_Env.lookup_univ env x)) then begin
u
end else begin
(let _155_420 = (let _155_419 = (let _155_418 = (FStar_Util.format1 "Universe variable \'%s\' not found" x.FStar_Ident.idText)
in (let _155_417 = (FStar_TypeChecker_Env.get_range env)
in ((_155_418), (_155_417))))
in FStar_Syntax_Syntax.Error (_155_419))
in (Prims.raise _155_420))
end
end)))
in (match (u) with
| FStar_Syntax_Syntax.U_unknown -> begin
(let _155_421 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _155_421 Prims.snd))
end
| _59_1143 -> begin
(aux u)
end)))
and tc_abs : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top bs body -> (

let fail = (fun msg t -> (let _155_430 = (let _155_429 = (let _155_428 = (FStar_TypeChecker_Errors.expected_a_term_of_type_t_got_a_function env msg t top)
in ((_155_428), (top.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_155_429))
in (Prims.raise _155_430)))
in (

let check_binders = (fun env bs bs_expected -> (

let rec aux = (fun _59_1161 bs bs_expected -> (match (_59_1161) with
| (env, out, g, subst) -> begin
(match (((bs), (bs_expected))) with
| ([], []) -> begin
((env), ((FStar_List.rev out)), (None), (g), (subst))
end
| (((hd, imp))::bs, ((hd_expected, imp'))::bs_expected) -> begin
(

let _59_1192 = (match (((imp), (imp'))) with
| ((None, Some (FStar_Syntax_Syntax.Implicit (_)))) | ((Some (FStar_Syntax_Syntax.Implicit (_)), None)) -> begin
(let _155_447 = (let _155_446 = (let _155_445 = (let _155_443 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.format1 "Inconsistent implicit argument annotation on argument %s" _155_443))
in (let _155_444 = (FStar_Syntax_Syntax.range_of_bv hd)
in ((_155_445), (_155_444))))
in FStar_Syntax_Syntax.Error (_155_446))
in (Prims.raise _155_447))
end
| _59_1191 -> begin
()
end)
in (

let expected_t = (FStar_Syntax_Subst.subst subst hd_expected.FStar_Syntax_Syntax.sort)
in (

let _59_1209 = (match ((let _155_448 = (FStar_Syntax_Util.unmeta hd.FStar_Syntax_Syntax.sort)
in _155_448.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
((expected_t), (g))
end
| _59_1197 -> begin
(

let _59_1198 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_449 = (FStar_Syntax_Print.bv_to_string hd)
in (FStar_Util.print1 "Checking binder %s\n" _155_449))
end else begin
()
end
in (

let _59_1204 = (tc_tot_or_gtot_term env hd.FStar_Syntax_Syntax.sort)
in (match (_59_1204) with
| (t, _59_1202, g1) -> begin
(

let g2 = (let _155_451 = (FStar_TypeChecker_Env.get_range env)
in (let _155_450 = (FStar_TypeChecker_Rel.teq env t expected_t)
in (FStar_TypeChecker_Util.label_guard _155_451 "Type annotation on parameter incompatible with the expected type" _155_450)))
in (

let g = (let _155_452 = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in (FStar_TypeChecker_Rel.conj_guard g _155_452))
in ((t), (g))))
end)))
end)
in (match (_59_1209) with
| (t, g) -> begin
(

let hd = (

let _59_1210 = hd
in {FStar_Syntax_Syntax.ppname = _59_1210.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1210.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})
in (

let b = ((hd), (imp))
in (

let b_expected = ((hd_expected), (imp'))
in (

let env = (push_binding env b)
in (

let subst = (let _155_453 = (FStar_Syntax_Syntax.bv_to_name hd)
in (maybe_extend_subst subst b_expected _155_453))
in (aux ((env), ((b)::out), (g), (subst)) bs bs_expected))))))
end))))
end
| (rest, []) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inl (rest))), (g), (subst))
end
| ([], rest) -> begin
((env), ((FStar_List.rev out)), (Some (FStar_Util.Inr (rest))), (g), (subst))
end)
end))
in (aux ((env), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs bs_expected)))
in (

let rec expected_function_typ = (fun env t0 body -> (match (t0) with
| None -> begin
(

let _59_1231 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _59_1230 -> begin
(FStar_All.failwith "Impossible: Can\'t have a let rec annotation but no expected type")
end)
in (

let _59_1238 = (tc_binders env bs)
in (match (_59_1238) with
| (bs, envbody, g, _59_1237) -> begin
(

let _59_1256 = (match ((let _155_460 = (FStar_Syntax_Subst.compress body)
in _155_460.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), _59_1243) -> begin
(

let _59_1250 = (tc_comp envbody c)
in (match (_59_1250) with
| (c, _59_1248, g') -> begin
(let _155_461 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((Some (c)), (body), (_155_461)))
end))
end
| _59_1252 -> begin
((None), (body), (g))
end)
in (match (_59_1256) with
| (copt, body, g) -> begin
((None), (bs), ([]), (copt), (envbody), (body), (g))
end))
end)))
end
| Some (t) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let rec as_function_typ = (fun norm t -> (match ((let _155_466 = (FStar_Syntax_Subst.compress t)
in _155_466.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let _59_1283 = (match (env.FStar_TypeChecker_Env.letrecs) with
| [] -> begin
()
end
| _59_1282 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let _59_1290 = (tc_binders env bs)
in (match (_59_1290) with
| (bs, envbody, g, _59_1289) -> begin
(

let _59_1294 = (FStar_TypeChecker_Env.clear_expected_typ envbody)
in (match (_59_1294) with
| (envbody, _59_1293) -> begin
((Some (((t), (true)))), (bs), ([]), (None), (envbody), (body), (g))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (b, _59_1297) -> begin
(

let _59_1308 = (as_function_typ norm b.FStar_Syntax_Syntax.sort)
in (match (_59_1308) with
| (_59_1301, bs, bs', copt, env, body, g) -> begin
((Some (((t), (false)))), (bs), (bs'), (copt), (env), (body), (g))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _59_1315 = (FStar_Syntax_Subst.open_comp bs_expected c_expected)
in (match (_59_1315) with
| (bs_expected, c_expected) -> begin
(

let check_actuals_against_formals = (fun env bs bs_expected -> (

let rec handle_more = (fun _59_1326 c_expected -> (match (_59_1326) with
| (env, bs, more, guard, subst) -> begin
(match (more) with
| None -> begin
(let _155_477 = (FStar_Syntax_Subst.subst_comp subst c_expected)
in ((env), (bs), (guard), (_155_477)))
end
| Some (FStar_Util.Inr (more_bs_expected)) -> begin
(

let c = (let _155_478 = (FStar_Syntax_Util.arrow more_bs_expected c_expected)
in (FStar_Syntax_Syntax.mk_Total _155_478))
in (let _155_479 = (FStar_Syntax_Subst.subst_comp subst c)
in ((env), (bs), (guard), (_155_479))))
end
| Some (FStar_Util.Inl (more_bs)) -> begin
(

let c = (FStar_Syntax_Subst.subst_comp subst c_expected)
in if (FStar_Syntax_Util.is_total_comp c) then begin
(

let t = (unfold_whnf env (FStar_Syntax_Util.comp_result c))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs_expected, c_expected) -> begin
(

let _59_1347 = (check_binders env more_bs bs_expected)
in (match (_59_1347) with
| (env, bs', more, guard', subst) -> begin
(let _155_481 = (let _155_480 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((env), ((FStar_List.append bs bs')), (more), (_155_480), (subst)))
in (handle_more _155_481 c_expected))
end))
end
| _59_1349 -> begin
(let _155_483 = (let _155_482 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "More arguments than annotated type (%s)" _155_482))
in (fail _155_483 t))
end))
end else begin
(fail "Function definition takes more arguments than expected from its annotated type" t)
end)
end)
end))
in (let _155_484 = (check_binders env bs bs_expected)
in (handle_more _155_484 c_expected))))
in (

let mk_letrec_env = (fun envbody bs c -> (

let letrecs = (guard_letrecs envbody bs c)
in (

let envbody = (

let _59_1355 = envbody
in {FStar_TypeChecker_Env.solver = _59_1355.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1355.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1355.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1355.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1355.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1355.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1355.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1355.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1355.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1355.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1355.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1355.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = []; FStar_TypeChecker_Env.top_level = _59_1355.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1355.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1355.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1355.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1355.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1355.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1355.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1355.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1355.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1355.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1355.FStar_TypeChecker_Env.qname_and_index})
in (FStar_All.pipe_right letrecs (FStar_List.fold_left (fun _59_1360 _59_1363 -> (match (((_59_1360), (_59_1363))) with
| ((env, letrec_binders), (l, t)) -> begin
(

let _59_1369 = (let _155_494 = (let _155_493 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _155_493 Prims.fst))
in (tc_term _155_494 t))
in (match (_59_1369) with
| (t, _59_1366, _59_1368) -> begin
(

let env = (FStar_TypeChecker_Env.push_let_binding env l (([]), (t)))
in (

let lb = (match (l) with
| FStar_Util.Inl (x) -> begin
(let _155_495 = (FStar_Syntax_Syntax.mk_binder (

let _59_1373 = x
in {FStar_Syntax_Syntax.ppname = _59_1373.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1373.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_155_495)::letrec_binders)
end
| _59_1376 -> begin
letrec_binders
end)
in ((env), (lb))))
end))
end)) ((envbody), ([])))))))
in (

let _59_1382 = (check_actuals_against_formals env bs bs_expected)
in (match (_59_1382) with
| (envbody, bs, g, c) -> begin
(

let _59_1385 = if (FStar_TypeChecker_Env.should_verify env) then begin
(mk_letrec_env envbody bs c)
end else begin
((envbody), ([]))
end
in (match (_59_1385) with
| (envbody, letrecs) -> begin
(

let envbody = (FStar_TypeChecker_Env.set_expected_typ envbody (FStar_Syntax_Util.comp_result c))
in ((Some (((t), (false)))), (bs), (letrecs), (Some (c)), (envbody), (body), (g)))
end))
end))))
end))
end
| _59_1388 -> begin
if (not (norm)) then begin
(let _155_496 = (unfold_whnf env t)
in (as_function_typ true _155_496))
end else begin
(

let _59_1398 = (expected_function_typ env None body)
in (match (_59_1398) with
| (_59_1390, bs, _59_1393, c_opt, envbody, body, g) -> begin
((Some (((t), (false)))), (bs), ([]), (c_opt), (envbody), (body), (g))
end))
end
end))
in (as_function_typ false t)))
end))
in (

let use_eq = env.FStar_TypeChecker_Env.use_eq
in (

let _59_1402 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_1402) with
| (env, topt) -> begin
(

let _59_1406 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_497 = (match (topt) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Syntax_Print.term_to_string t)
end)
in (FStar_Util.print2 "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n" _155_497 (if env.FStar_TypeChecker_Env.top_level then begin
"true"
end else begin
"false"
end)))
end else begin
()
end
in (

let _59_1415 = (expected_function_typ env topt body)
in (match (_59_1415) with
| (tfun_opt, bs, letrec_binders, c_opt, envbody, body, g) -> begin
(

let _59_1421 = (tc_term (

let _59_1416 = envbody
in {FStar_TypeChecker_Env.solver = _59_1416.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1416.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1416.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1416.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1416.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1416.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1416.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1416.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1416.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1416.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1416.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1416.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1416.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_1416.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _59_1416.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1416.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1416.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1416.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1416.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1416.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1416.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1416.FStar_TypeChecker_Env.qname_and_index}) body)
in (match (_59_1421) with
| (body, cbody, guard_body) -> begin
(

let guard_body = (FStar_TypeChecker_Rel.solve_deferred_constraints envbody guard_body)
in (

let _59_1423 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits"))) then begin
(let _155_500 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length guard_body.FStar_TypeChecker_Env.implicits))
in (let _155_499 = (let _155_498 = (cbody.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left FStar_Syntax_Print.comp_to_string _155_498))
in (FStar_Util.print2 "Introduced %s implicits in body of abstraction\nAfter solving constraints, cbody is %s\n" _155_500 _155_499)))
end else begin
()
end
in (

let _59_1430 = (let _155_502 = (let _155_501 = (cbody.FStar_Syntax_Syntax.comp ())
in ((body), (_155_501)))
in (check_expected_effect (

let _59_1425 = envbody
in {FStar_TypeChecker_Env.solver = _59_1425.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1425.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1425.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1425.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1425.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1425.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1425.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1425.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1425.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1425.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1425.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1425.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1425.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1425.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1425.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = use_eq; FStar_TypeChecker_Env.is_iface = _59_1425.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1425.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1425.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1425.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1425.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1425.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1425.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1425.FStar_TypeChecker_Env.qname_and_index}) c_opt _155_502))
in (match (_59_1430) with
| (body, cbody, guard) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard guard_body guard)
in (

let guard = if (env.FStar_TypeChecker_Env.top_level || (not ((FStar_TypeChecker_Env.should_verify env)))) then begin
(let _155_503 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.discharge_guard envbody _155_503))
end else begin
(

let guard = (let _155_504 = (FStar_TypeChecker_Rel.conj_guard g guard)
in (FStar_TypeChecker_Rel.close_guard (FStar_List.append bs letrec_binders) _155_504))
in guard)
end
in (

let tfun_computed = (FStar_Syntax_Util.arrow bs cbody)
in (

let e = (let _155_507 = (let _155_506 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp cbody) (fun _155_505 -> FStar_Util.Inl (_155_505)))
in Some (_155_506))
in (FStar_Syntax_Util.abs bs body _155_507))
in (

let _59_1453 = (match (tfun_opt) with
| Some (t, use_teq) -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_59_1442) -> begin
((e), (t), (guard))
end
| _59_1445 -> begin
(

let _59_1448 = if use_teq then begin
(let _155_508 = (FStar_TypeChecker_Rel.teq env t tfun_computed)
in ((e), (_155_508)))
end else begin
(FStar_TypeChecker_Util.check_and_ascribe env e tfun_computed t)
end
in (match (_59_1448) with
| (e, guard') -> begin
(let _155_509 = (FStar_TypeChecker_Rel.conj_guard guard guard')
in ((e), (t), (_155_509)))
end))
end))
end
| None -> begin
((e), (tfun_computed), (guard))
end)
in (match (_59_1453) with
| (e, tfun, guard) -> begin
(

let c = if env.FStar_TypeChecker_Env.top_level then begin
(FStar_Syntax_Syntax.mk_Total tfun)
end else begin
(FStar_TypeChecker_Util.return_value env tfun e)
end
in (

let _59_1457 = (FStar_TypeChecker_Util.strengthen_precondition None env e (FStar_Syntax_Util.lcomp_of_comp c) guard)
in (match (_59_1457) with
| (c, g) -> begin
((e), (c), (g))
end)))
end))))))
end))))
end))
end)))
end)))))))
and check_application_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead ghead args expected_topt -> (

let n_args = (FStar_List.length args)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let thead = chead.FStar_Syntax_Syntax.res_typ
in (

let _59_1467 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_518 = (FStar_Range.string_of_range head.FStar_Syntax_Syntax.pos)
in (let _155_517 = (FStar_Syntax_Print.term_to_string thead)
in (FStar_Util.print2 "(%s) Type of head is %s\n" _155_518 _155_517)))
end else begin
()
end
in (

let monadic_application = (fun _59_1474 subst arg_comps_rev arg_rets guard fvs bs -> (match (_59_1474) with
| (head, chead, ghead, cres) -> begin
(

let rt = (check_no_escape (Some (head)) env fvs cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _59_1482 = cres
in {FStar_Syntax_Syntax.eff_name = _59_1482.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = rt; FStar_Syntax_Syntax.cflags = _59_1482.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_1482.FStar_Syntax_Syntax.comp})
in (

let _59_1513 = (match (bs) with
| [] -> begin
(

let cres = (FStar_TypeChecker_Util.subst_lcomp subst cres)
in (

let g = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (

let refine_with_equality = ((FStar_Syntax_Util.is_pure_or_ghost_lcomp cres) && (FStar_All.pipe_right arg_comps_rev (FStar_Util.for_some (fun _59_5 -> (match (_59_5) with
| (_59_1490, _59_1492, FStar_Util.Inl (_59_1494)) -> begin
false
end
| (_59_1498, _59_1500, FStar_Util.Inr (c)) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c)))
end)))))
in (

let cres = if refine_with_equality then begin
(let _155_534 = (FStar_Syntax_Syntax.mk_Tm_app head (FStar_List.rev arg_rets) (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term env _155_534 cres))
end else begin
(

let _59_1505 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_537 = (FStar_Syntax_Print.term_to_string head)
in (let _155_536 = (FStar_Syntax_Print.lcomp_to_string cres)
in (let _155_535 = (FStar_TypeChecker_Rel.guard_to_string env g)
in (FStar_Util.print3 "Not refining result: f=%s; cres=%s; guard=%s\n" _155_537 _155_536 _155_535))))
end else begin
()
end
in cres)
end
in ((cres), (g))))))
end
| _59_1509 -> begin
(

let g = (let _155_538 = (FStar_TypeChecker_Rel.conj_guard ghead guard)
in (FStar_All.pipe_right _155_538 (FStar_TypeChecker_Rel.solve_deferred_constraints env)))
in (let _155_543 = (let _155_542 = (let _155_541 = (let _155_540 = (let _155_539 = (cres.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Util.arrow bs _155_539))
in (FStar_All.pipe_left (FStar_Syntax_Subst.subst subst) _155_540))
in (FStar_Syntax_Syntax.mk_Total _155_541))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_542))
in ((_155_543), (g))))
end)
in (match (_59_1513) with
| (cres, guard) -> begin
(

let _59_1514 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_544 = (FStar_Syntax_Print.lcomp_to_string cres)
in (FStar_Util.print1 "\t Type of result cres is %s\n" _155_544))
end else begin
()
end
in (

let _59_1537 = (FStar_List.fold_left (fun _59_1519 _59_1525 -> (match (((_59_1519), (_59_1525))) with
| ((args, out_c, monadic), ((e, q), x, c)) -> begin
(match (c) with
| FStar_Util.Inl (eff_name) -> begin
(let _155_549 = (let _155_548 = (let _155_547 = (FStar_TypeChecker_Util.maybe_lift env e eff_name out_c.FStar_Syntax_Syntax.eff_name)
in ((_155_547), (q)))
in (_155_548)::args)
in ((_155_549), (out_c), (monadic)))
end
| FStar_Util.Inr (c) -> begin
(

let monadic = (monadic || (not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp c))))
in (

let out_c = (FStar_TypeChecker_Util.bind e.FStar_Syntax_Syntax.pos env None c ((x), (out_c)))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e c.FStar_Syntax_Syntax.eff_name c.FStar_Syntax_Syntax.res_typ)
in (

let e = (FStar_TypeChecker_Util.maybe_lift env e c.FStar_Syntax_Syntax.eff_name out_c.FStar_Syntax_Syntax.eff_name)
in (((((e), (q)))::args), (out_c), (monadic))))))
end)
end)) (([]), (cres), (false)) arg_comps_rev)
in (match (_59_1537) with
| (args, comp, monadic) -> begin
(

let comp = (FStar_TypeChecker_Util.bind head.FStar_Syntax_Syntax.pos env None chead ((None), (comp)))
in (

let app = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (

let app = if monadic then begin
(FStar_TypeChecker_Util.maybe_monadic env app comp.FStar_Syntax_Syntax.eff_name comp.FStar_Syntax_Syntax.res_typ)
end else begin
app
end
in (

let _59_1543 = (FStar_TypeChecker_Util.strengthen_precondition None env app comp guard)
in (match (_59_1543) with
| (comp, g) -> begin
((app), (comp), (g))
end)))))
end)))
end))))
end))
in (

let rec tc_args = (fun head_info _59_1551 bs args -> (match (_59_1551) with
| (subst, outargs, arg_rets, g, fvs) -> begin
(match (((bs), (args))) with
| (((x, Some (FStar_Syntax_Syntax.Implicit (_59_1557))))::rest, ((_59_1565, None))::_59_1563) -> begin
(

let t = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let t = (check_no_escape (Some (head)) env fvs t)
in (

let _59_1576 = (FStar_TypeChecker_Util.new_implicit_var "Instantiating implicit argument in application" head.FStar_Syntax_Syntax.pos env t)
in (match (_59_1576) with
| (varg, _59_1574, implicits) -> begin
(

let subst = (FStar_Syntax_Syntax.NT (((x), (varg))))::subst
in (

let arg = (let _155_559 = (FStar_Syntax_Syntax.as_implicit true)
in ((varg), (_155_559)))
in (let _155_561 = (let _155_560 = (FStar_TypeChecker_Rel.conj_guard implicits g)
in ((subst), ((((arg), (None), (FStar_Util.Inl (FStar_Syntax_Const.effect_Tot_lid))))::outargs), ((arg)::arg_rets), (_155_560), (fvs)))
in (tc_args head_info _155_561 rest args))))
end))))
end
| (((x, aqual))::rest, ((e, aq))::rest') -> begin
(

let _59_1608 = (match (((aqual), (aq))) with
| ((Some (FStar_Syntax_Syntax.Implicit (_)), Some (FStar_Syntax_Syntax.Implicit (_)))) | ((None, None)) | ((Some (FStar_Syntax_Syntax.Equality), None)) -> begin
()
end
| _59_1607 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifier"), (e.FStar_Syntax_Syntax.pos)))))
end)
in (

let targ = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (

let x = (

let _59_1611 = x
in {FStar_Syntax_Syntax.ppname = _59_1611.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1611.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = targ})
in (

let _59_1614 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_562 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print1 "\tType of arg (after subst) = %s\n" _155_562))
end else begin
()
end
in (

let targ = (check_no_escape (Some (head)) env fvs targ)
in (

let env = (FStar_TypeChecker_Env.set_expected_typ env targ)
in (

let env = (

let _59_1618 = env
in {FStar_TypeChecker_Env.solver = _59_1618.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1618.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1618.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1618.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1618.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1618.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1618.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1618.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_1618.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_1618.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1618.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1618.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1618.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1618.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1618.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = (is_eq aqual); FStar_TypeChecker_Env.is_iface = _59_1618.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1618.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1618.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1618.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1618.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1618.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1618.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1618.FStar_TypeChecker_Env.qname_and_index})
in (

let _59_1621 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_565 = (FStar_Syntax_Print.tag_of_term e)
in (let _155_564 = (FStar_Syntax_Print.term_to_string e)
in (let _155_563 = (FStar_Syntax_Print.term_to_string targ)
in (FStar_Util.print3 "Checking arg (%s) %s at type %s\n" _155_565 _155_564 _155_563))))
end else begin
()
end
in (

let _59_1626 = (tc_term env e)
in (match (_59_1626) with
| (e, c, g_e) -> begin
(

let g = (FStar_TypeChecker_Rel.conj_guard g g_e)
in (

let arg = ((e), (aq))
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
(

let subst = (let _155_566 = (FStar_List.hd bs)
in (maybe_extend_subst subst _155_566 e))
in (tc_args head_info ((subst), ((((arg), (None), (FStar_Util.Inl (c.FStar_Syntax_Syntax.eff_name))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (FStar_TypeChecker_Util.is_pure_or_ghost_effect env c.FStar_Syntax_Syntax.eff_name) then begin
(

let subst = (let _155_567 = (FStar_List.hd bs)
in (maybe_extend_subst subst _155_567 e))
in (tc_args head_info ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), ((arg)::arg_rets), (g), (fvs)) rest rest'))
end else begin
if (let _155_568 = (FStar_List.hd bs)
in (FStar_Syntax_Syntax.is_null_binder _155_568)) then begin
(

let newx = (FStar_Syntax_Syntax.new_bv (Some (e.FStar_Syntax_Syntax.pos)) c.FStar_Syntax_Syntax.res_typ)
in (

let arg' = (let _155_569 = (FStar_Syntax_Syntax.bv_to_name newx)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_569))
in (tc_args head_info ((subst), ((((arg), (Some (newx)), (FStar_Util.Inr (c))))::outargs), ((arg')::arg_rets), (g), (fvs)) rest rest')))
end else begin
(let _155_573 = (let _155_572 = (let _155_571 = (let _155_570 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg _155_570))
in (_155_571)::arg_rets)
in ((subst), ((((arg), (Some (x)), (FStar_Util.Inr (c))))::outargs), (_155_572), (g), ((x)::fvs)))
in (tc_args head_info _155_573 rest rest'))
end
end
end))
end))))))))))
end
| (_59_1634, []) -> begin
(monadic_application head_info subst outargs arg_rets g fvs bs)
end
| ([], (arg)::_59_1639) -> begin
(

let _59_1646 = (monadic_application head_info subst outargs arg_rets g fvs [])
in (match (_59_1646) with
| (head, chead, ghead) -> begin
(

let rec aux = (fun norm tres -> (

let tres = (let _155_578 = (FStar_Syntax_Subst.compress tres)
in (FStar_All.pipe_right _155_578 FStar_Syntax_Util.unrefine))
in (match (tres.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, cres') -> begin
(

let _59_1657 = (FStar_Syntax_Subst.open_comp bs cres')
in (match (_59_1657) with
| (bs, cres') -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp cres')))
in (

let _59_1659 = if (FStar_TypeChecker_Env.debug env FStar_Options.Low) then begin
(let _155_579 = (FStar_Range.string_of_range tres.FStar_Syntax_Syntax.pos)
in (FStar_Util.print1 "%s: Warning: Potentially redundant explicit currying of a function type \n" _155_579))
end else begin
()
end
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args)))
end))
end
| _59_1662 when (not (norm)) -> begin
(let _155_580 = (unfold_whnf env tres)
in (aux true _155_580))
end
| _59_1664 -> begin
(let _155_586 = (let _155_585 = (let _155_584 = (let _155_582 = (FStar_TypeChecker_Normalize.term_to_string env thead)
in (let _155_581 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format2 "Too many arguments to function of type %s; got %s arguments" _155_582 _155_581)))
in (let _155_583 = (FStar_Syntax_Syntax.argpos arg)
in ((_155_584), (_155_583))))
in FStar_Syntax_Syntax.Error (_155_585))
in (Prims.raise _155_586))
end)))
in (aux false chead.FStar_Syntax_Syntax.res_typ))
end))
end)
end))
in (

let rec check_function_app = (fun norm tf -> (match ((let _155_591 = (FStar_Syntax_Util.unrefine tf)
in _155_591.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let rec tc_args = (fun env args -> (match (args) with
| [] -> begin
(([]), ([]), (FStar_TypeChecker_Rel.trivial_guard))
end
| ((e, imp))::tl -> begin
(

let _59_1697 = (tc_term env e)
in (match (_59_1697) with
| (e, c, g_e) -> begin
(

let _59_1701 = (tc_args env tl)
in (match (_59_1701) with
| (args, comps, g_rest) -> begin
(let _155_596 = (FStar_TypeChecker_Rel.conj_guard g_e g_rest)
in (((((e), (imp)))::args), ((((e.FStar_Syntax_Syntax.pos), (c)))::comps), (_155_596)))
end))
end))
end))
in (

let _59_1705 = (tc_args env args)
in (match (_59_1705) with
| (args, comps, g_args) -> begin
(

let bs = (let _155_598 = (FStar_All.pipe_right comps (FStar_List.map (fun _59_1709 -> (match (_59_1709) with
| (_59_1707, c) -> begin
((c.FStar_Syntax_Syntax.res_typ), (None))
end))))
in (FStar_Syntax_Util.null_binders_of_tks _155_598))
in (

let ml_or_tot = (match ((FStar_TypeChecker_Env.try_lookup_effect_lid env FStar_Syntax_Const.effect_ML_lid)) with
| None -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_Total t))
end
| _59_1715 -> begin
FStar_Syntax_Util.ml_comp
end)
in (

let ml_or_tot = (match (expected_topt) with
| None -> begin
ml_or_tot
end
| Some (t) -> begin
(match ((let _155_613 = (FStar_Syntax_Subst.compress t)
in _155_613.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (_59_1721) -> begin
(fun t r -> (FStar_Syntax_Syntax.mk_GTotal t))
end
| _59_1726 -> begin
ml_or_tot
end)
end)
in (

let cres = (let _155_618 = (let _155_617 = (let _155_616 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _155_616 Prims.fst))
in (FStar_TypeChecker_Util.new_uvar env _155_617))
in (ml_or_tot _155_618 r))
in (

let bs_cres = (FStar_Syntax_Util.arrow bs cres)
in (

let _59_1730 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) FStar_Options.Extreme) then begin
(let _155_621 = (FStar_Syntax_Print.term_to_string head)
in (let _155_620 = (FStar_Syntax_Print.term_to_string tf)
in (let _155_619 = (FStar_Syntax_Print.term_to_string bs_cres)
in (FStar_Util.print3 "Forcing the type of %s from %s to %s\n" _155_621 _155_620 _155_619))))
end else begin
()
end
in (

let _59_1732 = (let _155_622 = (FStar_TypeChecker_Rel.teq env tf bs_cres)
in (FStar_All.pipe_left (FStar_TypeChecker_Rel.force_trivial_guard env) _155_622))
in (

let comp = (let _155_625 = (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp cres)
in (FStar_List.fold_right (fun _59_1736 out -> (match (_59_1736) with
| (r1, c) -> begin
(FStar_TypeChecker_Util.bind r1 env None c ((None), (out)))
end)) ((((head.FStar_Syntax_Syntax.pos), (chead)))::comps) _155_625))
in (let _155_627 = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (comp.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) r)
in (let _155_626 = (FStar_TypeChecker_Rel.conj_guard ghead g_args)
in ((_155_627), (comp), (_155_626))))))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _59_1745 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_1745) with
| (bs, c) -> begin
(

let head_info = ((head), (chead), (ghead), ((FStar_Syntax_Util.lcomp_of_comp c)))
in (tc_args head_info (([]), ([]), ([]), (FStar_TypeChecker_Rel.trivial_guard), ([])) bs args))
end))
end
| _59_1748 -> begin
if (not (norm)) then begin
(let _155_628 = (unfold_whnf env tf)
in (check_function_app true _155_628))
end else begin
(let _155_631 = (let _155_630 = (let _155_629 = (FStar_TypeChecker_Errors.expected_function_typ env tf)
in ((_155_629), (head.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_155_630))
in (Prims.raise _155_631))
end
end))
in (let _155_633 = (let _155_632 = (FStar_Syntax_Util.unrefine thead)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _155_632))
in (check_function_app false _155_633))))))))))
and check_short_circuit_args : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.typ Prims.option  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env head chead g_head args expected_topt -> (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let tf = (FStar_Syntax_Subst.compress chead.FStar_Syntax_Syntax.res_typ)
in (match (tf.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) when ((FStar_Syntax_Util.is_total_comp c) && ((FStar_List.length bs) = (FStar_List.length args))) -> begin
(

let res_t = (FStar_Syntax_Util.comp_result c)
in (

let _59_1784 = (FStar_List.fold_left2 (fun _59_1765 _59_1768 _59_1771 -> (match (((_59_1765), (_59_1768), (_59_1771))) with
| ((seen, guard, ghost), (e, aq), (b, aq')) -> begin
(

let _59_1772 = if (aq <> aq') then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inconsistent implicit qualifiers"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _59_1777 = (tc_check_tot_or_gtot_term env e b.FStar_Syntax_Syntax.sort)
in (match (_59_1777) with
| (e, c, g) -> begin
(

let short = (FStar_TypeChecker_Util.short_circuit head seen)
in (

let g = (let _155_643 = (FStar_TypeChecker_Rel.guard_of_guard_formula short)
in (FStar_TypeChecker_Rel.imp_guard _155_643 g))
in (

let ghost = (ghost || ((not ((FStar_Syntax_Util.is_total_lcomp c))) && (not ((FStar_TypeChecker_Util.is_pure_effect env c.FStar_Syntax_Syntax.eff_name)))))
in (let _155_647 = (let _155_645 = (let _155_644 = (FStar_Syntax_Syntax.as_arg e)
in (_155_644)::[])
in (FStar_List.append seen _155_645))
in (let _155_646 = (FStar_TypeChecker_Rel.conj_guard guard g)
in ((_155_647), (_155_646), (ghost)))))))
end)))
end)) (([]), (g_head), (false)) args bs)
in (match (_59_1784) with
| (args, guard, ghost) -> begin
(

let e = (FStar_Syntax_Syntax.mk_Tm_app head args (Some (res_t.FStar_Syntax_Syntax.n)) r)
in (

let c = if ghost then begin
(let _155_648 = (FStar_Syntax_Syntax.mk_GTotal res_t)
in (FStar_All.pipe_right _155_648 FStar_Syntax_Util.lcomp_of_comp))
end else begin
(FStar_Syntax_Util.lcomp_of_comp c)
end
in (

let _59_1789 = (FStar_TypeChecker_Util.strengthen_precondition None env e c guard)
in (match (_59_1789) with
| (c, g) -> begin
((e), (c), (g))
end))))
end)))
end
| _59_1791 -> begin
(check_application_args env head chead g_head args expected_topt)
end))))
and tc_eqn : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.branch  ->  ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun scrutinee env branch -> (

let _59_1798 = (FStar_Syntax_Subst.open_branch branch)
in (match (_59_1798) with
| (pattern, when_clause, branch_exp) -> begin
(

let _59_1803 = branch
in (match (_59_1803) with
| (cpat, _59_1801, cbr) -> begin
(

let tc_pat = (fun allow_implicits pat_t p0 -> (

let _59_1811 = (FStar_TypeChecker_Util.pat_as_exps allow_implicits env p0)
in (match (_59_1811) with
| (pat_bvs, exps, p) -> begin
(

let _59_1812 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_660 = (FStar_Syntax_Print.pat_to_string p0)
in (let _155_659 = (FStar_Syntax_Print.pat_to_string p)
in (FStar_Util.print2 "Pattern %s elaborated to %s\n" _155_660 _155_659)))
end else begin
()
end
in (

let pat_env = (FStar_List.fold_left FStar_TypeChecker_Env.push_bv env pat_bvs)
in (

let _59_1818 = (FStar_TypeChecker_Env.clear_expected_typ pat_env)
in (match (_59_1818) with
| (env1, _59_1817) -> begin
(

let env1 = (

let _59_1819 = env1
in {FStar_TypeChecker_Env.solver = _59_1819.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_1819.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_1819.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_1819.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_1819.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_1819.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_1819.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_1819.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = true; FStar_TypeChecker_Env.instantiate_imp = _59_1819.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_1819.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_1819.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_1819.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_1819.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_1819.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_1819.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_1819.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_1819.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_1819.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_1819.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_1819.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_1819.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_1819.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_1819.FStar_TypeChecker_Env.qname_and_index})
in (

let expected_pat_t = (FStar_TypeChecker_Rel.unrefine env pat_t)
in (

let _59_1858 = (let _155_683 = (FStar_All.pipe_right exps (FStar_List.map (fun e -> (

let _59_1824 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_663 = (FStar_Syntax_Print.term_to_string e)
in (let _155_662 = (FStar_Syntax_Print.term_to_string pat_t)
in (FStar_Util.print2 "Checking pattern expression %s against expected type %s\n" _155_663 _155_662)))
end else begin
()
end
in (

let _59_1829 = (tc_term env1 e)
in (match (_59_1829) with
| (e, lc, g) -> begin
(

let _59_1830 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_665 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (let _155_664 = (FStar_TypeChecker_Normalize.term_to_string env lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Pre-checked pattern expression %s at type %s\n" _155_665 _155_664)))
end else begin
()
end
in (

let g' = (FStar_TypeChecker_Rel.teq env lc.FStar_Syntax_Syntax.res_typ expected_pat_t)
in (

let g = (FStar_TypeChecker_Rel.conj_guard g g')
in (

let _59_1836 = (let _155_666 = (FStar_TypeChecker_Rel.discharge_guard env (

let _59_1834 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _59_1834.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _59_1834.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _59_1834.FStar_TypeChecker_Env.implicits}))
in (FStar_All.pipe_right _155_666 FStar_TypeChecker_Rel.resolve_implicits))
in (

let e' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env e)
in (

let uvars_to_string = (fun uvs -> (let _155_671 = (let _155_670 = (FStar_All.pipe_right uvs FStar_Util.set_elements)
in (FStar_All.pipe_right _155_670 (FStar_List.map (fun _59_1844 -> (match (_59_1844) with
| (u, _59_1843) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end)))))
in (FStar_All.pipe_right _155_671 (FStar_String.concat ", "))))
in (

let uvs1 = (FStar_Syntax_Free.uvars e')
in (

let uvs2 = (FStar_Syntax_Free.uvars expected_pat_t)
in (

let _59_1852 = if (let _155_672 = (FStar_Util.set_is_subset_of uvs1 uvs2)
in (FStar_All.pipe_left Prims.op_Negation _155_672)) then begin
(

let unresolved = (let _155_673 = (FStar_Util.set_difference uvs1 uvs2)
in (FStar_All.pipe_right _155_673 FStar_Util.set_elements))
in (let _155_681 = (let _155_680 = (let _155_679 = (let _155_678 = (FStar_TypeChecker_Normalize.term_to_string env e')
in (let _155_677 = (FStar_TypeChecker_Normalize.term_to_string env expected_pat_t)
in (let _155_676 = (let _155_675 = (FStar_All.pipe_right unresolved (FStar_List.map (fun _59_1851 -> (match (_59_1851) with
| (u, _59_1850) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _155_675 (FStar_String.concat ", ")))
in (FStar_Util.format3 "Implicit pattern variables in %s could not be resolved against expected type %s;Variables {%s} were unresolved; please bind them explicitly" _155_678 _155_677 _155_676))))
in ((_155_679), (p.FStar_Syntax_Syntax.p)))
in FStar_Syntax_Syntax.Error (_155_680))
in (Prims.raise _155_681)))
end else begin
()
end
in (

let _59_1854 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_682 = (FStar_TypeChecker_Normalize.term_to_string env e)
in (FStar_Util.print1 "Done checking pattern expression %s\n" _155_682))
end else begin
()
end
in ((e), (e'))))))))))))
end))))))
in (FStar_All.pipe_right _155_683 FStar_List.unzip))
in (match (_59_1858) with
| (exps, norm_exps) -> begin
(

let p = (FStar_TypeChecker_Util.decorate_pattern env p exps)
in ((p), (pat_bvs), (pat_env), (exps), (norm_exps)))
end))))
end))))
end)))
in (

let pat_t = scrutinee.FStar_Syntax_Syntax.sort
in (

let scrutinee_tm = (FStar_Syntax_Syntax.bv_to_name scrutinee)
in (

let _59_1865 = (let _155_684 = (FStar_TypeChecker_Env.push_bv env scrutinee)
in (FStar_All.pipe_right _155_684 FStar_TypeChecker_Env.clear_expected_typ))
in (match (_59_1865) with
| (scrutinee_env, _59_1864) -> begin
(

let _59_1871 = (tc_pat true pat_t pattern)
in (match (_59_1871) with
| (pattern, pat_bvs, pat_env, disj_exps, norm_disj_exps) -> begin
(

let _59_1881 = (match (when_clause) with
| None -> begin
((None), (FStar_TypeChecker_Rel.trivial_guard))
end
| Some (e) -> begin
if (FStar_TypeChecker_Env.should_verify env) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("When clauses are not yet supported in --verify mode; they will be some day"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
(

let _59_1878 = (let _155_685 = (FStar_TypeChecker_Env.set_expected_typ pat_env FStar_TypeChecker_Common.t_bool)
in (tc_term _155_685 e))
in (match (_59_1878) with
| (e, c, g) -> begin
((Some (e)), (g))
end))
end
end)
in (match (_59_1881) with
| (when_clause, g_when) -> begin
(

let _59_1885 = (tc_term pat_env branch_exp)
in (match (_59_1885) with
| (branch_exp, c, g_branch) -> begin
(

let when_condition = (match (when_clause) with
| None -> begin
None
end
| Some (w) -> begin
(let _155_687 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool w FStar_Syntax_Const.exp_true_bool)
in (FStar_All.pipe_left (fun _155_686 -> Some (_155_686)) _155_687))
end)
in (

let _59_1943 = (

let eqs = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
None
end else begin
(FStar_All.pipe_right disj_exps (FStar_List.fold_left (fun fopt e -> (

let e = (FStar_Syntax_Subst.compress e)
in (match (e.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
fopt
end
| _59_1903 -> begin
(

let clause = (FStar_Syntax_Util.mk_eq pat_t pat_t scrutinee_tm e)
in (match (fopt) with
| None -> begin
Some (clause)
end
| Some (f) -> begin
(let _155_691 = (FStar_Syntax_Util.mk_disj clause f)
in (FStar_All.pipe_left (fun _155_690 -> Some (_155_690)) _155_691))
end))
end))) None))
end
in (

let _59_1911 = (FStar_TypeChecker_Util.strengthen_precondition None env branch_exp c g_branch)
in (match (_59_1911) with
| (c, g_branch) -> begin
(

let _59_1938 = (match (((eqs), (when_condition))) with
| _59_1913 when (not ((FStar_TypeChecker_Env.should_verify env))) -> begin
((c), (g_when))
end
| (None, None) -> begin
((c), (g_when))
end
| (Some (f), None) -> begin
(

let gf = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula gf)
in (let _155_694 = (FStar_TypeChecker_Util.weaken_precondition env c gf)
in (let _155_693 = (FStar_TypeChecker_Rel.imp_guard g g_when)
in ((_155_694), (_155_693))))))
end
| (Some (f), Some (w)) -> begin
(

let g_f = FStar_TypeChecker_Common.NonTrivial (f)
in (

let g_fw = (let _155_695 = (FStar_Syntax_Util.mk_conj f w)
in FStar_TypeChecker_Common.NonTrivial (_155_695))
in (let _155_698 = (FStar_TypeChecker_Util.weaken_precondition env c g_fw)
in (let _155_697 = (let _155_696 = (FStar_TypeChecker_Rel.guard_of_guard_formula g_f)
in (FStar_TypeChecker_Rel.imp_guard _155_696 g_when))
in ((_155_698), (_155_697))))))
end
| (None, Some (w)) -> begin
(

let g_w = FStar_TypeChecker_Common.NonTrivial (w)
in (

let g = (FStar_TypeChecker_Rel.guard_of_guard_formula g_w)
in (let _155_699 = (FStar_TypeChecker_Util.weaken_precondition env c g_w)
in ((_155_699), (g_when)))))
end)
in (match (_59_1938) with
| (c_weak, g_when_weak) -> begin
(

let binders = (FStar_List.map FStar_Syntax_Syntax.mk_binder pat_bvs)
in (let _155_701 = (FStar_TypeChecker_Util.close_comp env pat_bvs c_weak)
in (let _155_700 = (FStar_TypeChecker_Rel.close_guard binders g_when_weak)
in ((_155_701), (_155_700), (g_branch)))))
end))
end)))
in (match (_59_1943) with
| (c, g_when, g_branch) -> begin
(

let branch_guard = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
FStar_Syntax_Util.t_true
end else begin
(

let rec build_branch_guard = (fun scrutinee_tm pat_exp -> (

let discriminate = (fun scrutinee_tm f -> if ((let _155_711 = (let _155_710 = (FStar_TypeChecker_Env.typ_of_datacon env f.FStar_Syntax_Syntax.v)
in (FStar_TypeChecker_Env.datacons_of_typ env _155_710))
in (FStar_List.length _155_711)) > (Prims.parse_int "1")) then begin
(

let disc = (let _155_712 = (FStar_Syntax_Util.mk_discriminator f.FStar_Syntax_Syntax.v)
in (FStar_Syntax_Syntax.fvar _155_712 FStar_Syntax_Syntax.Delta_equational None))
in (

let disc = (let _155_714 = (let _155_713 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_155_713)::[])
in (FStar_Syntax_Syntax.mk_Tm_app disc _155_714 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (let _155_715 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Util.t_bool FStar_Syntax_Util.t_bool disc FStar_Syntax_Const.exp_true_bool)
in (_155_715)::[])))
end else begin
[]
end)
in (

let fail = (fun _59_1953 -> (match (()) with
| () -> begin
(let _155_721 = (let _155_720 = (FStar_Range.string_of_range pat_exp.FStar_Syntax_Syntax.pos)
in (let _155_719 = (FStar_Syntax_Print.term_to_string pat_exp)
in (let _155_718 = (FStar_Syntax_Print.tag_of_term pat_exp)
in (FStar_Util.format3 "tc_eqn: Impossible (%s) %s (%s)" _155_720 _155_719 _155_718))))
in (FStar_All.failwith _155_721))
end))
in (

let rec head_constructor = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name
end
| FStar_Syntax_Syntax.Tm_uinst (t, _59_1960) -> begin
(head_constructor t)
end
| _59_1964 -> begin
(fail ())
end))
in (

let pat_exp = (let _155_724 = (FStar_Syntax_Subst.compress pat_exp)
in (FStar_All.pipe_right _155_724 FStar_Syntax_Util.unmeta))
in (match (pat_exp.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)) -> begin
[]
end
| FStar_Syntax_Syntax.Tm_constant (_59_1989) -> begin
(let _155_729 = (let _155_728 = (let _155_727 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (let _155_726 = (let _155_725 = (FStar_Syntax_Syntax.as_arg pat_exp)
in (_155_725)::[])
in (_155_727)::_155_726))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.teq _155_728 None scrutinee_tm.FStar_Syntax_Syntax.pos))
in (_155_729)::[])
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
(

let f = (head_constructor pat_exp)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(let _155_730 = (head_constructor pat_exp)
in (discriminate scrutinee_tm _155_730))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let f = (head_constructor head)
in if (not ((FStar_TypeChecker_Env.is_datacon env f.FStar_Syntax_Syntax.v))) then begin
[]
end else begin
(

let sub_term_guards = (let _155_736 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _59_2007 -> (match (_59_2007) with
| (ei, _59_2006) -> begin
(

let projector = (FStar_TypeChecker_Env.lookup_projector env f.FStar_Syntax_Syntax.v i)
in (match ((FStar_TypeChecker_Env.try_lookup_lid env projector)) with
| None -> begin
[]
end
| _59_2011 -> begin
(

let sub_term = (let _155_735 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projector f.FStar_Syntax_Syntax.p) FStar_Syntax_Syntax.Delta_equational None)
in (let _155_734 = (let _155_733 = (FStar_Syntax_Syntax.as_arg scrutinee_tm)
in (_155_733)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _155_735 _155_734 None f.FStar_Syntax_Syntax.p)))
in (build_branch_guard sub_term ei))
end))
end))))
in (FStar_All.pipe_right _155_736 FStar_List.flatten))
in (let _155_737 = (discriminate scrutinee_tm f)
in (FStar_List.append _155_737 sub_term_guards)))
end)
end
| _59_2015 -> begin
[]
end))))))
in (

let build_and_check_branch_guard = (fun scrutinee_tm pat -> if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
(FStar_TypeChecker_Util.fvar_const env FStar_Syntax_Const.true_lid)
end else begin
(

let t = (let _155_742 = (build_branch_guard scrutinee_tm pat)
in (FStar_All.pipe_left FStar_Syntax_Util.mk_conj_l _155_742))
in (

let _59_2023 = (FStar_Syntax_Util.type_u ())
in (match (_59_2023) with
| (k, _59_2022) -> begin
(

let _59_2029 = (tc_check_tot_or_gtot_term scrutinee_env t k)
in (match (_59_2029) with
| (t, _59_2026, _59_2028) -> begin
t
end))
end)))
end)
in (

let branch_guard = (let _155_743 = (FStar_All.pipe_right norm_disj_exps (FStar_List.map (build_and_check_branch_guard scrutinee_tm)))
in (FStar_All.pipe_right _155_743 FStar_Syntax_Util.mk_disj_l))
in (

let branch_guard = (match (when_condition) with
| None -> begin
branch_guard
end
| Some (w) -> begin
(FStar_Syntax_Util.mk_conj branch_guard w)
end)
in branch_guard))))
end
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g_when g_branch)
in (

let _59_2037 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_744 = (FStar_TypeChecker_Rel.guard_to_string env guard)
in (FStar_All.pipe_left (FStar_Util.print1 "Carrying guard from match: %s\n") _155_744))
end else begin
()
end
in (let _155_745 = (FStar_Syntax_Subst.close_branch ((pattern), (when_clause), (branch_exp)))
in ((_155_745), (branch_guard), (c), (guard))))))
end)))
end))
end))
end))
end)))))
end))
end)))
and check_top_level_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let _59_2054 = (check_let_bound_def true env lb)
in (match (_59_2054) with
| (e1, univ_vars, c1, g1, annotated) -> begin
(

let _59_2066 = if (annotated && (not (env.FStar_TypeChecker_Env.generalize))) then begin
((g1), (e1), (univ_vars), (c1))
end else begin
(

let g1 = (let _155_748 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g1)
in (FStar_All.pipe_right _155_748 FStar_TypeChecker_Rel.resolve_implicits))
in (

let _59_2061 = (let _155_752 = (let _155_751 = (let _155_750 = (let _155_749 = (c1.FStar_Syntax_Syntax.comp ())
in ((lb.FStar_Syntax_Syntax.lbname), (e1), (_155_749)))
in (_155_750)::[])
in (FStar_TypeChecker_Util.generalize env _155_751))
in (FStar_List.hd _155_752))
in (match (_59_2061) with
| (_59_2057, univs, e1, c1) -> begin
((g1), (e1), (univs), ((FStar_Syntax_Util.lcomp_of_comp c1)))
end)))
end
in (match (_59_2066) with
| (g1, e1, univ_vars, c1) -> begin
(

let _59_2077 = if (FStar_TypeChecker_Env.should_verify env) then begin
(

let _59_2069 = (FStar_TypeChecker_Util.check_top_level env g1 c1)
in (match (_59_2069) with
| (ok, c1) -> begin
if ok then begin
((e2), (c1))
end else begin
(

let _59_2070 = if (FStar_Options.warn_top_level_effects ()) then begin
(let _155_753 = (FStar_TypeChecker_Env.get_range env)
in (FStar_TypeChecker_Errors.warn _155_753 FStar_TypeChecker_Errors.top_level_effect))
end else begin
()
end
in (let _155_754 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((e2), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Masked_effect))))) None e2.FStar_Syntax_Syntax.pos)
in ((_155_754), (c1))))
end
end))
end else begin
(

let _59_2072 = (FStar_TypeChecker_Rel.force_trivial_guard env g1)
in (

let c = (let _155_755 = (c1.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_right _155_755 (FStar_TypeChecker_Normalize.normalize_comp ((FStar_TypeChecker_Normalize.Beta)::[]) env)))
in ((e2), (c))))
end
in (match (_59_2077) with
| (e2, c1) -> begin
(

let cres = (let _155_756 = (FStar_Syntax_Util.ml_comp FStar_TypeChecker_Common.t_unit e.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_756))
in (

let _59_2079 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let lb = (FStar_Syntax_Util.close_univs_and_mk_letbinding None lb.FStar_Syntax_Syntax.lbname univ_vars (FStar_Syntax_Util.comp_result c1) (FStar_Syntax_Util.comp_effect_name c1) e1)
in (let _155_757 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos)
in ((_155_757), (cres), (FStar_TypeChecker_Rel.trivial_guard))))))
end))
end))
end))
end
| _59_2083 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let env = (instantiate_both env)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), e2) -> begin
(

let env = (

let _59_2094 = env
in {FStar_TypeChecker_Env.solver = _59_2094.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2094.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2094.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2094.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2094.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2094.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2094.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2094.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2094.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2094.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2094.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2094.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2094.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_2094.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2094.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2094.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2094.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2094.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2094.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2094.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2094.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2094.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2094.FStar_TypeChecker_Env.qname_and_index})
in (

let _59_2103 = (let _155_761 = (let _155_760 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (FStar_All.pipe_right _155_760 Prims.fst))
in (check_let_bound_def false _155_761 lb))
in (match (_59_2103) with
| (e1, _59_2099, c1, g1, annotated) -> begin
(

let x = (

let _59_2104 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _59_2104.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_2104.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = c1.FStar_Syntax_Syntax.res_typ})
in (

let _59_2109 = (let _155_763 = (let _155_762 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_762)::[])
in (FStar_Syntax_Subst.open_term _155_763 e2))
in (match (_59_2109) with
| (xb, e2) -> begin
(

let xbinder = (FStar_List.hd xb)
in (

let x = (Prims.fst xbinder)
in (

let _59_2115 = (let _155_764 = (FStar_TypeChecker_Env.push_bv env x)
in (tc_term _155_764 e2))
in (match (_59_2115) with
| (e2, c2, g2) -> begin
(

let cres = (FStar_TypeChecker_Util.bind e1.FStar_Syntax_Syntax.pos env (Some (e1)) c1 ((Some (x)), (c2)))
in (

let e1 = (FStar_TypeChecker_Util.maybe_lift env e1 c1.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let e2 = (FStar_TypeChecker_Util.maybe_lift env e2 c2.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.eff_name)
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (x)) [] c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.eff_name e1)
in (

let e = (let _155_767 = (let _155_766 = (let _155_765 = (FStar_Syntax_Subst.close xb e2)
in ((((false), ((lb)::[]))), (_155_765)))
in FStar_Syntax_Syntax.Tm_let (_155_766))
in (FStar_Syntax_Syntax.mk _155_767 (Some (cres.FStar_Syntax_Syntax.res_typ.FStar_Syntax_Syntax.n)) e.FStar_Syntax_Syntax.pos))
in (

let e = (FStar_TypeChecker_Util.maybe_monadic env e cres.FStar_Syntax_Syntax.eff_name cres.FStar_Syntax_Syntax.res_typ)
in (

let x_eq_e1 = (let _155_770 = (let _155_769 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_eq c1.FStar_Syntax_Syntax.res_typ c1.FStar_Syntax_Syntax.res_typ _155_769 e1))
in (FStar_All.pipe_left (fun _155_768 -> FStar_TypeChecker_Common.NonTrivial (_155_768)) _155_770))
in (

let g2 = (let _155_772 = (let _155_771 = (FStar_TypeChecker_Rel.guard_of_guard_formula x_eq_e1)
in (FStar_TypeChecker_Rel.imp_guard _155_771 g2))
in (FStar_TypeChecker_Rel.close_guard xb _155_772))
in (

let guard = (FStar_TypeChecker_Rel.conj_guard g1 g2)
in if (let _155_773 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_Option.isSome _155_773)) then begin
(

let tt = (let _155_774 = (FStar_TypeChecker_Env.expected_typ env)
in (FStar_All.pipe_right _155_774 FStar_Option.get))
in (

let _59_2126 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _155_776 = (FStar_Syntax_Print.term_to_string tt)
in (let _155_775 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.print2 "Got expected type from env %s\ncres.res_typ=%s\n" _155_776 _155_775)))
end else begin
()
end
in ((e), (cres), (guard))))
end else begin
(

let t = (check_no_escape None env ((x)::[]) cres.FStar_Syntax_Syntax.res_typ)
in (

let _59_2129 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Exports"))) then begin
(let _155_778 = (FStar_Syntax_Print.term_to_string cres.FStar_Syntax_Syntax.res_typ)
in (let _155_777 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Checked %s has no escaping types; normalized to %s\n" _155_778 _155_777)))
end else begin
()
end
in ((e), ((

let _59_2131 = cres
in {FStar_Syntax_Syntax.eff_name = _59_2131.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_2131.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_2131.FStar_Syntax_Syntax.comp})), (guard))))
end)))))))))
end))))
end)))
end)))
end
| _59_2134 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_top_level_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _59_2146 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_59_2146) with
| (lbs, e2) -> begin
(

let _59_2149 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_2149) with
| (env0, topt) -> begin
(

let _59_2152 = (build_let_rec_env true env0 lbs)
in (match (_59_2152) with
| (lbs, rec_env) -> begin
(

let _59_2155 = (check_let_recs rec_env lbs)
in (match (_59_2155) with
| (lbs, g_lbs) -> begin
(

let g_lbs = (let _155_781 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g_lbs)
in (FStar_All.pipe_right _155_781 FStar_TypeChecker_Rel.resolve_implicits))
in (

let all_lb_names = (let _155_784 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _155_784 (fun _155_783 -> Some (_155_783))))
in (

let lbs = if (not (env.FStar_TypeChecker_Env.generalize)) then begin
(FStar_All.pipe_right lbs (FStar_List.map (fun lb -> if (lb.FStar_Syntax_Syntax.lbunivs = []) then begin
lb
end else begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbeff lb.FStar_Syntax_Syntax.lbdef)
end)))
end else begin
(

let ecs = (let _155_788 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (let _155_787 = (FStar_Syntax_Syntax.mk_Total lb.FStar_Syntax_Syntax.lbtyp)
in ((lb.FStar_Syntax_Syntax.lbname), (lb.FStar_Syntax_Syntax.lbdef), (_155_787))))))
in (FStar_TypeChecker_Util.generalize env _155_788))
in (FStar_All.pipe_right ecs (FStar_List.map (fun _59_2166 -> (match (_59_2166) with
| (x, uvs, e, c) -> begin
(FStar_Syntax_Util.close_univs_and_mk_letbinding all_lb_names x uvs (FStar_Syntax_Util.comp_result c) (FStar_Syntax_Util.comp_effect_name c) e)
end)))))
end
in (

let cres = (let _155_790 = (FStar_Syntax_Syntax.mk_Total FStar_TypeChecker_Common.t_unit)
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_790))
in (

let _59_2169 = (FStar_ST.op_Colon_Equals e2.FStar_Syntax_Syntax.tk (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)))
in (

let _59_2173 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_59_2173) with
| (lbs, e2) -> begin
(let _155_792 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (FStar_TypeChecker_Common.t_unit.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (let _155_791 = (FStar_TypeChecker_Rel.discharge_guard env g_lbs)
in ((_155_792), (cres), (_155_791))))
end)))))))
end))
end))
end))
end))
end
| _59_2175 -> begin
(FStar_All.failwith "Impossible")
end)))
and check_inner_let_rec : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env top -> (

let env = (instantiate_both env)
in (match (top.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_let ((true, lbs), e2) -> begin
(

let _59_2187 = (FStar_Syntax_Subst.open_let_rec lbs e2)
in (match (_59_2187) with
| (lbs, e2) -> begin
(

let _59_2190 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_2190) with
| (env0, topt) -> begin
(

let _59_2193 = (build_let_rec_env false env0 lbs)
in (match (_59_2193) with
| (lbs, rec_env) -> begin
(

let _59_2196 = (check_let_recs rec_env lbs)
in (match (_59_2196) with
| (lbs, g_lbs) -> begin
(

let _59_2208 = (FStar_All.pipe_right lbs (FStar_Util.fold_map (fun env lb -> (

let x = (

let _59_2199 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _59_2199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_2199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lb.FStar_Syntax_Syntax.lbtyp})
in (

let lb = (

let _59_2202 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _59_2202.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _59_2202.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _59_2202.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _59_2202.FStar_Syntax_Syntax.lbdef})
in (

let env = (FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (lb.FStar_Syntax_Syntax.lbtyp)))
in ((env), (lb)))))) env))
in (match (_59_2208) with
| (env, lbs) -> begin
(

let bvs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (FStar_Util.left lb.FStar_Syntax_Syntax.lbname))))
in (

let _59_2214 = (tc_term env e2)
in (match (_59_2214) with
| (e2, cres, g2) -> begin
(

let guard = (FStar_TypeChecker_Rel.conj_guard g_lbs g2)
in (

let cres = (FStar_TypeChecker_Util.close_comp env bvs cres)
in (

let tres = (norm env cres.FStar_Syntax_Syntax.res_typ)
in (

let cres = (

let _59_2218 = cres
in {FStar_Syntax_Syntax.eff_name = _59_2218.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _59_2218.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_2218.FStar_Syntax_Syntax.comp})
in (

let _59_2223 = (FStar_Syntax_Subst.close_let_rec lbs e2)
in (match (_59_2223) with
| (lbs, e2) -> begin
(

let e = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (e2)))) (Some (tres.FStar_Syntax_Syntax.n)) top.FStar_Syntax_Syntax.pos)
in (match (topt) with
| Some (_59_2226) -> begin
((e), (cres), (guard))
end
| None -> begin
(

let tres = (check_no_escape None env bvs tres)
in (

let cres = (

let _59_2230 = cres
in {FStar_Syntax_Syntax.eff_name = _59_2230.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = tres; FStar_Syntax_Syntax.cflags = _59_2230.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = _59_2230.FStar_Syntax_Syntax.comp})
in ((e), (cres), (guard))))
end))
end))))))
end)))
end))
end))
end))
end))
end))
end
| _59_2234 -> begin
(FStar_All.failwith "Impossible")
end)))
and build_let_rec_env : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.env_t) = (fun top_level env lbs -> (

let env0 = env
in (

let termination_check_enabled = (fun t -> (

let _59_2244 = (FStar_Syntax_Util.arrow_formals_comp t)
in (match (_59_2244) with
| (_59_2242, c) -> begin
(

let quals = (FStar_TypeChecker_Env.lookup_effect_quals env (FStar_Syntax_Util.comp_effect_name c))
in (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.TotalEffect)))
end)))
in (

let _59_2274 = (FStar_List.fold_left (fun _59_2248 lb -> (match (_59_2248) with
| (lbs, env) -> begin
(

let _59_2253 = (FStar_TypeChecker_Util.extract_let_rec_annotation env lb)
in (match (_59_2253) with
| (univ_vars, t, check_t) -> begin
(

let env = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in (

let e = (FStar_Syntax_Util.unascribe lb.FStar_Syntax_Syntax.lbdef)
in (

let t = if (not (check_t)) then begin
t
end else begin
if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
t
end else begin
(

let _59_2262 = (let _155_806 = (let _155_805 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_left Prims.fst _155_805))
in (tc_check_tot_or_gtot_term (

let _59_2256 = env0
in {FStar_TypeChecker_Env.solver = _59_2256.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2256.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2256.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2256.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2256.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2256.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2256.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2256.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2256.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2256.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2256.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2256.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2256.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2256.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = true; FStar_TypeChecker_Env.use_eq = _59_2256.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2256.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2256.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2256.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2256.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2256.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2256.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2256.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2256.FStar_TypeChecker_Env.qname_and_index}) t _155_806))
in (match (_59_2262) with
| (t, _59_2260, g) -> begin
(

let _59_2263 = (FStar_TypeChecker_Rel.force_trivial_guard env0 g)
in (norm env0 t))
end))
end
end
in (

let env = if ((termination_check_enabled t) && (FStar_TypeChecker_Env.should_verify env)) then begin
(

let _59_2266 = env
in {FStar_TypeChecker_Env.solver = _59_2266.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2266.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2266.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2266.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2266.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2266.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2266.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2266.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2266.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2266.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2266.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2266.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = (((lb.FStar_Syntax_Syntax.lbname), (t)))::env.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _59_2266.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _59_2266.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2266.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2266.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2266.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2266.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2266.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2266.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2266.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2266.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2266.FStar_TypeChecker_Env.qname_and_index})
end else begin
(FStar_TypeChecker_Env.push_let_binding env lb.FStar_Syntax_Syntax.lbname (([]), (t)))
end
in (

let lb = (

let _59_2269 = lb
in {FStar_Syntax_Syntax.lbname = _59_2269.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = univ_vars; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _59_2269.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = e})
in (((lb)::lbs), (env)))))))
end))
end)) (([]), (env)) lbs)
in (match (_59_2274) with
| (lbs, env) -> begin
(((FStar_List.rev lbs)), (env))
end)))))
and check_let_recs : FStar_TypeChecker_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env lbs -> (

let _59_2287 = (let _155_811 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _59_2281 = (let _155_810 = (FStar_TypeChecker_Env.set_expected_typ env lb.FStar_Syntax_Syntax.lbtyp)
in (tc_tot_or_gtot_term _155_810 lb.FStar_Syntax_Syntax.lbdef))
in (match (_59_2281) with
| (e, c, g) -> begin
(

let _59_2282 = if (not ((FStar_Syntax_Util.is_total_lcomp c))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Expected let rec to be a Tot term; got effect GTot"), (e.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let lb = (FStar_Syntax_Util.mk_letbinding lb.FStar_Syntax_Syntax.lbname lb.FStar_Syntax_Syntax.lbunivs lb.FStar_Syntax_Syntax.lbtyp FStar_Syntax_Const.effect_Tot_lid e)
in ((lb), (g))))
end)))))
in (FStar_All.pipe_right _155_811 FStar_List.unzip))
in (match (_59_2287) with
| (lbs, gs) -> begin
(

let g_lbs = (FStar_List.fold_right FStar_TypeChecker_Rel.conj_guard gs FStar_TypeChecker_Rel.trivial_guard)
in ((lbs), (g_lbs)))
end)))
and check_let_bound_def : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t * Prims.bool) = (fun top_level env lb -> (

let _59_2295 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_2295) with
| (env1, _59_2294) -> begin
(

let e1 = lb.FStar_Syntax_Syntax.lbdef
in (

let _59_2301 = (check_lbtyp top_level env lb)
in (match (_59_2301) with
| (topt, wf_annot, univ_vars, env1) -> begin
(

let _59_2302 = if ((not (top_level)) && (univ_vars <> [])) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Inner let-bound definitions cannot be universe polymorphic"), (e1.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let _59_2309 = (tc_maybe_toplevel_term (

let _59_2304 = env1
in {FStar_TypeChecker_Env.solver = _59_2304.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2304.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2304.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2304.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2304.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2304.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2304.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2304.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2304.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2304.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2304.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2304.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2304.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = top_level; FStar_TypeChecker_Env.check_uvars = _59_2304.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2304.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2304.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2304.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2304.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2304.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2304.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2304.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2304.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2304.FStar_TypeChecker_Env.qname_and_index}) e1)
in (match (_59_2309) with
| (e1, c1, g1) -> begin
(

let _59_2313 = (let _155_818 = (FStar_TypeChecker_Env.set_range env1 e1.FStar_Syntax_Syntax.pos)
in (FStar_TypeChecker_Util.strengthen_precondition (Some ((fun _59_2310 -> (match (()) with
| () -> begin
FStar_TypeChecker_Errors.ill_kinded_type
end)))) _155_818 e1 c1 wf_annot))
in (match (_59_2313) with
| (c1, guard_f) -> begin
(

let g1 = (FStar_TypeChecker_Rel.conj_guard g1 guard_f)
in (

let _59_2315 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_821 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (let _155_820 = (FStar_Syntax_Print.term_to_string c1.FStar_Syntax_Syntax.res_typ)
in (let _155_819 = (FStar_TypeChecker_Rel.guard_to_string env g1)
in (FStar_Util.print3 "checked top-level def %s, result type is %s, guard is %s\n" _155_821 _155_820 _155_819))))
end else begin
()
end
in (let _155_822 = (FStar_Option.isSome topt)
in ((e1), (univ_vars), (c1), (g1), (_155_822)))))
end))
end)))
end)))
end)))
and check_lbtyp : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.letbinding  ->  (FStar_Syntax_Syntax.typ Prims.option * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.univ_names * FStar_TypeChecker_Env.env) = (fun top_level env lb -> (

let t = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let _59_2322 = if (lb.FStar_Syntax_Syntax.lbunivs <> []) then begin
(FStar_All.failwith "Impossible: non-empty universe variables but the type is unknown")
end else begin
()
end
in ((None), (FStar_TypeChecker_Rel.trivial_guard), ([]), (env)))
end
| _59_2325 -> begin
(

let _59_2328 = (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs t)
in (match (_59_2328) with
| (univ_vars, t) -> begin
(

let env1 = (FStar_TypeChecker_Env.push_univ_vars env univ_vars)
in if (top_level && (not (env.FStar_TypeChecker_Env.generalize))) then begin
(let _155_826 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (FStar_TypeChecker_Rel.trivial_guard), (univ_vars), (_155_826)))
end else begin
(

let _59_2333 = (FStar_Syntax_Util.type_u ())
in (match (_59_2333) with
| (k, _59_2332) -> begin
(

let _59_2338 = (tc_check_tot_or_gtot_term env1 t k)
in (match (_59_2338) with
| (t, _59_2336, g) -> begin
(

let _59_2339 = if (FStar_TypeChecker_Env.debug env FStar_Options.Medium) then begin
(let _155_829 = (let _155_827 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in (FStar_Range.string_of_range _155_827))
in (let _155_828 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "(%s) Checked type annotation %s\n" _155_829 _155_828)))
end else begin
()
end
in (

let t = (norm env1 t)
in (let _155_830 = (FStar_TypeChecker_Env.set_expected_typ env1 t)
in ((Some (t)), (g), (univ_vars), (_155_830)))))
end))
end))
end)
end))
end)))
and tc_binder : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe) = (fun env _59_2345 -> (match (_59_2345) with
| (x, imp) -> begin
(

let _59_2348 = (FStar_Syntax_Util.type_u ())
in (match (_59_2348) with
| (tu, u) -> begin
(

let _59_2349 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_835 = (FStar_Syntax_Print.bv_to_string x)
in (let _155_834 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _155_833 = (FStar_Syntax_Print.term_to_string tu)
in (FStar_Util.print3 "Checking binders %s:%s at type %s\n" _155_835 _155_834 _155_833))))
end else begin
()
end
in (

let _59_2355 = (tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort tu)
in (match (_59_2355) with
| (t, _59_2353, g) -> begin
(

let x = (((

let _59_2356 = x
in {FStar_Syntax_Syntax.ppname = _59_2356.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_2356.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp))
in (

let _59_2359 = if (FStar_TypeChecker_Env.debug env FStar_Options.High) then begin
(let _155_837 = (FStar_Syntax_Print.bv_to_string (Prims.fst x))
in (let _155_836 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Pushing binder %s at type %s\n" _155_837 _155_836)))
end else begin
()
end
in (let _155_838 = (push_binding env x)
in ((x), (_155_838), (g), (u)))))
end)))
end))
end))
and tc_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env * FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universes) = (fun env bs -> (

let rec aux = (fun env bs -> (match (bs) with
| [] -> begin
(([]), (env), (FStar_TypeChecker_Rel.trivial_guard), ([]))
end
| (b)::bs -> begin
(

let _59_2374 = (tc_binder env b)
in (match (_59_2374) with
| (b, env', g, u) -> begin
(

let _59_2379 = (aux env' bs)
in (match (_59_2379) with
| (bs, env', g', us) -> begin
(let _155_846 = (let _155_845 = (FStar_TypeChecker_Rel.close_guard ((b)::[]) g')
in (FStar_TypeChecker_Rel.conj_guard g _155_845))
in (((b)::bs), (env'), (_155_846), ((u)::us)))
end))
end))
end))
in (aux env bs)))
and tc_pats : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.args Prims.list  ->  (FStar_Syntax_Syntax.args Prims.list * FStar_TypeChecker_Env.guard_t) = (fun env pats -> (

let tc_args = (fun env args -> (FStar_List.fold_right (fun _59_2387 _59_2390 -> (match (((_59_2387), (_59_2390))) with
| ((t, imp), (args, g)) -> begin
(

let _59_2395 = (tc_term env t)
in (match (_59_2395) with
| (t, _59_2393, g') -> begin
(let _155_855 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((((t), (imp)))::args), (_155_855)))
end))
end)) args (([]), (FStar_TypeChecker_Rel.trivial_guard))))
in (FStar_List.fold_right (fun p _59_2399 -> (match (_59_2399) with
| (pats, g) -> begin
(

let _59_2402 = (tc_args env p)
in (match (_59_2402) with
| (args, g') -> begin
(let _155_858 = (FStar_TypeChecker_Rel.conj_guard g g')
in (((args)::pats), (_155_858)))
end))
end)) pats (([]), (FStar_TypeChecker_Rel.trivial_guard)))))
and tc_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _59_2408 = (tc_maybe_toplevel_term env e)
in (match (_59_2408) with
| (e, c, g) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp c) then begin
((e), (c), (g))
end else begin
(

let g = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (

let c = (c.FStar_Syntax_Syntax.comp ())
in (

let c = (norm_c env c)
in (

let _59_2414 = if (FStar_TypeChecker_Util.is_pure_effect env (FStar_Syntax_Util.comp_effect_name c)) then begin
(let _155_861 = (FStar_Syntax_Syntax.mk_Total (FStar_Syntax_Util.comp_result c))
in ((_155_861), (false)))
end else begin
(let _155_862 = (FStar_Syntax_Syntax.mk_GTotal (FStar_Syntax_Util.comp_result c))
in ((_155_862), (true)))
end
in (match (_59_2414) with
| (target_comp, allow_ghost) -> begin
(match ((FStar_TypeChecker_Rel.sub_comp env c target_comp)) with
| Some (g') -> begin
(let _155_863 = (FStar_TypeChecker_Rel.conj_guard g g')
in ((e), ((FStar_Syntax_Util.lcomp_of_comp target_comp)), (_155_863)))
end
| _59_2418 -> begin
if allow_ghost then begin
(let _155_866 = (let _155_865 = (let _155_864 = (FStar_TypeChecker_Errors.expected_ghost_expression e c)
in ((_155_864), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_155_865))
in (Prims.raise _155_866))
end else begin
(let _155_869 = (let _155_868 = (let _155_867 = (FStar_TypeChecker_Errors.expected_pure_expression e c)
in ((_155_867), (e.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_155_868))
in (Prims.raise _155_869))
end
end)
end)))))
end
end)))
and tc_check_tot_or_gtot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * FStar_TypeChecker_Env.guard_t) = (fun env e t -> (

let env = (FStar_TypeChecker_Env.set_expected_typ env t)
in (tc_tot_or_gtot_term env e)))
and tc_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp) = (fun env t -> (

let _59_2428 = (tc_tot_or_gtot_term env t)
in (match (_59_2428) with
| (t, c, g) -> begin
(

let _59_2429 = (FStar_TypeChecker_Rel.force_trivial_guard env g)
in ((t), (c)))
end)))


let type_of_tot_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_TypeChecker_Env.guard_t) = (fun env e -> (

let _59_2433 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_879 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "Checking term %s\n" _155_879))
end else begin
()
end
in (

let env = (

let _59_2435 = env
in {FStar_TypeChecker_Env.solver = _59_2435.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2435.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2435.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2435.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2435.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2435.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2435.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2435.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2435.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2435.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2435.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2435.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2435.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_2435.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2435.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2435.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2435.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _59_2435.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _59_2435.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2435.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2435.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _59_2435.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _59_2435.FStar_TypeChecker_Env.qname_and_index})
in (

let _59_2451 = try
(match (()) with
| () -> begin
(tc_tot_or_gtot_term env e)
end)
with
| FStar_Syntax_Syntax.Error (msg, _59_2443) -> begin
(let _155_884 = (let _155_883 = (let _155_882 = (FStar_TypeChecker_Env.get_range env)
in (((Prims.strcat "Implicit argument: " msg)), (_155_882)))
in FStar_Syntax_Syntax.Error (_155_883))
in (Prims.raise _155_884))
end
in (match (_59_2451) with
| (t, c, g) -> begin
if (FStar_Syntax_Util.is_total_lcomp c) then begin
((t), (c.FStar_Syntax_Syntax.res_typ), (g))
end else begin
(let _155_889 = (let _155_888 = (let _155_887 = (let _155_885 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Implicit argument: Expected a total term; got a ghost term: %s" _155_885))
in (let _155_886 = (FStar_TypeChecker_Env.get_range env)
in ((_155_887), (_155_886))))
in FStar_Syntax_Syntax.Error (_155_888))
in (Prims.raise _155_889))
end
end)))))


let universe_of : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun env e -> (

let _59_2454 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_894 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print1 "<start> universe_of %s\n" _155_894))
end else begin
()
end
in (

let _59_2459 = (FStar_TypeChecker_Env.clear_expected_typ env)
in (match (_59_2459) with
| (env, _59_2458) -> begin
(

let env = (

let _59_2460 = env
in {FStar_TypeChecker_Env.solver = _59_2460.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _59_2460.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _59_2460.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _59_2460.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _59_2460.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _59_2460.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _59_2460.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _59_2460.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _59_2460.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _59_2460.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _59_2460.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _59_2460.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _59_2460.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = false; FStar_TypeChecker_Env.check_uvars = _59_2460.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _59_2460.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _59_2460.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _59_2460.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _59_2460.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _59_2460.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _59_2460.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _59_2460.FStar_TypeChecker_Env.qname_and_index})
in (

let fail = (fun e t -> (let _155_904 = (let _155_903 = (let _155_902 = (let _155_900 = (FStar_Syntax_Print.term_to_string e)
in (let _155_899 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "Expected a term of type \'Type\'; got %s : %s" _155_900 _155_899)))
in (let _155_901 = (FStar_TypeChecker_Env.get_range env)
in ((_155_902), (_155_901))))
in FStar_Syntax_Syntax.Error (_155_903))
in (Prims.raise _155_904)))
in (

let ok = (fun u -> (

let _59_2468 = if (FStar_TypeChecker_Env.debug env FStar_Options.Extreme) then begin
(let _155_909 = (FStar_Syntax_Print.tag_of_term e)
in (let _155_908 = (FStar_Syntax_Print.term_to_string e)
in (let _155_907 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.print3 "<end> universe_of (%s) %s is %s\n" _155_909 _155_908 _155_907))))
end else begin
()
end
in u))
in (

let universe_of_type = (fun e t -> (match ((let _155_914 = (FStar_Syntax_Util.unrefine t)
in _155_914.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(ok u)
end
| _59_2476 -> begin
(fail e t)
end))
in (

let _59_2479 = (FStar_Syntax_Util.head_and_args e)
in (match (_59_2479) with
| (head, args) -> begin
(match ((let _155_915 = (FStar_Syntax_Subst.compress head)
in _155_915.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_59_2481, t) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (match ((let _155_916 = (FStar_Syntax_Subst.compress t)
in _155_916.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (_59_2487, t) -> begin
(universe_of_type e (FStar_Syntax_Util.comp_result t))
end
| _59_2492 -> begin
(universe_of_type e t)
end))
end
| _59_2494 -> begin
(

let t = (match ((FStar_ST.read e.FStar_Syntax_Syntax.tk)) with
| (None) | (Some (FStar_Syntax_Syntax.Tm_unknown)) -> begin
(

let e = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.NoDeltaSteps)::[]) env e)
in (

let _59_2510 = (tc_term env e)
in (match (_59_2510) with
| (_59_2500, {FStar_Syntax_Syntax.eff_name = _59_2507; FStar_Syntax_Syntax.res_typ = t; FStar_Syntax_Syntax.cflags = _59_2504; FStar_Syntax_Syntax.comp = _59_2502}, g) -> begin
(

let _59_2511 = (let _155_918 = (FStar_TypeChecker_Rel.solve_deferred_constraints env g)
in (FStar_All.pipe_right _155_918 Prims.ignore))
in t)
end)))
end
| Some (t) -> begin
(FStar_Syntax_Syntax.mk t None e.FStar_Syntax_Syntax.pos)
end)
in (let _155_919 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env t)
in (FStar_All.pipe_left (universe_of_type e) _155_919)))
end)
end))))))
end))))




