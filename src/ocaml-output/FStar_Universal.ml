
open Prims

let module_or_interface_name : FStar_Syntax_Syntax.modul  ->  (Prims.bool * FStar_Ident.lident) = (fun m -> ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name)))


let parse : FStar_Parser_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env pre_fn fn -> (

let ast = (FStar_Parser_Driver.parse_file fn)
in (

let ast = (match (pre_fn) with
| None -> begin
ast
end
| Some (pre_fn) -> begin
(

let pre_ast = (FStar_Parser_Driver.parse_file pre_fn)
in (match (((pre_ast), (ast))) with
| ((FStar_Parser_AST.Interface (lid1, decls1, _94_13))::[], (FStar_Parser_AST.Module (lid2, decls2))::[]) when (FStar_Ident.lid_equals lid1 lid2) -> begin
(let _190_11 = (let _190_10 = (let _190_9 = (FStar_Parser_Interleave.interleave decls1 decls2)
in ((lid1), (_190_9)))
in FStar_Parser_AST.Module (_190_10))
in (_190_11)::[])
end
| _94_24 -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("mismatch between pre-module and module\n")))
end))
end)
in (FStar_Parser_ToSyntax.desugar_file env ast))))


let tc_prims : Prims.unit  ->  ((FStar_Syntax_Syntax.modul * Prims.int) * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _94_26 -> (match (()) with
| () -> begin
(

let solver = if (FStar_Options.lax ()) then begin
FStar_SMTEncoding_Solver.dummy
end else begin
FStar_SMTEncoding_Solver.solver
end
in (

let env = (FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.type_of_tot_term FStar_TypeChecker_TcTerm.universe_of solver FStar_Syntax_Const.prims_lid)
in (

let _94_29 = (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.init env)
in (

let prims_filename = (FStar_Options.prims ())
in (

let _94_34 = (let _190_14 = (FStar_Parser_Env.empty_env ())
in (parse _190_14 None prims_filename))
in (match (_94_34) with
| (dsenv, prims_mod) -> begin
(

let _94_40 = (FStar_Util.record_time (fun _94_35 -> (match (()) with
| () -> begin
(let _190_16 = (FStar_List.hd prims_mod)
in (FStar_TypeChecker_Tc.check_module env _190_16))
end)))
in (match (_94_40) with
| ((prims_mod, env), elapsed_time) -> begin
((((prims_mod), (elapsed_time))), (dsenv), (env))
end))
end))))))
end))


let tc_one_fragment : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  FStar_Parser_ParseIt.input_frag  ->  (FStar_Syntax_Syntax.modul Prims.option * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) Prims.option = (fun curmod dsenv env frag -> try
(match (()) with
| () -> begin
(match ((FStar_Parser_Driver.parse_fragment frag)) with
| FStar_Parser_Driver.Empty -> begin
Some (((curmod), (dsenv), (env)))
end
| FStar_Parser_Driver.Modul (ast_modul) -> begin
(

let _94_66 = (FStar_Parser_ToSyntax.desugar_partial_modul curmod dsenv ast_modul)
in (match (_94_66) with
| (dsenv, modul) -> begin
(

let env = (match (curmod) with
| None -> begin
env
end
| Some (_94_69) -> begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Interactive mode only supports a single module at the top-level")))
end)
in (

let _94_76 = (FStar_TypeChecker_Tc.tc_partial_modul env modul)
in (match (_94_76) with
| (modul, _94_74, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end)))
end))
end
| FStar_Parser_Driver.Decls (ast_decls) -> begin
(

let _94_81 = (FStar_Parser_ToSyntax.desugar_decls dsenv ast_decls)
in (match (_94_81) with
| (dsenv, decls) -> begin
(match (curmod) with
| None -> begin
(

let _94_83 = (FStar_Util.print_error "fragment without an enclosing module")
in (FStar_All.exit (Prims.parse_int "1")))
end
| Some (modul) -> begin
(

let _94_91 = (FStar_TypeChecker_Tc.tc_more_partial_modul env modul decls)
in (match (_94_91) with
| (modul, _94_89, env) -> begin
Some (((Some (modul)), (dsenv), (env)))
end))
end)
end))
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _94_52 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _94_56 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (FStar_Range.dummyRange)))::[]))
in None)
end
| e when (not ((FStar_Options.trace_error ()))) -> begin
(Prims.raise e)
end)


let pop_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  Prims.unit = (fun _94_94 msg -> (match (_94_94) with
| (dsenv, env) -> begin
(

let _94_96 = (let _190_31 = (FStar_Parser_Env.pop dsenv)
in (FStar_All.pipe_right _190_31 Prims.ignore))
in (

let _94_98 = (let _190_32 = (FStar_TypeChecker_Env.pop env msg)
in (FStar_All.pipe_right _190_32 Prims.ignore))
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())))
end))


let push_context : (FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string  ->  (FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun _94_102 msg -> (match (_94_102) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.push dsenv)
in (

let env = (FStar_TypeChecker_Env.push env msg)
in ((dsenv), (env))))
end))


let interactive_tc : ((FStar_Parser_Env.env * FStar_TypeChecker_Env.env), FStar_Syntax_Syntax.modul Prims.option) FStar_Interactive.interactive_tc = (

let pop = (fun _94_109 msg -> (match (_94_109) with
| (dsenv, env) -> begin
(

let _94_111 = (pop_context ((dsenv), (env)) msg)
in (FStar_Options.pop ()))
end))
in (

let push = (fun _94_116 msg -> (match (_94_116) with
| (dsenv, env) -> begin
(

let res = (push_context ((dsenv), (env)) msg)
in (

let _94_119 = (FStar_Options.push ())
in res))
end))
in (

let mark = (fun _94_124 -> (match (_94_124) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.mark dsenv)
in (

let env = (FStar_TypeChecker_Env.mark env)
in (

let _94_127 = (FStar_Options.push ())
in ((dsenv), (env)))))
end))
in (

let reset_mark = (fun _94_132 -> (match (_94_132) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.reset_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.reset_mark env)
in (

let _94_135 = (FStar_Options.pop ())
in ((dsenv), (env)))))
end))
in (

let commit_mark = (fun _94_140 -> (match (_94_140) with
| (dsenv, env) -> begin
(

let dsenv = (FStar_Parser_Env.commit_mark dsenv)
in (

let env = (FStar_TypeChecker_Env.commit_mark env)
in ((dsenv), (env))))
end))
in (

let check_frag = (fun _94_146 curmod text -> (match (_94_146) with
| (dsenv, env) -> begin
try
(match (()) with
| () -> begin
(match ((tc_one_fragment curmod dsenv env text)) with
| Some (m, dsenv, env) -> begin
(let _190_59 = (let _190_58 = (FStar_TypeChecker_Errors.get_err_count ())
in ((m), (((dsenv), (env))), (_190_58)))
in Some (_190_59))
end
| _94_170 -> begin
None
end)
end)
with
| FStar_Syntax_Syntax.Error (msg, r) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _94_156 = (FStar_TypeChecker_Errors.add_errors env ((((msg), (r)))::[]))
in None)
end
| FStar_Syntax_Syntax.Err (msg) when (not ((FStar_Options.trace_error ()))) -> begin
(

let _94_160 = (let _190_63 = (let _190_62 = (let _190_61 = (FStar_TypeChecker_Env.get_range env)
in ((msg), (_190_61)))
in (_190_62)::[])
in (FStar_TypeChecker_Errors.add_errors env _190_63))
in None)
end
end))
in (

let report_fail = (fun _94_172 -> (match (()) with
| () -> begin
(

let _94_173 = (let _190_66 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _190_66 Prims.ignore))
in (FStar_ST.op_Colon_Equals FStar_TypeChecker_Errors.num_errs (Prims.parse_int "0")))
end))
in {FStar_Interactive.pop = pop; FStar_Interactive.push = push; FStar_Interactive.mark = mark; FStar_Interactive.reset_mark = reset_mark; FStar_Interactive.commit_mark = commit_mark; FStar_Interactive.check_frag = check_frag; FStar_Interactive.report_fail = report_fail})))))))


let tc_one_file : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.option  ->  Prims.string  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env pre_fn fn -> (

let _94_181 = (parse dsenv pre_fn fn)
in (match (_94_181) with
| (dsenv, fmods) -> begin
(

let check_mods = (fun _94_183 -> (match (()) with
| () -> begin
(

let _94_196 = (FStar_All.pipe_right fmods (FStar_List.fold_left (fun _94_186 m -> (match (_94_186) with
| (env, all_mods) -> begin
(

let _94_193 = (FStar_Util.record_time (fun _94_188 -> (match (()) with
| () -> begin
(FStar_TypeChecker_Tc.check_module env m)
end)))
in (match (_94_193) with
| ((m, env), elapsed_ms) -> begin
((env), ((((m), (elapsed_ms)))::all_mods))
end))
end)) ((env), ([]))))
in (match (_94_196) with
| (env, all_mods) -> begin
(((FStar_List.rev all_mods)), (dsenv), (env))
end))
end))
in (match (fmods) with
| (m)::[] when ((FStar_Options.should_verify m.FStar_Syntax_Syntax.name.FStar_Ident.str) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) -> begin
(FStar_SMTEncoding_Solver.with_hints_db fn check_mods)
end
| _94_200 -> begin
(check_mods ())
end))
end)))


let needs_interleaving : Prims.string  ->  Prims.string  ->  Prims.bool = (fun intf impl -> (

let m1 = (FStar_Parser_Dep.lowercase_module_name intf)
in (

let m2 = (FStar_Parser_Dep.lowercase_module_name impl)
in (((m1 = m2) && ((FStar_Util.get_file_extension intf) = "fsti")) && ((FStar_Util.get_file_extension impl) = "fst")))))


let rec tc_fold_interleave : ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env)  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun acc remaining -> (

let move = (fun intf impl remaining -> (

let _94_211 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let _94_216 = acc
in (match (_94_216) with
| (all_mods, dsenv, env) -> begin
(

let _94_241 = (match (intf) with
| None -> begin
(tc_one_file dsenv env None impl)
end
| Some (_94_219) when ((FStar_Options.codegen ()) <> None) -> begin
(

let _94_221 = if (not ((FStar_Options.lax ()))) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")))
end else begin
()
end
in (tc_one_file dsenv env intf impl))
end
| Some (iname) -> begin
(

let _94_225 = if (FStar_Options.debug_any ()) then begin
(FStar_Util.print1 "Interleaving iface+module: %s\n" iname)
end else begin
()
end
in (

let caption = (Prims.strcat "interface: " iname)
in (

let _94_230 = (push_context ((dsenv), (env)) caption)
in (match (_94_230) with
| (dsenv', env') -> begin
(

let _94_235 = (tc_one_file dsenv' env' intf impl)
in (match (_94_235) with
| (_94_232, dsenv', env') -> begin
(

let _94_236 = (pop_context ((dsenv'), (env')) caption)
in (tc_one_file dsenv env None iname))
end))
end))))
end)
in (match (_94_241) with
| (ms, dsenv, env) -> begin
(

let acc = (((FStar_List.append all_mods ms)), (dsenv), (env))
in (tc_fold_interleave acc remaining))
end))
end))))
in (match (remaining) with
| (intf)::(impl)::remaining when (needs_interleaving intf impl) -> begin
(move (Some (intf)) impl remaining)
end
| (intf_or_impl)::remaining -> begin
(move None intf_or_impl remaining)
end
| [] -> begin
acc
end)))


let batch_mode_tc_no_prims : FStar_Parser_Env.env  ->  FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun dsenv env filenames -> (

let _94_258 = (tc_fold_interleave (([]), (dsenv), (env)) filenames)
in (match (_94_258) with
| (all_mods, dsenv, env) -> begin
(

let _94_259 = if ((FStar_Options.interactive ()) && ((FStar_TypeChecker_Errors.get_err_count ()) = (Prims.parse_int "0"))) then begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.refresh ())
end else begin
(env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.finish ())
end
in ((all_mods), (dsenv), (env)))
end)))


let batch_mode_tc : FStar_Parser_Dep.verify_mode  ->  Prims.string Prims.list  ->  ((FStar_Syntax_Syntax.modul * Prims.int) Prims.list * FStar_Parser_Env.env * FStar_TypeChecker_Env.env) = (fun verify_mode filenames -> (

let _94_266 = (tc_prims ())
in (match (_94_266) with
| (prims_mod, dsenv, env) -> begin
(

let filenames = (FStar_Dependences.find_deps_if_needed verify_mode filenames)
in (

let _94_272 = if ((not ((FStar_Options.explicit_deps ()))) && (FStar_Options.debug_any ())) then begin
(

let _94_268 = (FStar_Util.print_endline "Auto-deps kicked in; here\'s some info.")
in (

let _94_270 = (FStar_Util.print1 "Here\'s the list of filenames we will process: %s\n" (FStar_String.concat " " filenames))
in (let _190_105 = (let _190_104 = (FStar_Options.verify_module ())
in (FStar_String.concat " " _190_104))
in (FStar_Util.print1 "Here\'s the list of modules we will verify: %s\n" _190_105))))
end else begin
()
end
in (

let _94_277 = (batch_mode_tc_no_prims dsenv env filenames)
in (match (_94_277) with
| (all_mods, dsenv, env) -> begin
(((prims_mod)::all_mods), (dsenv), (env))
end))))
end)))




