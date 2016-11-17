
open Prims

type z3_err =
(FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun _90_1 -> (match (_90_1) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, _90_9) -> begin
FStar_Util.Inr (r)
end))


type hint_stat =
{hint : FStar_Util.hint Prims.option; replay_result : z3_replay_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


let is_Mkhint_stat : hint_stat  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkhint_stat"))))


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db = (fun src_filename force_record -> (

let _90_20 = (FStar_ST.op_Colon_Equals hint_stats [])
in (

let _90_22 = if (FStar_Options.record_hints ()) then begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ([])))
end else begin
()
end
in if (FStar_Options.use_hints ()) then begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (format_hints_file_name norm_src_filename)
in (match ((FStar_Util.read_hints val_filename)) with
| Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in (

let _90_29 = if (FStar_Options.hint_info ()) then begin
if (hints.FStar_Util.module_digest = expected_digest) then begin
(FStar_Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_filename)
end else begin
(FStar_Util.print1 "(%s) digest is invalid; using potentially stale hints\n" norm_src_filename)
end
end else begin
()
end
in (FStar_ST.op_Colon_Equals replaying_hints (Some (hints.FStar_Util.hints)))))
end
| None -> begin
if (FStar_Options.hint_info ()) then begin
(FStar_Util.print1 "(%s) Unable to read hints db.\n" norm_src_filename)
end else begin
()
end
end)))
end else begin
()
end)))


let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_filename -> (

let _90_36 = if (FStar_Options.record_hints ()) then begin
(

let hints = (let _186_21 = (FStar_ST.read recorded_hints)
in (FStar_Option.get _186_21))
in (

let hints_db = (let _186_22 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _186_22; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end else begin
()
end
in (

let _90_44 = if (FStar_Options.hint_info ()) then begin
(

let stats = (let _186_23 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _186_23 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _186_26 = (FStar_Range.string_of_range s.source_location)
in (let _186_25 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _186_26 _186_25)))
end
| FStar_Util.Inr (_error) -> begin
(let _186_28 = (FStar_Range.string_of_range s.source_location)
in (let _186_27 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _186_28 _186_27)))
end)))))
end else begin
()
end
in (

let _90_46 = (FStar_ST.op_Colon_Equals recorded_hints None)
in (

let _90_48 = (FStar_ST.op_Colon_Equals replaying_hints None)
in (FStar_ST.op_Colon_Equals hint_stats []))))))


let with_hints_db = (fun fname f -> (

let _90_52 = (initialize_hints_db fname false)
in (

let result = (f ())
in (

let _90_55 = (finalize_hints_db fname)
in result))))


let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint Prims.option = (fun qname qindex -> (match ((FStar_ST.read replaying_hints)) with
| Some (hints) -> begin
(FStar_Util.find_map hints (fun _90_2 -> (match (_90_2) with
| Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
Some (hint)
end
| _90_65 -> begin
None
end)))
end
| _90_67 -> begin
None
end))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (

let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let _90_72 = h
in {FStar_Util.hint_name = _90_72.FStar_Util.hint_name; FStar_Util.hint_index = _90_72.FStar_Util.hint_index; FStar_Util.fuel = _90_72.FStar_Util.fuel; FStar_Util.ifuel = _90_72.FStar_Util.ifuel; FStar_Util.unsat_core = _90_72.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (match ((FStar_ST.read recorded_hints)) with
| Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| _90_78 -> begin
()
end)))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (let _186_50 = (let _186_49 = (FStar_ST.read hint_stats)
in (s)::_186_49)
in (FStar_ST.op_Colon_Equals hint_stats _186_50))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix query suffix -> (

let _90_89 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let _90_98 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(FStar_All.failwith "No query name set!")
end
| Some (q, n) -> begin
(((FStar_Ident.text_of_lid q)), (n))
end)
in (match (_90_98) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _90_3 -> (match (_90_3) with
| ([], _90_105) -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_90_109) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some (((f), (errs)))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _90_118 -> (match (_90_118) with
| (n, i, timeout_ms) -> begin
(let _186_98 = (let _186_88 = (let _186_73 = (let _186_72 = (FStar_Util.string_of_int n)
in (let _186_71 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _186_72 _186_71)))
in FStar_SMTEncoding_Term.Caption (_186_73))
in (let _186_87 = (let _186_86 = (let _186_78 = (let _186_77 = (let _186_76 = (let _186_75 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (let _186_74 = (FStar_SMTEncoding_Term.n_fuel n)
in ((_186_75), (_186_74))))
in (FStar_SMTEncoding_Util.mkEq _186_76))
in ((_186_77), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_186_78))
in (let _186_85 = (let _186_84 = (let _186_83 = (let _186_82 = (let _186_81 = (let _186_80 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (let _186_79 = (FStar_SMTEncoding_Term.n_fuel i)
in ((_186_80), (_186_79))))
in (FStar_SMTEncoding_Util.mkEq _186_81))
in ((_186_82), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_186_83))
in (_186_84)::(p)::[])
in (_186_86)::_186_85))
in (_186_88)::_186_87))
in (let _186_97 = (let _186_96 = (let _186_95 = (let _186_91 = (let _186_90 = (let _186_89 = (FStar_Util.string_of_int timeout_ms)
in (("timeout"), (_186_89)))
in FStar_SMTEncoding_Term.SetOption (_186_90))
in (_186_91)::[])
in (let _186_94 = (let _186_93 = (let _186_92 = if (FStar_Options.record_hints ()) then begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end else begin
[]
end
in (FStar_List.append _186_92 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) _186_93))
in (FStar_List.append _186_95 _186_94)))
in (FStar_List.append label_assumptions _186_96))
in (FStar_List.append _186_98 _186_97)))
end))
in (

let check = (fun p -> (

let default_timeout = ((FStar_Options.z3_timeout ()) * (Prims.parse_int "1000"))
in (

let default_initial_config = (let _186_102 = (FStar_Options.initial_fuel ())
in (let _186_101 = (FStar_Options.initial_ifuel ())
in ((_186_102), (_186_101), (default_timeout))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let _90_132 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(

let _90_129 = if (FStar_Option.isSome hint.FStar_Util.unsat_core) then begin
((hint.FStar_Util.unsat_core), (default_timeout))
end else begin
((None), (((Prims.parse_int "60") * (Prims.parse_int "1000"))))
end
in (match (_90_129) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (_90_132) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (let _186_123 = (let _186_122 = if ((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core)) then begin
(default_initial_config)::[]
end else begin
[]
end
in (let _186_121 = (let _186_120 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _186_105 = (let _186_104 = (FStar_Options.initial_fuel ())
in (let _186_103 = (FStar_Options.max_ifuel ())
in ((_186_104), (_186_103), (default_timeout))))
in (_186_105)::[])
end else begin
[]
end
in (let _186_119 = (let _186_118 = if (((FStar_Options.max_fuel ()) / (Prims.parse_int "2")) > (FStar_Options.initial_fuel ())) then begin
(let _186_108 = (let _186_107 = ((FStar_Options.max_fuel ()) / (Prims.parse_int "2"))
in (let _186_106 = (FStar_Options.max_ifuel ())
in ((_186_107), (_186_106), (default_timeout))))
in (_186_108)::[])
end else begin
[]
end
in (let _186_117 = (let _186_116 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _186_111 = (let _186_110 = (FStar_Options.max_fuel ())
in (let _186_109 = (FStar_Options.max_ifuel ())
in ((_186_110), (_186_109), (default_timeout))))
in (_186_111)::[])
end else begin
[]
end
in (let _186_115 = (let _186_114 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _186_113 = (let _186_112 = (FStar_Options.min_fuel ())
in ((_186_112), ((Prims.parse_int "1")), (default_timeout)))
in (_186_113)::[])
end else begin
[]
end
in (_186_114)::[])
in (_186_116)::_186_115))
in (_186_118)::_186_117))
in (_186_120)::_186_119))
in (_186_122)::_186_121))
in (FStar_List.flatten _186_123))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = (Prims.parse_int "1"))) then begin
(

let _90_144 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
((f), (errs))
end
| None -> begin
(let _186_129 = (let _186_128 = (FStar_Options.min_fuel ())
in ((_186_128), ((Prims.parse_int "1")), (default_timeout)))
in ((_186_129), (errs)))
end)
in (match (_90_144) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _90_149 = (let _186_133 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask None all_labels _186_133 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _186_134 = (FStar_ST.read res)
in (FStar_Option.get _186_134)))))
in (let _186_135 = (FStar_SMTEncoding_ErrorReporting.detail_errors env all_labels ask_z3)
in ((_186_135), (FStar_SMTEncoding_Z3.Default))))
end))
end else begin
(match (errs) with
| ([], FStar_SMTEncoding_Z3.Timeout) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| ([], FStar_SMTEncoding_Z3.Default) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| (_90_158, FStar_SMTEncoding_Z3.Kill) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Killed: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| _90_162 -> begin
errs
end)
end
in (

let _90_164 = (record_hint None)
in (

let _90_166 = if (FStar_Options.print_fuels ()) then begin
(let _186_141 = (let _186_136 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _186_136))
in (let _186_140 = (let _186_137 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _186_137 FStar_Util.string_of_int))
in (let _186_139 = (let _186_138 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _186_138 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _186_141 _186_140 _186_139))))
end else begin
()
end
in (let _186_143 = (FStar_All.pipe_right (Prims.fst errs) (FStar_List.map (fun _90_172 -> (match (_90_172) with
| (_90_169, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Errors.add_errors env _186_143))))))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| ((([], _), _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (_90_190, FStar_Util.Inr (_90_192)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _90_201 = (set_minimum_workable_fuel prev_f errs)
in (match (((cfgs), ((Prims.snd errs)))) with
| (([], _)) | ((_, FStar_SMTEncoding_Z3.Kill)) -> begin
(report p errs)
end
| ((mi)::[], _90_214) -> begin
(match (errs) with
| ([], _90_218) -> begin
(let _186_161 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _186_161 (cb false mi p [])))
end
| _90_221 -> begin
(

let _90_222 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| ((mi)::tl, _90_228) -> begin
(let _186_163 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _186_163 (fun _90_232 -> (match (_90_232) with
| (result, elapsed_time) -> begin
(cb false mi p tl (((use_errors errs result)), (elapsed_time)))
end))))
end)))
and cb = (fun used_hint _90_237 p alt _90_242 -> (match (((_90_237), (_90_242))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
(

let _90_245 = if used_hint then begin
(

let _90_243 = (FStar_SMTEncoding_Z3.refresh ())
in (let _186_169 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _186_169)))
end else begin
()
end
in (

let at_log_file = (fun _90_248 -> (match (()) with
| () -> begin
if (FStar_Options.log_queries ()) then begin
(let _186_172 = (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.log_file_name ())
in (Prims.strcat "@" _186_172))
end else begin
""
end
end))
in (

let query_info = (fun tag -> (let _186_190 = (let _186_189 = (let _186_175 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _186_175))
in (let _186_188 = (let _186_187 = (at_log_file ())
in (let _186_186 = (let _186_185 = (let _186_184 = (FStar_Util.string_of_int query_index)
in (let _186_183 = (let _186_182 = (let _186_181 = (let _186_180 = (FStar_Util.string_of_int elapsed_time)
in (let _186_179 = (let _186_178 = (FStar_Util.string_of_int prev_fuel)
in (let _186_177 = (let _186_176 = (FStar_Util.string_of_int prev_ifuel)
in (_186_176)::[])
in (_186_178)::_186_177))
in (_186_180)::_186_179))
in (if used_hint then begin
" (with hint)"
end else begin
""
end)::_186_181)
in (tag)::_186_182)
in (_186_184)::_186_183))
in (query_name)::_186_185)
in (_186_187)::_186_186))
in (_186_189)::_186_188))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" _186_190)))
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
(

let _90_254 = if (not (used_hint)) then begin
(

let hint = {FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core; FStar_Util.query_elapsed_time = elapsed_time}
in (record_hint (Some (hint))))
end else begin
(record_hint hint_opt)
end
in if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(query_info "succeeded")
end else begin
()
end)
end
| FStar_Util.Inr (errs) -> begin
(

let _90_258 = if ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) then begin
(query_info "failed")
end else begin
()
end
in (try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p errs alt))
end))))
end))
in (

let _90_260 = if (FStar_Option.isSome unsat_core) then begin
(FStar_SMTEncoding_Z3.refresh ())
end else begin
()
end
in (let _186_193 = (with_fuel [] p initial_config)
in (let _186_192 = (let _186_191 = (FStar_Option.isSome unsat_core)
in (cb _186_191 initial_config p alt_configs))
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels _186_193 _186_192))))))))
end))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > (Prims.parse_int "0")) then begin
(

let _90_266 = (let _186_199 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _186_199 q))
in (match (_90_266) with
| (b, cb) -> begin
if b then begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in if (FStar_Options.admit_smt_queries ()) then begin
()
end else begin
(process_query query)
end)))))
end))))


let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (

let _90_270 = (let _186_218 = (let _186_217 = (let _186_216 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _186_216))
in (FStar_Util.format1 "Starting query at %s" _186_217))
in (FStar_SMTEncoding_Encode.push _186_218))
in (

let tcenv = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let _90_277 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (_90_277) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun _90_279 -> (match (()) with
| () -> begin
(let _186_223 = (let _186_222 = (let _186_221 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _186_221))
in (FStar_Util.format1 "Ending query at %s" _186_222))
in (FStar_SMTEncoding_Encode.pop _186_223))
end))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _90_286); FStar_SMTEncoding_Term.freevars = _90_283; FStar_SMTEncoding_Term.rng = _90_281}, _90_291, _90_293) -> begin
(

let _90_296 = (pop ())
in ())
end
| _90_299 when tcenv.FStar_TypeChecker_Env.admit -> begin
(

let _90_300 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _90_304, _90_306) -> begin
(

let _90_309 = (ask_and_report_errors tcenv labels prefix qry suffix)
in (pop ()))
end
| _90_312 -> begin
(FStar_All.failwith "Impossible")
end))
end)))))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _90_313 -> ()); FStar_TypeChecker_Env.push = (fun _90_315 -> ()); FStar_TypeChecker_Env.pop = (fun _90_317 -> ()); FStar_TypeChecker_Env.mark = (fun _90_319 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _90_321 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _90_323 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _90_325 _90_327 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _90_329 _90_331 -> ()); FStar_TypeChecker_Env.solve = (fun _90_333 _90_335 _90_337 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _90_339 _90_341 -> false); FStar_TypeChecker_Env.finish = (fun _90_343 -> ()); FStar_TypeChecker_Env.refresh = (fun _90_344 -> ())}




