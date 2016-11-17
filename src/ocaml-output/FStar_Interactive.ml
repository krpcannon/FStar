
open Prims

type ('env, 'modul) interactive_tc =
{pop : 'env  ->  Prims.string  ->  Prims.unit; push : 'env  ->  Prims.string  ->  'env; mark : 'env  ->  'env; reset_mark : 'env  ->  'env; commit_mark : 'env  ->  'env; check_frag : 'env  ->  'modul  ->  FStar_Parser_ParseIt.input_frag  ->  ('modul * 'env * Prims.int) Prims.option; report_fail : Prims.unit  ->  Prims.unit}


let is_Mkinteractive_tc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_tc"))))


type input_chunks =
| Push of (Prims.int * Prims.int)
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))


let is_Push = (fun _discr_ -> (match (_discr_) with
| Push (_) -> begin
true
end
| _ -> begin
false
end))


let is_Pop = (fun _discr_ -> (match (_discr_) with
| Pop (_) -> begin
true
end
| _ -> begin
false
end))


let is_Code = (fun _discr_ -> (match (_discr_) with
| Code (_) -> begin
true
end
| _ -> begin
false
end))


let ___Push____0 = (fun projectee -> (match (projectee) with
| Push (_92_13) -> begin
_92_13
end))


let ___Pop____0 = (fun projectee -> (match (projectee) with
| Pop (_92_16) -> begin
_92_16
end))


let ___Code____0 = (fun projectee -> (match (projectee) with
| Code (_92_19) -> begin
_92_19
end))


type ('env, 'modul) stack =
('env * 'modul) Prims.list


type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let is_Mkinteractive_state : interactive_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinteractive_state"))))


let the_interactive_state : interactive_state = (let _188_149 = (FStar_Util.new_string_builder ())
in (let _188_148 = (FStar_ST.alloc None)
in (let _188_147 = (FStar_ST.alloc [])
in (let _188_146 = (FStar_ST.alloc None)
in {chunk = _188_149; stdin = _188_148; buffer = _188_147; log = _188_146}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun _92_27 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (

let log = if (FStar_Options.debug_any ()) then begin
(

let transcript = (match ((FStar_ST.read s.log)) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in (

let _92_33 = (FStar_ST.op_Colon_Equals s.log (Some (transcript)))
in transcript))
end)
in (fun line -> (

let _92_37 = (FStar_Util.append_to_file transcript line)
in (FStar_Util.flush_file transcript))))
end else begin
(fun _92_39 -> ())
end
in (

let stdin = (match ((FStar_ST.read s.stdin)) with
| Some (i) -> begin
i
end
| None -> begin
(

let i = (FStar_Util.open_stdin ())
in (

let _92_46 = (FStar_ST.op_Colon_Equals s.stdin (Some (i)))
in i))
end)
in (

let line = (match ((FStar_Util.read_line stdin)) with
| None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| Some (l) -> begin
l
end)
in (

let _92_53 = (log line)
in (

let l = (FStar_Util.trim_string line)
in if (FStar_Util.starts_with l "#end") then begin
(

let responses = (match ((FStar_Util.split l " ")) with
| (_92_59)::(ok)::(fail)::[] -> begin
((ok), (fail))
end
| _92_62 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in (

let _92_65 = (FStar_Util.clear_string_builder s.chunk)
in Code (((str), (responses))))))
end else begin
if (FStar_Util.starts_with l "#pop") then begin
(

let _92_67 = (FStar_Util.clear_string_builder s.chunk)
in Pop (l))
end else begin
if (FStar_Util.starts_with l "#push") then begin
(

let _92_69 = (FStar_Util.clear_string_builder s.chunk)
in (

let lc = (FStar_Util.substring_from l (FStar_String.length "#push"))
in (

let lc = (FStar_Util.trim_string lc)
in (

let lcs = (FStar_Util.split lc " ")
in (

let lc = (match (lcs) with
| (l)::(c)::[] -> begin
(let _188_158 = (FStar_Util.int_of_string l)
in (let _188_157 = (FStar_Util.int_of_string c)
in ((_188_158), (_188_157))))
end
| _92_78 -> begin
(((Prims.parse_int "1")), ((Prims.parse_int "0")))
end)
in Push (lc))))))
end else begin
if (l = "#finish") then begin
(FStar_All.exit (Prims.parse_int "0"))
end else begin
(

let _92_80 = (FStar_Util.string_builder_append s.chunk line)
in (

let _92_82 = (FStar_Util.string_builder_append s.chunk "\n")
in (read_chunk ())))
end
end
end
end))))))
end))


let shift_chunk : Prims.unit  ->  input_chunks = (fun _92_84 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (match ((FStar_ST.read s.buffer)) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
(

let _92_90 = (FStar_ST.op_Colon_Equals s.buffer chunks)
in chunk)
end))
end))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun _92_92 -> (match (()) with
| () -> begin
(

let s = the_interactive_state
in (let _188_166 = (let _188_165 = (FStar_ST.read s.buffer)
in (let _188_164 = (let _188_163 = (read_chunk ())
in (_188_163)::[])
in (FStar_List.append _188_165 _188_164)))
in (FStar_ST.op_Colon_Equals s.buffer _188_166)))
end))


exception Found of (Prims.string)


let is_Found = (fun _discr_ -> (match (_discr_) with
| Found (_) -> begin
true
end
| _ -> begin
false
end))


let ___Found____0 = (fun projectee -> (match (projectee) with
| Found (_92_95) -> begin
_92_95
end))


let find_initial_module_name : Prims.unit  ->  Prims.string Prims.option = (fun _92_96 -> (match (()) with
| () -> begin
(

let _92_97 = (fill_buffer ())
in (

let _92_99 = (fill_buffer ())
in try
(match (()) with
| () -> begin
(

let _92_123 = (match ((FStar_ST.read the_interactive_state.buffer)) with
| (Push (_92_114))::(Code (code, _92_110))::[] -> begin
(

let lines = (FStar_Util.split code "\n")
in (FStar_List.iter (fun line -> (

let line = (FStar_Util.trim_string line)
in if (((FStar_String.length line) > (Prims.parse_int "7")) && ((FStar_Util.substring line (Prims.parse_int "0") (Prims.parse_int "6")) = "module")) then begin
(

let module_name = (FStar_Util.substring line (Prims.parse_int "7") ((FStar_String.length line) - (Prims.parse_int "7")))
in (Prims.raise (Found (module_name))))
end else begin
()
end)) lines))
end
| _92_122 -> begin
()
end)
in None)
end)
with
| Found (n) -> begin
Some (n)
end))
end))


let detect_dependencies_with_first_interactive_chunk : Prims.unit  ->  (Prims.string * Prims.string Prims.list) = (fun _92_125 -> (match (()) with
| () -> begin
(

let failr = (fun msg r -> (

let _92_129 = if (FStar_Options.universes ()) then begin
(FStar_TypeChecker_Errors.warn r msg)
end else begin
(FStar_Tc_Errors.warn r msg)
end
in (FStar_All.exit (Prims.parse_int "1"))))
in (

let fail = (fun msg -> (failr msg FStar_Range.dummyRange))
in (

let parse_msg = "Dependency analysis may not be correct because the file failed to parse: "
in try
(match (()) with
| () -> begin
(match ((find_initial_module_name ())) with
| None -> begin
(fail "No initial module directive found\n")
end
| Some (module_name) -> begin
(

let file_of_module_name = (FStar_Parser_Dep.build_map [])
in (

let filename = (FStar_Util.smap_try_find file_of_module_name (FStar_String.lowercase module_name))
in (match (filename) with
| None -> begin
(let _188_186 = (FStar_Util.format2 "I found a \"module %s\" directive, but there is no %s.fst\n" module_name module_name)
in (fail _188_186))
end
| (Some (None, Some (filename))) | (Some (Some (filename), None)) -> begin
(

let _92_163 = (FStar_Options.add_verify_module module_name)
in (

let _92_170 = (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyUserList ((filename)::[]))
in (match (_92_170) with
| (_92_166, all_filenames, _92_169) -> begin
(let _188_188 = (let _188_187 = (FStar_List.tl all_filenames)
in (FStar_List.rev _188_187))
in ((filename), (_188_188)))
end)))
end
| Some (Some (_92_172), Some (_92_175)) -> begin
(let _188_189 = (FStar_Util.format1 "The combination of split interfaces and interactive verification is not supported for: %s\n" module_name)
in (fail _188_189))
end
| Some (None, None) -> begin
(FStar_All.failwith "impossible")
end)))
end)
end)
with
| (FStar_Syntax_Syntax.Error (msg, r)) | (FStar_Absyn_Syntax.Error (msg, r)) -> begin
(failr (Prims.strcat parse_msg msg) r)
end
| (FStar_Syntax_Syntax.Err (msg)) | (FStar_Absyn_Syntax.Err (msg)) -> begin
(fail (Prims.strcat parse_msg msg))
end)))
end))


let interactive_mode = (fun filename env initial_mod tc -> (

let _92_189 = if (let _188_195 = (FStar_Options.codegen ())
in (FStar_Option.isSome _188_195)) then begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end else begin
()
end
in (

let rec go = (fun line_col stack curmod env -> (match ((shift_chunk ())) with
| Pop (msg) -> begin
(

let _92_198 = (tc.pop env msg)
in (

let _92_210 = (match (stack) with
| [] -> begin
(

let _92_201 = (FStar_Util.print_error "too many pops")
in (FStar_All.exit (Prims.parse_int "1")))
end
| (hd)::tl -> begin
((hd), (tl))
end)
in (match (_92_210) with
| ((env, curmod), stack) -> begin
(go line_col stack curmod env)
end)))
end
| Push (lc) -> begin
(

let stack = (((env), (curmod)))::stack
in (

let env = (tc.push env "#push")
in (go lc stack curmod env)))
end
| Code (text, (ok, fail)) -> begin
(

let fail = (fun curmod env_mark -> (

let _92_224 = (tc.report_fail ())
in (

let _92_226 = (FStar_Util.print1 "%s\n" fail)
in (

let env = (tc.reset_mark env_mark)
in (go line_col stack curmod env)))))
in (

let env_mark = (tc.mark env)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = (Prims.fst line_col); FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)}
in (

let res = (tc.check_frag env_mark curmod frag)
in (match (res) with
| Some (curmod, env, n_errs) -> begin
if (n_errs = (Prims.parse_int "0")) then begin
(

let _92_237 = (FStar_Util.print1 "\n%s\n" ok)
in (

let env = (tc.commit_mark env)
in (go line_col stack curmod env)))
end else begin
(fail curmod env_mark)
end
end
| _92_241 -> begin
(fail curmod env_mark)
end)))))
end))
in if (((FStar_Options.universes ()) && ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))) && (FStar_Option.isSome filename)) then begin
(let _188_209 = (FStar_Option.get filename)
in (FStar_SMTEncoding_Solver.with_hints_db _188_209 (fun _92_242 -> (match (()) with
| () -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) [] initial_mod env)
end))))
end else begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) [] initial_mod env)
end)))




