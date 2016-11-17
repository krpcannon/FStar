
open Prims

let fail_exp = (fun lid t -> (let _177_16 = (let _177_15 = (let _177_14 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.failwith_lid FStar_Syntax_Syntax.Delta_constant None)
in (let _177_13 = (let _177_12 = (FStar_Syntax_Syntax.iarg t)
in (let _177_11 = (let _177_10 = (let _177_9 = (let _177_8 = (let _177_7 = (let _177_6 = (let _177_5 = (let _177_4 = (let _177_3 = (FStar_Syntax_Print.lid_to_string lid)
in (Prims.strcat "Not yet implemented:" _177_3))
in (FStar_Bytes.string_as_unicode_bytes _177_4))
in ((_177_5), (FStar_Range.dummyRange)))
in FStar_Const.Const_string (_177_6))
in FStar_Syntax_Syntax.Tm_constant (_177_7))
in (FStar_Syntax_Syntax.mk _177_8 None FStar_Range.dummyRange))
in (FStar_All.pipe_left FStar_Syntax_Syntax.iarg _177_9))
in (_177_10)::[])
in (_177_12)::_177_11))
in ((_177_14), (_177_13))))
in FStar_Syntax_Syntax.Tm_app (_177_15))
in (FStar_Syntax_Syntax.mk _177_16 None FStar_Range.dummyRange)))


let mangle_projector_lid : FStar_Ident.lident  ->  FStar_Ident.lident = (fun x -> (

let projecteeName = x.FStar_Ident.ident
in (

let _81_20 = (FStar_Util.prefix x.FStar_Ident.ns)
in (match (_81_20) with
| (prefix, constrName) -> begin
(

let mangledName = (FStar_Ident.id_of_text (Prims.strcat "___" (Prims.strcat constrName.FStar_Ident.idText (Prims.strcat "___" projecteeName.FStar_Ident.idText))))
in (FStar_Ident.lid_of_ids (FStar_List.append prefix ((mangledName)::[]))))
end))))


let lident_as_mlsymbol : FStar_Ident.lident  ->  Prims.string = (fun id -> id.FStar_Ident.ident.FStar_Ident.idText)


let binders_as_mlty_binders = (fun env bs -> (FStar_Util.fold_map (fun env _81_29 -> (match (_81_29) with
| (bv, _81_28) -> begin
(let _177_29 = (let _177_27 = (let _177_26 = (let _177_25 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in FStar_Extraction_ML_Syntax.MLTY_Var (_177_25))
in Some (_177_26))
in (FStar_Extraction_ML_UEnv.extend_ty env bv _177_27))
in (let _177_28 = (FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv)
in ((_177_29), (_177_28))))
end)) env bs))


let extract_typ_abbrev : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env fv quals def -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let def = (let _177_39 = (let _177_38 = (FStar_Syntax_Subst.compress def)
in (FStar_All.pipe_right _177_38 FStar_Syntax_Util.unmeta))
in (FStar_All.pipe_right _177_39 FStar_Syntax_Util.un_uinst))
in (

let def = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_81_37) -> begin
(FStar_Extraction_ML_Term.normalize_abs def)
end
| _81_40 -> begin
def
end)
in (

let _81_52 = (match (def.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _81_45) -> begin
(FStar_Syntax_Subst.open_term bs body)
end
| _81_49 -> begin
(([]), (def))
end)
in (match (_81_52) with
| (bs, body) -> begin
(

let assumed = (FStar_Util.for_some (fun _81_1 -> (match (_81_1) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _81_56 -> begin
false
end)) quals)
in (

let _81_60 = (binders_as_mlty_binders env bs)
in (match (_81_60) with
| (env, ml_bs) -> begin
(

let body = (let _177_41 = (FStar_Extraction_ML_Term.term_as_mlty env body)
in (FStar_All.pipe_right _177_41 (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env))))
in (

let mangled_projector = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _81_2 -> (match (_81_2) with
| FStar_Syntax_Syntax.Projector (_81_64) -> begin
true
end
| _81_67 -> begin
false
end)))) then begin
(

let mname = (mangle_projector_lid lid)
in Some (mname.FStar_Ident.ident.FStar_Ident.idText))
end else begin
None
end
in (

let td = (((assumed), ((lident_as_mlsymbol lid)), (mangled_projector), (ml_bs), (Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev (body)))))::[]
in (

let def = (let _177_44 = (let _177_43 = (FStar_Extraction_ML_Util.mlloc_of_range (FStar_Ident.range_of_lid lid))
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_43))
in (_177_44)::(FStar_Extraction_ML_Syntax.MLM_Ty (td))::[])
in (

let env = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _81_3 -> (match (_81_3) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.New) -> begin
true
end
| _81_76 -> begin
false
end)))) then begin
env
end else begin
(FStar_Extraction_ML_UEnv.extend_tydef env fv td)
end
in ((env), (def)))))))
end)))
end))))))


type data_constructor =
{dname : FStar_Ident.lident; dtyp : FStar_Syntax_Syntax.typ}


let is_Mkdata_constructor : data_constructor  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdata_constructor"))))


type inductive_family =
{iname : FStar_Ident.lident; iparams : FStar_Syntax_Syntax.binders; ityp : FStar_Syntax_Syntax.term; idatas : data_constructor Prims.list; iquals : FStar_Syntax_Syntax.qualifier Prims.list}


let is_Mkinductive_family : inductive_family  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkinductive_family"))))


let print_ifamily : inductive_family  ->  Prims.unit = (fun i -> (let _177_79 = (FStar_Syntax_Print.lid_to_string i.iname)
in (let _177_78 = (FStar_Syntax_Print.binders_to_string " " i.iparams)
in (let _177_77 = (FStar_Syntax_Print.term_to_string i.ityp)
in (let _177_76 = (let _177_75 = (FStar_All.pipe_right i.idatas (FStar_List.map (fun d -> (let _177_74 = (FStar_Syntax_Print.lid_to_string d.dname)
in (let _177_73 = (let _177_72 = (FStar_Syntax_Print.term_to_string d.dtyp)
in (Prims.strcat " : " _177_72))
in (Prims.strcat _177_74 _177_73))))))
in (FStar_All.pipe_right _177_75 (FStar_String.concat "\n\t\t")))
in (FStar_Util.print4 "\n\t%s %s : %s { %s }\n" _177_79 _177_78 _177_77 _177_76))))))


let bundle_as_inductive_families = (fun env ses quals -> (FStar_All.pipe_right ses (FStar_List.collect (fun _81_5 -> (match (_81_5) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _us, bs, t, _mut_i, datas, quals, r) -> begin
(

let _81_105 = (FStar_Syntax_Subst.open_term bs t)
in (match (_81_105) with
| (bs, t) -> begin
(

let datas = (FStar_All.pipe_right ses (FStar_List.collect (fun _81_4 -> (match (_81_4) with
| FStar_Syntax_Syntax.Sig_datacon (d, _81_109, t, l', nparams, _81_114, _81_116, _81_118) when (FStar_Ident.lid_equals l l') -> begin
(

let _81_123 = (FStar_Syntax_Util.arrow_formals t)
in (match (_81_123) with
| (bs', body) -> begin
(

let _81_126 = (FStar_Util.first_N (FStar_List.length bs) bs')
in (match (_81_126) with
| (bs_params, rest) -> begin
(

let subst = (FStar_List.map2 (fun _81_130 _81_134 -> (match (((_81_130), (_81_134))) with
| ((b', _81_129), (b, _81_133)) -> begin
(let _177_88 = (let _177_87 = (FStar_Syntax_Syntax.bv_to_name b)
in ((b'), (_177_87)))
in FStar_Syntax_Syntax.NT (_177_88))
end)) bs_params bs)
in (

let t = (let _177_90 = (let _177_89 = (FStar_Syntax_Syntax.mk_Total body)
in (FStar_Syntax_Util.arrow rest _177_89))
in (FStar_All.pipe_right _177_90 (FStar_Syntax_Subst.subst subst)))
in ({dname = d; dtyp = t})::[]))
end))
end))
end
| _81_138 -> begin
[]
end))))
in ({iname = l; iparams = bs; ityp = t; idatas = datas; iquals = quals})::[])
end))
end
| _81_141 -> begin
[]
end)))))


type env_t =
FStar_Extraction_ML_UEnv.env


let extract_bundle : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun env se -> (

let extract_ctor = (fun ml_tyvars env ctor -> (

let mlt = (let _177_101 = (FStar_Extraction_ML_Term.term_as_mlty env ctor.dtyp)
in (FStar_Extraction_ML_Util.eraseTypeDeep (FStar_Extraction_ML_Util.udelta_unfold env) _177_101))
in (

let tys = ((ml_tyvars), (mlt))
in (

let fvv = (FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp)
in (let _177_104 = (FStar_Extraction_ML_UEnv.extend_fv env fvv tys false false)
in (let _177_103 = (let _177_102 = (FStar_Extraction_ML_Util.argTypes mlt)
in (((lident_as_mlsymbol ctor.dname)), (_177_102)))
in ((_177_104), (_177_103))))))))
in (

let extract_one_family = (fun env ind -> (

let _81_156 = (binders_as_mlty_binders env ind.iparams)
in (match (_81_156) with
| (env, vars) -> begin
(

let _81_159 = (FStar_All.pipe_right ind.idatas (FStar_Util.fold_map (extract_ctor vars) env))
in (match (_81_159) with
| (env, ctors) -> begin
(

let _81_163 = (FStar_Syntax_Util.arrow_formals ind.ityp)
in (match (_81_163) with
| (indices, _81_162) -> begin
(

let ml_params = (let _177_113 = (FStar_All.pipe_right indices (FStar_List.mapi (fun i _81_165 -> (let _177_112 = (let _177_111 = (FStar_Util.string_of_int i)
in (Prims.strcat "\'dummyV" _177_111))
in ((_177_112), ((Prims.parse_int "0")))))))
in (FStar_List.append vars _177_113))
in (

let tbody = (match ((FStar_Util.find_opt (fun _81_6 -> (match (_81_6) with
| FStar_Syntax_Syntax.RecordType (_81_170) -> begin
true
end
| _81_173 -> begin
false
end)) ind.iquals)) with
| Some (FStar_Syntax_Syntax.RecordType (ids)) -> begin
(

let _81_180 = (FStar_List.hd ctors)
in (match (_81_180) with
| (_81_178, c_ty) -> begin
(

let _81_181 = ()
in (

let fields = (FStar_List.map2 (fun lid ty -> (((lident_as_mlsymbol lid)), (ty))) ids c_ty)
in FStar_Extraction_ML_Syntax.MLTD_Record (fields)))
end))
end
| _81_187 -> begin
FStar_Extraction_ML_Syntax.MLTD_DType (ctors)
end)
in ((env), (((false), ((lident_as_mlsymbol ind.iname)), (None), (ml_params), (Some (tbody)))))))
end))
end))
end)))
in (match (se) with
| FStar_Syntax_Syntax.Sig_bundle ((FStar_Syntax_Syntax.Sig_datacon (l, _81_191, t, _81_194, _81_196, _81_198, _81_200, _81_202))::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], _81_209, r) -> begin
(

let _81_215 = (extract_ctor [] env {dname = l; dtyp = t})
in (match (_81_215) with
| (env, ctor) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Exn (ctor))::[]))
end))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, quals, _81_219, r) -> begin
(

let ifams = (bundle_as_inductive_families env ses quals)
in (

let _81_226 = (FStar_Util.fold_map extract_one_family env ifams)
in (match (_81_226) with
| (env, td) -> begin
((env), ((FStar_Extraction_ML_Syntax.MLM_Ty (td))::[]))
end)))
end
| _81_228 -> begin
(FStar_All.failwith "Unexpected signature element")
end))))


let level_of_sigelt : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun g se -> (

let l = (fun _81_7 -> (match (_81_7) with
| FStar_Extraction_ML_Term.Term_level -> begin
"Term_level"
end
| FStar_Extraction_ML_Term.Type_level -> begin
"Type_level"
end
| FStar_Extraction_ML_Term.Kind_level -> begin
"Kind_level"
end))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(FStar_Util.print_string "\t\tInductive bundle")
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _81_247, t, quals, _81_251) -> begin
(let _177_126 = (FStar_Syntax_Print.lid_to_string lid)
in (let _177_125 = (let _177_124 = (let _177_123 = (FStar_Extraction_ML_Term.level g t)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor t) _177_123))
in (l _177_124))
in (FStar_Util.print2 "\t\t%s @ %s\n" _177_126 _177_125)))
end
| FStar_Syntax_Syntax.Sig_let ((_81_255, (lb)::_81_257), _81_262, _81_264, _81_266) -> begin
(let _177_134 = (let _177_129 = (let _177_128 = (let _177_127 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _177_127.FStar_Syntax_Syntax.fv_name)
in _177_128.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_129 FStar_Syntax_Print.lid_to_string))
in (let _177_133 = (FStar_Syntax_Print.term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (let _177_132 = (let _177_131 = (let _177_130 = (FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp)
in (FStar_All.pipe_left (FStar_Extraction_ML_Term.predecessor lb.FStar_Syntax_Syntax.lbtyp) _177_130))
in (l _177_131))
in (FStar_Util.print3 "\t\t%s : %s @ %s\n" _177_134 _177_133 _177_132))))
end
| _81_270 -> begin
(FStar_Util.print_string "other\n")
end)))


let rec extract_sig : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list) = (fun g se -> (

let _81_276 = (FStar_Extraction_ML_UEnv.debug g (fun u -> (

let _81_274 = (let _177_141 = (let _177_140 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.format1 ">>>> extract_sig :  %s \n" _177_140))
in (FStar_Util.print_string _177_141))
in (level_of_sigelt g se))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_bundle (_)) | (FStar_Syntax_Syntax.Sig_inductive_typ (_)) | (FStar_Syntax_Syntax.Sig_datacon (_)) -> begin
(extract_bundle g se)
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _81_289) when (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let extend_env = (fun g lid ml_name tm tysc -> (

let mangled_name = (Prims.snd ml_name)
in (

let g = (let _177_152 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Extraction_ML_UEnv.extend_fv' g _177_152 ml_name tysc false false))
in (

let lb = {FStar_Extraction_ML_Syntax.mllb_name = ((mangled_name), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = None; FStar_Extraction_ML_Syntax.mllb_add_unit = false; FStar_Extraction_ML_Syntax.mllb_def = tm; FStar_Extraction_ML_Syntax.print_typ = false}
in ((g), (FStar_Extraction_ML_Syntax.MLM_Let (((FStar_Extraction_ML_Syntax.NonRec), ([]), ((lb)::[])))))))))
in (

let rec extract_fv = (fun tm -> (match ((let _177_155 = (FStar_Syntax_Subst.compress tm)
in _177_155.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (tm, _81_305) -> begin
(extract_fv tm)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let mlp = (FStar_Extraction_ML_Syntax.mlpath_of_lident fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let _81_316 = (let _177_156 = (FStar_Extraction_ML_UEnv.lookup_fv g fv)
in (FStar_All.pipe_left FStar_Util.right _177_156))
in (match (_81_316) with
| (_81_312, tysc, _81_315) -> begin
(let _177_157 = (FStar_All.pipe_left (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top) (FStar_Extraction_ML_Syntax.MLE_Name (mlp)))
in ((_177_157), (tysc)))
end)))
end
| _81_318 -> begin
(FStar_All.failwith "Not an fv")
end))
in (

let extract_action = (fun g a -> (

let _81_324 = (extract_fv a.FStar_Syntax_Syntax.action_defn)
in (match (_81_324) with
| (a_tm, ty_sc) -> begin
(

let _81_327 = (FStar_Extraction_ML_UEnv.action_name ed a)
in (match (_81_327) with
| (a_nm, a_lid) -> begin
(extend_env g a_lid a_nm a_tm ty_sc)
end))
end)))
in (

let _81_336 = (

let _81_330 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.return_repr))
in (match (_81_330) with
| (return_tm, ty_sc) -> begin
(

let _81_333 = (FStar_Extraction_ML_UEnv.monad_op_name ed "return")
in (match (_81_333) with
| (return_nm, return_lid) -> begin
(extend_env g return_lid return_nm return_tm ty_sc)
end))
end))
in (match (_81_336) with
| (g, return_decl) -> begin
(

let _81_345 = (

let _81_339 = (extract_fv (Prims.snd ed.FStar_Syntax_Syntax.bind_repr))
in (match (_81_339) with
| (bind_tm, ty_sc) -> begin
(

let _81_342 = (FStar_Extraction_ML_UEnv.monad_op_name ed "bind")
in (match (_81_342) with
| (bind_nm, bind_lid) -> begin
(extend_env g bind_lid bind_nm bind_tm ty_sc)
end))
end))
in (match (_81_345) with
| (g, bind_decl) -> begin
(

let _81_348 = (FStar_Util.fold_map extract_action g ed.FStar_Syntax_Syntax.actions)
in (match (_81_348) with
| (g, actions) -> begin
((g), ((FStar_List.append ((return_decl)::(bind_decl)::[]) actions)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_new_effect (_81_350) -> begin
((g), ([]))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _81_354, t, quals, _81_358) when ((FStar_Extraction_ML_Term.level g t) = FStar_Extraction_ML_Term.Kind_level) -> begin
if (let _177_163 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _81_8 -> (match (_81_8) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _81_364 -> begin
false
end))))
in (FStar_All.pipe_right _177_163 Prims.op_Negation)) then begin
((g), ([]))
end else begin
(

let _81_368 = (FStar_Syntax_Util.arrow_formals t)
in (match (_81_368) with
| (bs, _81_367) -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (let _177_164 = (FStar_Syntax_Util.abs bs FStar_TypeChecker_Common.t_unit None)
in (extract_typ_abbrev g fv quals _177_164)))
end))
end
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _81_375, _81_377, quals) when ((FStar_Extraction_ML_Term.level g lb.FStar_Syntax_Syntax.lbtyp) = FStar_Extraction_ML_Term.Kind_level) -> begin
(let _177_165 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (extract_typ_abbrev g _177_165 quals lb.FStar_Syntax_Syntax.lbdef))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _81_384, quals) -> begin
(

let elet = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((lbs), (FStar_Syntax_Const.exp_false_bool)))) None r)
in (

let _81_394 = (FStar_Extraction_ML_Term.term_as_mlexpr g elet)
in (match (_81_394) with
| (ml_let, _81_391, _81_393) -> begin
(match (ml_let.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Let ((flavor, _81_397, bindings), _81_401) -> begin
(

let _81_433 = (FStar_List.fold_left2 (fun _81_406 ml_lb _81_416 -> (match (((_81_406), (_81_416))) with
| ((env, ml_lbs), {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _81_414; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = _81_411; FStar_Syntax_Syntax.lbdef = _81_409}) -> begin
(

let lb_lid = (let _177_170 = (let _177_169 = (FStar_Util.right lbname)
in _177_169.FStar_Syntax_Syntax.fv_name)
in _177_170.FStar_Syntax_Syntax.v)
in (

let _81_430 = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _81_9 -> (match (_81_9) with
| FStar_Syntax_Syntax.Projector (_81_420) -> begin
true
end
| _81_423 -> begin
false
end)))) then begin
(

let mname = (let _177_172 = (mangle_projector_lid lb_lid)
in (FStar_All.pipe_right _177_172 FStar_Extraction_ML_Syntax.mlpath_of_lident))
in (

let env = (let _177_174 = (FStar_Util.right lbname)
in (let _177_173 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_fv' env _177_174 mname _177_173 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false)))
in ((env), ((

let _81_426 = ml_lb
in {FStar_Extraction_ML_Syntax.mllb_name = (((Prims.snd mname)), ((Prims.parse_int "0"))); FStar_Extraction_ML_Syntax.mllb_tysc = _81_426.FStar_Extraction_ML_Syntax.mllb_tysc; FStar_Extraction_ML_Syntax.mllb_add_unit = _81_426.FStar_Extraction_ML_Syntax.mllb_add_unit; FStar_Extraction_ML_Syntax.mllb_def = _81_426.FStar_Extraction_ML_Syntax.mllb_def; FStar_Extraction_ML_Syntax.print_typ = _81_426.FStar_Extraction_ML_Syntax.print_typ})))))
end else begin
(let _177_177 = (let _177_176 = (let _177_175 = (FStar_Util.must ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc)
in (FStar_Extraction_ML_UEnv.extend_lb env lbname t _177_175 ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit false))
in (FStar_All.pipe_left Prims.fst _177_176))
in ((_177_177), (ml_lb)))
end
in (match (_81_430) with
| (g, ml_lb) -> begin
((g), ((ml_lb)::ml_lbs))
end)))
end)) ((g), ([])) bindings (Prims.snd lbs))
in (match (_81_433) with
| (g, ml_lbs') -> begin
(

let flags = (let _177_181 = if (FStar_Util.for_some (fun _81_10 -> (match (_81_10) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| _81_437 -> begin
false
end)) quals) then begin
(FStar_Extraction_ML_Syntax.Assumed)::[]
end else begin
[]
end
in (let _177_180 = if (FStar_Util.for_some (fun _81_11 -> (match (_81_11) with
| FStar_Syntax_Syntax.Private -> begin
true
end
| _81_441 -> begin
false
end)) quals) then begin
(FStar_Extraction_ML_Syntax.Private)::[]
end else begin
[]
end
in (FStar_List.append _177_181 _177_180)))
in (let _177_184 = (let _177_183 = (let _177_182 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_182))
in (_177_183)::(FStar_Extraction_ML_Syntax.MLM_Let (((flavor), (flags), ((FStar_List.rev ml_lbs')))))::[])
in ((g), (_177_184))))
end))
end
| _81_444 -> begin
(let _177_186 = (let _177_185 = (FStar_Extraction_ML_Code.string_of_mlexpr g.FStar_Extraction_ML_UEnv.currentModule ml_let)
in (FStar_Util.format1 "Impossible: Translated a let to a non-let: %s" _177_185))
in (FStar_All.failwith _177_186))
end)
end)))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _81_447, t, quals, r) -> begin
if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
(

let always_fail = (

let imp = (match ((FStar_Syntax_Util.arrow_formals t)) with
| ([], t) -> begin
(fail_exp lid t)
end
| (bs, t) -> begin
(let _177_187 = (fail_exp lid t)
in (FStar_Syntax_Util.abs bs _177_187 None))
end)
in (let _177_193 = (let _177_192 = (let _177_191 = (let _177_190 = (let _177_189 = (let _177_188 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in FStar_Util.Inr (_177_188))
in {FStar_Syntax_Syntax.lbname = _177_189; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ML_lid; FStar_Syntax_Syntax.lbdef = imp})
in (_177_190)::[])
in ((false), (_177_191)))
in ((_177_192), (r), ([]), (quals)))
in FStar_Syntax_Syntax.Sig_let (_177_193)))
in (

let _81_463 = (extract_sig g always_fail)
in (match (_81_463) with
| (g, mlm) -> begin
(match ((FStar_Util.find_map quals (fun _81_12 -> (match (_81_12) with
| FStar_Syntax_Syntax.Discriminator (l) -> begin
Some (l)
end
| _81_468 -> begin
None
end)))) with
| Some (l) -> begin
(let _177_199 = (let _177_198 = (let _177_195 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_195))
in (let _177_197 = (let _177_196 = (FStar_Extraction_ML_Term.ind_discriminator_body g lid l)
in (_177_196)::[])
in (_177_198)::_177_197))
in ((g), (_177_199)))
end
| _81_472 -> begin
(match ((FStar_Util.find_map quals (fun _81_13 -> (match (_81_13) with
| FStar_Syntax_Syntax.Projector (l, _81_476) -> begin
Some (l)
end
| _81_480 -> begin
None
end)))) with
| Some (_81_482) -> begin
((g), ([]))
end
| _81_485 -> begin
((g), (mlm))
end)
end)
end)))
end else begin
((g), ([]))
end
end
| FStar_Syntax_Syntax.Sig_main (e, r) -> begin
(

let _81_495 = (FStar_Extraction_ML_Term.term_as_mlexpr g e)
in (match (_81_495) with
| (ml_main, _81_492, _81_494) -> begin
(let _177_203 = (let _177_202 = (let _177_201 = (FStar_Extraction_ML_Util.mlloc_of_range r)
in FStar_Extraction_ML_Syntax.MLM_Loc (_177_201))
in (_177_202)::(FStar_Extraction_ML_Syntax.MLM_Top (ml_main))::[])
in ((g), (_177_203)))
end))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_81_497) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_assume (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_pragma (_)) -> begin
((g), ([]))
end)))


let extract_iface : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  env_t = (fun g m -> (let _177_208 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right _177_208 Prims.fst)))


let rec extract : FStar_Extraction_ML_UEnv.env  ->  FStar_Syntax_Syntax.modul  ->  (FStar_Extraction_ML_UEnv.env * FStar_Extraction_ML_Syntax.mllib Prims.list) = (fun g m -> (

let _81_515 = (FStar_Syntax_Syntax.reset_gensym ())
in (

let name = (FStar_Extraction_ML_Syntax.mlpath_of_lident m.FStar_Syntax_Syntax.name)
in (

let g = (

let _81_518 = g
in {FStar_Extraction_ML_UEnv.tcenv = _81_518.FStar_Extraction_ML_UEnv.tcenv; FStar_Extraction_ML_UEnv.gamma = _81_518.FStar_Extraction_ML_UEnv.gamma; FStar_Extraction_ML_UEnv.tydefs = _81_518.FStar_Extraction_ML_UEnv.tydefs; FStar_Extraction_ML_UEnv.currentModule = name})
in if (((m.FStar_Syntax_Syntax.name.FStar_Ident.str = "Prims") || m.FStar_Syntax_Syntax.is_interface) || (FStar_Options.no_extract m.FStar_Syntax_Syntax.name.FStar_Ident.str)) then begin
(

let g = (extract_iface g m)
in ((g), ([])))
end else begin
(

let _81_522 = (let _177_213 = (FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name)
in (FStar_Util.print1 "Extracting module %s\n" _177_213))
in (

let _81_526 = (FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations)
in (match (_81_526) with
| (g, sigs) -> begin
(

let mlm = (FStar_List.flatten sigs)
in ((g), ((FStar_Extraction_ML_Syntax.MLLib ((((name), (Some ((([]), (mlm)))), (FStar_Extraction_ML_Syntax.MLLib ([]))))::[]))::[])))
end)))
end))))




