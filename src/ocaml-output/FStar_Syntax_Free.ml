
open Prims

let no_free_vars : FStar_Syntax_Syntax.free_vars = {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}


let singleton_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _133_4 = (let _133_3 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Util.set_add x _133_3))
in {FStar_Syntax_Syntax.free_names = _133_4; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))


let singleton_uv : ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _133_8 = (let _133_7 = (FStar_Syntax_Syntax.new_uv_set ())
in (FStar_Util.set_add x _133_7))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = _133_8; FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars}))


let singleton_univ : FStar_Syntax_Syntax.universe_uvar  ->  FStar_Syntax_Syntax.free_vars = (fun x -> (let _133_12 = (let _133_11 = (FStar_Syntax_Syntax.new_universe_uvar_set ())
in (FStar_Util.set_add x _133_11))
in {FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names; FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs; FStar_Syntax_Syntax.free_univs = _133_12}))


let union : FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun f1 f2 -> (let _133_19 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_names f2.FStar_Syntax_Syntax.free_names)
in (let _133_18 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_uvars f2.FStar_Syntax_Syntax.free_uvars)
in (let _133_17 = (FStar_Util.set_union f1.FStar_Syntax_Syntax.free_univs f2.FStar_Syntax_Syntax.free_univs)
in {FStar_Syntax_Syntax.free_names = _133_19; FStar_Syntax_Syntax.free_uvars = _133_18; FStar_Syntax_Syntax.free_univs = _133_17}))))


let rec free_univs : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.free_vars = (fun u -> (match ((FStar_Syntax_Subst.compress_univ u)) with
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(free_univs u)
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_List.fold_left (fun out x -> (let _133_24 = (free_univs x)
in (union out _133_24))) no_free_vars us)
end
| FStar_Syntax_Syntax.U_unif (u) -> begin
(singleton_univ u)
end))


let rec free_names_and_uvs' : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun tm -> (

let aux_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _37_31 -> (match (_37_31) with
| (x, _37_30) -> begin
(let _133_40 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _133_40))
end)) acc)))
in (

let t = (FStar_Syntax_Subst.compress tm)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_37_34) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(singleton_bv x)
end
| FStar_Syntax_Syntax.Tm_uvar (x, t) -> begin
(singleton_uv ((x), (t)))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(free_univs u)
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
no_free_vars
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let f = (free_names_and_uvars t)
in (FStar_List.fold_left (fun out u -> (let _133_46 = (free_univs u)
in (union out _133_46))) f us))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t, _37_64) -> begin
(let _133_47 = (free_names_and_uvars t)
in (aux_binders bs _133_47))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _133_48 = (free_names_and_uvars_comp c)
in (aux_binders bs _133_48))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t) -> begin
(let _133_49 = (free_names_and_uvars t)
in (aux_binders ((((bv), (None)))::[]) _133_49))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(let _133_50 = (free_names_and_uvars t)
in (free_names_and_uvars_args args _133_50))
end
| FStar_Syntax_Syntax.Tm_match (t, pats) -> begin
(let _133_59 = (let _133_58 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n _37_87 -> (match (_37_87) with
| (p, wopt, t) -> begin
(

let n1 = (match (wopt) with
| None -> begin
no_free_vars
end
| Some (w) -> begin
(free_names_and_uvars w)
end)
in (

let n2 = (free_names_and_uvars t)
in (

let n = (let _133_53 = (union n2 n)
in (union n1 _133_53))
in (let _133_57 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _133_57 (FStar_List.fold_left (fun n x -> (let _133_56 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _133_56))) n))))))
end)) _133_58))
in (FStar_All.pipe_right pats _133_59))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), _37_100) -> begin
(let _133_61 = (free_names_and_uvars t1)
in (let _133_60 = (free_names_and_uvars t2)
in (union _133_61 _133_60)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), _37_107) -> begin
(let _133_63 = (free_names_and_uvars t1)
in (let _133_62 = (free_names_and_uvars_comp c)
in (union _133_63 _133_62)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, t) -> begin
(let _133_70 = (let _133_69 = (free_names_and_uvars t)
in (FStar_List.fold_left (fun n lb -> (let _133_68 = (let _133_67 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp)
in (let _133_66 = (free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef)
in (union _133_67 _133_66)))
in (union n _133_68))) _133_69))
in (FStar_All.pipe_right (Prims.snd lbs) _133_70))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _133_71 = (free_names_and_uvars t)
in (FStar_List.fold_right free_names_and_uvars_args args _133_71))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (_37_123, t')) -> begin
(let _133_73 = (free_names_and_uvars t)
in (let _133_72 = (free_names_and_uvars t')
in (union _133_73 _133_72)))
end
| FStar_Syntax_Syntax.Tm_meta (t, _37_131) -> begin
(free_names_and_uvars t)
end))))
and free_names_and_uvars : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.free_vars = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match ((FStar_ST.read t.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(

let _37_138 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars t))
end else begin
n
end
end
| _37_141 -> begin
(

let n = (free_names_and_uvs' t)
in (

let _37_143 = (FStar_ST.op_Colon_Equals t.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end)))
and free_names_and_uvars_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.free_vars  ->  FStar_Syntax_Syntax.free_vars = (fun args acc -> (FStar_All.pipe_right args (FStar_List.fold_left (fun n _37_151 -> (match (_37_151) with
| (x, _37_150) -> begin
(let _133_79 = (free_names_and_uvars x)
in (union n _133_79))
end)) acc)))
and free_names_and_uvars_binders = (fun bs acc -> (FStar_All.pipe_right bs (FStar_List.fold_left (fun n _37_158 -> (match (_37_158) with
| (x, _37_157) -> begin
(let _133_82 = (free_names_and_uvars x.FStar_Syntax_Syntax.sort)
in (union n _133_82))
end)) acc)))
and free_names_and_uvars_comp : FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.free_vars = (fun c -> (match ((FStar_ST.read c.FStar_Syntax_Syntax.vars)) with
| Some (n) -> begin
if (should_invalidate_cache n) then begin
(

let _37_162 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars None)
in (free_names_and_uvars_comp c))
end else begin
n
end
end
| _37_165 -> begin
(

let n = (match (c.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.GTotal (t, None)) | (FStar_Syntax_Syntax.Total (t, None)) -> begin
(free_names_and_uvars t)
end
| (FStar_Syntax_Syntax.GTotal (t, Some (u))) | (FStar_Syntax_Syntax.Total (t, Some (u))) -> begin
(let _133_85 = (free_univs u)
in (let _133_84 = (free_names_and_uvars t)
in (union _133_85 _133_84)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let us = (let _133_86 = (free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ)
in (free_names_and_uvars_args ct.FStar_Syntax_Syntax.effect_args _133_86))
in (FStar_List.fold_left (fun us u -> (let _133_89 = (free_univs u)
in (union us _133_89))) us ct.FStar_Syntax_Syntax.comp_univs))
end)
in (

let _37_187 = (FStar_ST.op_Colon_Equals c.FStar_Syntax_Syntax.vars (Some (n)))
in n))
end))
and should_invalidate_cache : FStar_Syntax_Syntax.free_vars  ->  Prims.bool = (fun n -> ((let _133_92 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars FStar_Util.set_elements)
in (FStar_All.pipe_right _133_92 (FStar_Util.for_some (fun _37_193 -> (match (_37_193) with
| (u, _37_192) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Fixed (_37_195) -> begin
true
end
| _37_198 -> begin
false
end)
end))))) || (let _133_94 = (FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs FStar_Util.set_elements)
in (FStar_All.pipe_right _133_94 (FStar_Util.for_some (fun u -> (match ((FStar_Unionfind.find u)) with
| Some (_37_201) -> begin
true
end
| None -> begin
false
end)))))))


let names : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun t -> (let _133_97 = (free_names_and_uvars t)
in _133_97.FStar_Syntax_Syntax.free_names))


let uvars : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) FStar_Util.set = (fun t -> (let _133_100 = (free_names_and_uvars t)
in _133_100.FStar_Syntax_Syntax.free_uvars))


let univs : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun t -> (let _133_103 = (free_names_and_uvars t)
in _133_103.FStar_Syntax_Syntax.free_univs))


let names_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.bv FStar_Util.set = (fun bs -> (let _133_106 = (free_names_and_uvars_binders bs no_free_vars)
in _133_106.FStar_Syntax_Syntax.free_names))




