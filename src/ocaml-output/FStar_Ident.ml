
open Prims

type ident =
{idText : Prims.string; idRange : FStar_Range.range}


let is_Mkident : ident  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkident"))))


type lident =
{ns : ident Prims.list; ident : ident; nsstr : Prims.string; str : Prims.string}


let is_Mklident : lident  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mklident"))))


type lid =
lident


let mk_ident : (Prims.string * FStar_Range.range)  ->  ident = (fun _26_11 -> (match (_26_11) with
| (text, range) -> begin
{idText = text; idRange = range}
end))


let reserved_prefix : Prims.string = "uu___"


let gen : FStar_Range.range  ->  ident = (

let x = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun r -> (

let _26_14 = (let _122_25 = ((FStar_ST.read x) + (Prims.parse_int "1"))
in (FStar_ST.op_Colon_Equals x _122_25))
in (let _122_29 = (let _122_28 = (let _122_27 = (let _122_26 = (FStar_ST.read x)
in (Prims.string_of_int _122_26))
in (Prims.strcat reserved_prefix _122_27))
in ((_122_28), (r)))
in (mk_ident _122_29)))))


let id_of_text : Prims.string  ->  ident = (fun str -> (mk_ident ((str), (FStar_Range.dummyRange))))


let text_of_id : ident  ->  Prims.string = (fun id -> id.idText)


let text_of_path : Prims.string Prims.list  ->  Prims.string = (fun path -> (FStar_Util.concat_l "." path))


let path_of_text : Prims.string  ->  Prims.string Prims.list = (fun text -> (FStar_String.split (('.')::[]) text))


let path_of_ns : ident Prims.list  ->  Prims.string Prims.list = (fun ns -> (FStar_List.map text_of_id ns))


let path_of_lid : lident  ->  Prims.string Prims.list = (fun lid -> (FStar_List.map text_of_id (FStar_List.append lid.ns ((lid.ident)::[]))))


let ids_of_lid : lident  ->  ident Prims.list = (fun lid -> (FStar_List.append lid.ns ((lid.ident)::[])))


let lid_of_ids : ident Prims.list  ->  lident = (fun ids -> (

let _26_26 = (FStar_Util.prefix ids)
in (match (_26_26) with
| (ns, id) -> begin
(

let nsstr = (let _122_46 = (FStar_List.map text_of_id ns)
in (FStar_All.pipe_right _122_46 text_of_path))
in {ns = ns; ident = id; nsstr = nsstr; str = if (nsstr = "") then begin
id.idText
end else begin
(Prims.strcat nsstr (Prims.strcat "." id.idText))
end})
end)))


let lid_of_path : Prims.string Prims.list  ->  FStar_Range.range  ->  lident = (fun path pos -> (

let ids = (FStar_List.map (fun s -> (mk_ident ((s), (pos)))) path)
in (lid_of_ids ids)))


let text_of_lid : lident  ->  Prims.string = (fun lid -> lid.str)


let lid_equals : lident  ->  lident  ->  Prims.bool = (fun l1 l2 -> (l1.str = l2.str))


let range_of_lid : lid  ->  FStar_Range.range = (fun lid -> lid.ident.idRange)


let set_lid_range : lident  ->  FStar_Range.range  ->  lident = (fun l r -> (

let _26_38 = l
in {ns = _26_38.ns; ident = (

let _26_40 = l.ident
in {idText = _26_40.idText; idRange = r}); nsstr = _26_38.nsstr; str = _26_38.str}))


let lid_add_suffix : lident  ->  Prims.string  ->  lident = (fun l s -> (

let path = (path_of_lid l)
in (lid_of_path (FStar_List.append path ((s)::[])) (range_of_lid l))))


let string_of_lid : lident  ->  Prims.string = (fun lid -> (let _122_70 = (path_of_lid lid)
in (text_of_path _122_70)))




