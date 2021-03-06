open Prims
type binding =
  | Binding_var of FStar_Syntax_Syntax.bv
  | Binding_lid of (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
  FStar_Pervasives_Native.tuple2
  | Binding_sig of (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
  FStar_Pervasives_Native.tuple2
  | Binding_univ of FStar_Syntax_Syntax.univ_name
  | Binding_sig_inst of
  (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
  FStar_Pervasives_Native.tuple3
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____34 -> false
let __proj__Binding_var__item___0: binding -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_lid: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_lid _0 -> true | uu____48 -> false
let __proj__Binding_lid__item___0:
  binding ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.tscheme)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_lid _0 -> _0
let uu___is_Binding_sig: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig _0 -> true | uu____69 -> false
let __proj__Binding_sig__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_sig _0 -> _0
let uu___is_Binding_univ: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_univ _0 -> true | uu____90 -> false
let __proj__Binding_univ__item___0: binding -> FStar_Syntax_Syntax.univ_name
  = fun projectee  -> match projectee with | Binding_univ _0 -> _0
let uu___is_Binding_sig_inst: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_sig_inst _0 -> true | uu____106 -> false
let __proj__Binding_sig_inst__item___0:
  binding ->
    (FStar_Ident.lident Prims.list,FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Binding_sig_inst _0 -> _0
type delta_level =
  | NoDelta
  | Inlining
  | Eager_unfolding_only
  | Unfold of FStar_Syntax_Syntax.delta_depth
let uu___is_NoDelta: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | NoDelta  -> true | uu____133 -> false
let uu___is_Inlining: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Inlining  -> true | uu____137 -> false
let uu___is_Eager_unfolding_only: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Eager_unfolding_only  -> true | uu____141 -> false
let uu___is_Unfold: delta_level -> Prims.bool =
  fun projectee  ->
    match projectee with | Unfold _0 -> true | uu____146 -> false
let __proj__Unfold__item___0: delta_level -> FStar_Syntax_Syntax.delta_depth
  = fun projectee  -> match projectee with | Unfold _0 -> _0
type mlift =
  {
  mlift_wp:
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ;
  mlift_term:
    (FStar_Syntax_Syntax.typ ->
       FStar_Syntax_Syntax.typ ->
         FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option;}
type edge =
  {
  msource: FStar_Ident.lident;
  mtarget: FStar_Ident.lident;
  mlift: mlift;}
type effects =
  {
  decls:
    (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list;
  order: edge Prims.list;
  joins:
    (FStar_Ident.lident,FStar_Ident.lident,FStar_Ident.lident,mlift,mlift)
      FStar_Pervasives_Native.tuple5 Prims.list;}
type cached_elt =
  (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.universes
                                                                   FStar_Pervasives_Native.option)
                                       FStar_Pervasives_Native.tuple2)
     FStar_Util.either,FStar_Range.range)
    FStar_Pervasives_Native.tuple2
type goal = FStar_Syntax_Syntax.term
type env =
  {
  solver: solver_t;
  range: FStar_Range.range;
  curmodule: FStar_Ident.lident;
  gamma: binding Prims.list;
  gamma_cache: cached_elt FStar_Util.smap;
  modules: FStar_Syntax_Syntax.modul Prims.list;
  expected_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option;
  sigtab: FStar_Syntax_Syntax.sigelt FStar_Util.smap;
  is_pattern: Prims.bool;
  instantiate_imp: Prims.bool;
  effects: effects;
  generalize: Prims.bool;
  letrecs:
    (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 Prims.list;
  top_level: Prims.bool;
  check_uvars: Prims.bool;
  use_eq: Prims.bool;
  is_iface: Prims.bool;
  admit: Prims.bool;
  lax: Prims.bool;
  lax_universes: Prims.bool;
  type_of:
    env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
          FStar_Pervasives_Native.tuple3;
  universe_of:
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe;
  use_bv_sorts: Prims.bool;
  qname_and_index:
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option;}
and solver_t =
  {
  init: env -> Prims.unit;
  push: Prims.string -> Prims.unit;
  pop: Prims.string -> Prims.unit;
  mark: Prims.string -> Prims.unit;
  reset_mark: Prims.string -> Prims.unit;
  commit_mark: Prims.string -> Prims.unit;
  encode_modul: env -> FStar_Syntax_Syntax.modul -> Prims.unit;
  encode_sig: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit;
  preprocess:
    env -> goal -> (env,goal) FStar_Pervasives_Native.tuple2 Prims.list;
  solve:
    (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
      env -> FStar_Syntax_Syntax.typ -> Prims.unit;
  is_trivial: env -> FStar_Syntax_Syntax.typ -> Prims.bool;
  finish: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;}
and guard_t =
  {
  guard_f: FStar_TypeChecker_Common.guard_formula;
  deferred: FStar_TypeChecker_Common.deferred;
  univ_ineqs:
    (FStar_Syntax_Syntax.universe Prims.list,FStar_TypeChecker_Common.univ_ineq
                                               Prims.list)
      FStar_Pervasives_Native.tuple2;
  implicits:
    (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
      FStar_Syntax_Syntax.typ,FStar_Range.range)
      FStar_Pervasives_Native.tuple6 Prims.list;}
type implicits =
  (Prims.string,env,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.typ,FStar_Range.range) FStar_Pervasives_Native.tuple6
    Prims.list
type env_t = env
type sigtable = FStar_Syntax_Syntax.sigelt FStar_Util.smap
let should_verify: env -> Prims.bool =
  fun env  ->
    ((Prims.op_Negation env.lax) && (Prims.op_Negation env.admit)) &&
      (FStar_Options.should_verify (env.curmodule).FStar_Ident.str)
let visible_at: delta_level -> FStar_Syntax_Syntax.qualifier -> Prims.bool =
  fun d  ->
    fun q  ->
      match (d, q) with
      | (NoDelta ,uu____929) -> true
      | (Eager_unfolding_only
         ,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) -> true
      | (Unfold
         uu____930,FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ) ->
          true
      | (Unfold uu____931,FStar_Syntax_Syntax.Visible_default ) -> true
      | (Inlining ,FStar_Syntax_Syntax.Inline_for_extraction ) -> true
      | uu____932 -> false
let default_table_size: Prims.int = Prims.parse_int "200"
let new_sigtab uu____942 = FStar_Util.smap_create default_table_size
let new_gamma_cache uu____950 =
  FStar_Util.smap_create (Prims.parse_int "100")
let initial_env:
  (env ->
     FStar_Syntax_Syntax.term ->
       (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,guard_t)
         FStar_Pervasives_Native.tuple3)
    ->
    (env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe) ->
      solver_t -> FStar_Ident.lident -> env
  =
  fun type_of  ->
    fun universe_of  ->
      fun solver  ->
        fun module_lid  ->
          let uu____989 = new_gamma_cache () in
          let uu____991 = new_sigtab () in
          {
            solver;
            range = FStar_Range.dummyRange;
            curmodule = module_lid;
            gamma = [];
            gamma_cache = uu____989;
            modules = [];
            expected_typ = FStar_Pervasives_Native.None;
            sigtab = uu____991;
            is_pattern = false;
            instantiate_imp = true;
            effects = { decls = []; order = []; joins = [] };
            generalize = true;
            letrecs = [];
            top_level = false;
            check_uvars = false;
            use_eq = false;
            is_iface = false;
            admit = false;
            lax = false;
            lax_universes = false;
            type_of;
            universe_of;
            use_bv_sorts = false;
            qname_and_index = FStar_Pervasives_Native.None
          }
let sigtab: env -> FStar_Syntax_Syntax.sigelt FStar_Util.smap =
  fun env  -> env.sigtab
let gamma_cache: env -> cached_elt FStar_Util.smap =
  fun env  -> env.gamma_cache
let query_indices:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
    Prims.list FStar_ST.ref
  = FStar_Util.mk_ref [[]]
let push_query_indices: Prims.unit -> Prims.unit =
  fun uu____1034  ->
    let uu____1035 = FStar_ST.read query_indices in
    match uu____1035 with
    | [] -> failwith "Empty query indices!"
    | uu____1049 ->
        let uu____1054 =
          let uu____1059 =
            let uu____1063 = FStar_ST.read query_indices in
            FStar_List.hd uu____1063 in
          let uu____1077 = FStar_ST.read query_indices in uu____1059 ::
            uu____1077 in
        FStar_ST.write query_indices uu____1054
let pop_query_indices: Prims.unit -> Prims.unit =
  fun uu____1099  ->
    let uu____1100 = FStar_ST.read query_indices in
    match uu____1100 with
    | [] -> failwith "Empty query indices!"
    | hd1::tl1 -> FStar_ST.write query_indices tl1
let add_query_index:
  (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____1136  ->
    match uu____1136 with
    | (l,n1) ->
        let uu____1141 = FStar_ST.read query_indices in
        (match uu____1141 with
         | hd1::tl1 -> FStar_ST.write query_indices (((l, n1) :: hd1) :: tl1)
         | uu____1175 -> failwith "Empty query indices")
let peek_query_indices:
  Prims.unit ->
    (FStar_Ident.lident,Prims.int) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1185  ->
    let uu____1186 = FStar_ST.read query_indices in FStar_List.hd uu____1186
let commit_query_index_mark: Prims.unit -> Prims.unit =
  fun uu____1202  ->
    let uu____1203 = FStar_ST.read query_indices in
    match uu____1203 with
    | hd1::uu____1215::tl1 -> FStar_ST.write query_indices (hd1 :: tl1)
    | uu____1242 -> failwith "Unmarked query index stack"
let stack: env Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let push_stack: env -> env =
  fun env  ->
    (let uu____1256 =
       let uu____1258 = FStar_ST.read stack in env :: uu____1258 in
     FStar_ST.write stack uu____1256);
    (let uu___111_1266 = env in
     let uu____1267 = FStar_Util.smap_copy (gamma_cache env) in
     let uu____1269 = FStar_Util.smap_copy (sigtab env) in
     {
       solver = (uu___111_1266.solver);
       range = (uu___111_1266.range);
       curmodule = (uu___111_1266.curmodule);
       gamma = (uu___111_1266.gamma);
       gamma_cache = uu____1267;
       modules = (uu___111_1266.modules);
       expected_typ = (uu___111_1266.expected_typ);
       sigtab = uu____1269;
       is_pattern = (uu___111_1266.is_pattern);
       instantiate_imp = (uu___111_1266.instantiate_imp);
       effects = (uu___111_1266.effects);
       generalize = (uu___111_1266.generalize);
       letrecs = (uu___111_1266.letrecs);
       top_level = (uu___111_1266.top_level);
       check_uvars = (uu___111_1266.check_uvars);
       use_eq = (uu___111_1266.use_eq);
       is_iface = (uu___111_1266.is_iface);
       admit = (uu___111_1266.admit);
       lax = (uu___111_1266.lax);
       lax_universes = (uu___111_1266.lax_universes);
       type_of = (uu___111_1266.type_of);
       universe_of = (uu___111_1266.universe_of);
       use_bv_sorts = (uu___111_1266.use_bv_sorts);
       qname_and_index = (uu___111_1266.qname_and_index)
     })
let pop_stack: Prims.unit -> env =
  fun uu____1273  ->
    let uu____1274 = FStar_ST.read stack in
    match uu____1274 with
    | env::tl1 -> (FStar_ST.write stack tl1; env)
    | uu____1286 -> failwith "Impossible: Too many pops"
let cleanup_interactive: env -> Prims.unit = fun env  -> (env.solver).pop ""
let push: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> push_query_indices (); (env.solver).push msg; push_stack env
let pop: env -> Prims.string -> env =
  fun env  ->
    fun msg  -> (env.solver).pop msg; pop_query_indices (); pop_stack ()
let mark: env -> env =
  fun env  ->
    (env.solver).mark "USER MARK"; push_query_indices (); push_stack env
let commit_mark: env -> env =
  fun env  ->
    commit_query_index_mark ();
    (env.solver).commit_mark "USER MARK";
    (let uu____1318 = pop_stack () in ());
    env
let reset_mark: env -> env =
  fun env  ->
    (env.solver).reset_mark "USER MARK"; pop_query_indices (); pop_stack ()
let incr_query_index: env -> env =
  fun env  ->
    let qix = peek_query_indices () in
    match env.qname_and_index with
    | FStar_Pervasives_Native.None  -> env
    | FStar_Pervasives_Native.Some (l,n1) ->
        let uu____1337 =
          FStar_All.pipe_right qix
            (FStar_List.tryFind
               (fun uu____1349  ->
                  match uu____1349 with
                  | (m,uu____1353) -> FStar_Ident.lid_equals l m)) in
        (match uu____1337 with
         | FStar_Pervasives_Native.None  ->
             let next = n1 + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___112_1358 = env in
               {
                 solver = (uu___112_1358.solver);
                 range = (uu___112_1358.range);
                 curmodule = (uu___112_1358.curmodule);
                 gamma = (uu___112_1358.gamma);
                 gamma_cache = (uu___112_1358.gamma_cache);
                 modules = (uu___112_1358.modules);
                 expected_typ = (uu___112_1358.expected_typ);
                 sigtab = (uu___112_1358.sigtab);
                 is_pattern = (uu___112_1358.is_pattern);
                 instantiate_imp = (uu___112_1358.instantiate_imp);
                 effects = (uu___112_1358.effects);
                 generalize = (uu___112_1358.generalize);
                 letrecs = (uu___112_1358.letrecs);
                 top_level = (uu___112_1358.top_level);
                 check_uvars = (uu___112_1358.check_uvars);
                 use_eq = (uu___112_1358.use_eq);
                 is_iface = (uu___112_1358.is_iface);
                 admit = (uu___112_1358.admit);
                 lax = (uu___112_1358.lax);
                 lax_universes = (uu___112_1358.lax_universes);
                 type_of = (uu___112_1358.type_of);
                 universe_of = (uu___112_1358.universe_of);
                 use_bv_sorts = (uu___112_1358.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next))
               }))
         | FStar_Pervasives_Native.Some (uu____1361,m) ->
             let next = m + (Prims.parse_int "1") in
             (add_query_index (l, next);
              (let uu___113_1367 = env in
               {
                 solver = (uu___113_1367.solver);
                 range = (uu___113_1367.range);
                 curmodule = (uu___113_1367.curmodule);
                 gamma = (uu___113_1367.gamma);
                 gamma_cache = (uu___113_1367.gamma_cache);
                 modules = (uu___113_1367.modules);
                 expected_typ = (uu___113_1367.expected_typ);
                 sigtab = (uu___113_1367.sigtab);
                 is_pattern = (uu___113_1367.is_pattern);
                 instantiate_imp = (uu___113_1367.instantiate_imp);
                 effects = (uu___113_1367.effects);
                 generalize = (uu___113_1367.generalize);
                 letrecs = (uu___113_1367.letrecs);
                 top_level = (uu___113_1367.top_level);
                 check_uvars = (uu___113_1367.check_uvars);
                 use_eq = (uu___113_1367.use_eq);
                 is_iface = (uu___113_1367.is_iface);
                 admit = (uu___113_1367.admit);
                 lax = (uu___113_1367.lax);
                 lax_universes = (uu___113_1367.lax_universes);
                 type_of = (uu___113_1367.type_of);
                 universe_of = (uu___113_1367.universe_of);
                 use_bv_sorts = (uu___113_1367.use_bv_sorts);
                 qname_and_index = (FStar_Pervasives_Native.Some (l, next))
               })))
let debug: env -> FStar_Options.debug_level_t -> Prims.bool =
  fun env  ->
    fun l  -> FStar_Options.debug_at_level (env.curmodule).FStar_Ident.str l
let set_range: env -> FStar_Range.range -> env =
  fun e  ->
    fun r  ->
      if r = FStar_Range.dummyRange
      then e
      else
        (let uu___114_1383 = e in
         {
           solver = (uu___114_1383.solver);
           range = r;
           curmodule = (uu___114_1383.curmodule);
           gamma = (uu___114_1383.gamma);
           gamma_cache = (uu___114_1383.gamma_cache);
           modules = (uu___114_1383.modules);
           expected_typ = (uu___114_1383.expected_typ);
           sigtab = (uu___114_1383.sigtab);
           is_pattern = (uu___114_1383.is_pattern);
           instantiate_imp = (uu___114_1383.instantiate_imp);
           effects = (uu___114_1383.effects);
           generalize = (uu___114_1383.generalize);
           letrecs = (uu___114_1383.letrecs);
           top_level = (uu___114_1383.top_level);
           check_uvars = (uu___114_1383.check_uvars);
           use_eq = (uu___114_1383.use_eq);
           is_iface = (uu___114_1383.is_iface);
           admit = (uu___114_1383.admit);
           lax = (uu___114_1383.lax);
           lax_universes = (uu___114_1383.lax_universes);
           type_of = (uu___114_1383.type_of);
           universe_of = (uu___114_1383.universe_of);
           use_bv_sorts = (uu___114_1383.use_bv_sorts);
           qname_and_index = (uu___114_1383.qname_and_index)
         })
let get_range: env -> FStar_Range.range = fun e  -> e.range
let modules: env -> FStar_Syntax_Syntax.modul Prims.list =
  fun env  -> env.modules
let current_module: env -> FStar_Ident.lident = fun env  -> env.curmodule
let set_current_module: env -> FStar_Ident.lident -> env =
  fun env  ->
    fun lid  ->
      let uu___115_1400 = env in
      {
        solver = (uu___115_1400.solver);
        range = (uu___115_1400.range);
        curmodule = lid;
        gamma = (uu___115_1400.gamma);
        gamma_cache = (uu___115_1400.gamma_cache);
        modules = (uu___115_1400.modules);
        expected_typ = (uu___115_1400.expected_typ);
        sigtab = (uu___115_1400.sigtab);
        is_pattern = (uu___115_1400.is_pattern);
        instantiate_imp = (uu___115_1400.instantiate_imp);
        effects = (uu___115_1400.effects);
        generalize = (uu___115_1400.generalize);
        letrecs = (uu___115_1400.letrecs);
        top_level = (uu___115_1400.top_level);
        check_uvars = (uu___115_1400.check_uvars);
        use_eq = (uu___115_1400.use_eq);
        is_iface = (uu___115_1400.is_iface);
        admit = (uu___115_1400.admit);
        lax = (uu___115_1400.lax);
        lax_universes = (uu___115_1400.lax_universes);
        type_of = (uu___115_1400.type_of);
        universe_of = (uu___115_1400.universe_of);
        use_bv_sorts = (uu___115_1400.use_bv_sorts);
        qname_and_index = (uu___115_1400.qname_and_index)
      }
let has_interface: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right env.modules
        (FStar_Util.for_some
           (fun m  ->
              m.FStar_Syntax_Syntax.is_interface &&
                (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l)))
let find_in_sigtab:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)
let name_not_found: FStar_Ident.lid -> Prims.string =
  fun l  -> FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str
let variable_not_found: FStar_Syntax_Syntax.bv -> Prims.string =
  fun v1  ->
    let uu____1422 = FStar_Syntax_Print.bv_to_string v1 in
    FStar_Util.format1 "Variable \"%s\" not found" uu____1422
let new_u_univ: Prims.unit -> FStar_Syntax_Syntax.universe =
  fun uu____1425  ->
    let uu____1426 = FStar_Unionfind.fresh FStar_Pervasives_Native.None in
    FStar_Syntax_Syntax.U_unif uu____1426
let inst_tscheme_with:
  FStar_Syntax_Syntax.tscheme ->
    FStar_Syntax_Syntax.universes ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun ts  ->
    fun us  ->
      match (ts, us) with
      | (([],t),[]) -> ([], t)
      | ((formals,t),uu____1449) ->
          let n1 = (FStar_List.length formals) - (Prims.parse_int "1") in
          let vs =
            FStar_All.pipe_right us
              (FStar_List.mapi
                 (fun i  -> fun u  -> FStar_Syntax_Syntax.UN ((n1 - i), u))) in
          let uu____1465 = FStar_Syntax_Subst.subst vs t in (us, uu____1465)
let inst_tscheme:
  FStar_Syntax_Syntax.tscheme ->
    (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___99_1470  ->
    match uu___99_1470 with
    | ([],t) -> ([], t)
    | (us,t) ->
        let us' =
          FStar_All.pipe_right us
            (FStar_List.map (fun uu____1484  -> new_u_univ ())) in
        inst_tscheme_with (us, t) us'
let inst_tscheme_with_range:
  FStar_Range.range ->
    FStar_Syntax_Syntax.tscheme ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun t  ->
      let uu____1494 = inst_tscheme t in
      match uu____1494 with
      | (us,t1) ->
          let uu____1501 = FStar_Syntax_Subst.set_use_range r t1 in
          (us, uu____1501)
let inst_effect_fun_with:
  FStar_Syntax_Syntax.universes ->
    env ->
      FStar_Syntax_Syntax.eff_decl ->
        FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.term
  =
  fun insts  ->
    fun env  ->
      fun ed  ->
        fun uu____1513  ->
          match uu____1513 with
          | (us,t) ->
              (match ed.FStar_Syntax_Syntax.binders with
               | [] ->
                   let univs1 =
                     FStar_List.append ed.FStar_Syntax_Syntax.univs us in
                   (if
                      (FStar_List.length insts) <> (FStar_List.length univs1)
                    then
                      (let uu____1527 =
                         let uu____1528 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length univs1) in
                         let uu____1531 =
                           FStar_All.pipe_left FStar_Util.string_of_int
                             (FStar_List.length insts) in
                         let uu____1534 =
                           FStar_Syntax_Print.lid_to_string
                             ed.FStar_Syntax_Syntax.mname in
                         let uu____1535 = FStar_Syntax_Print.term_to_string t in
                         FStar_Util.format4
                           "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n"
                           uu____1528 uu____1531 uu____1534 uu____1535 in
                       failwith uu____1527)
                    else ();
                    (let uu____1537 =
                       inst_tscheme_with
                         ((FStar_List.append ed.FStar_Syntax_Syntax.univs us),
                           t) insts in
                     FStar_Pervasives_Native.snd uu____1537))
               | uu____1541 ->
                   let uu____1542 =
                     let uu____1543 =
                       FStar_Syntax_Print.lid_to_string
                         ed.FStar_Syntax_Syntax.mname in
                     FStar_Util.format1
                       "Unexpected use of an uninstantiated effect: %s\n"
                       uu____1543 in
                   failwith uu____1542)
type tri =
  | Yes
  | No
  | Maybe
let uu___is_Yes: tri -> Prims.bool =
  fun projectee  -> match projectee with | Yes  -> true | uu____1547 -> false
let uu___is_No: tri -> Prims.bool =
  fun projectee  -> match projectee with | No  -> true | uu____1551 -> false
let uu___is_Maybe: tri -> Prims.bool =
  fun projectee  ->
    match projectee with | Maybe  -> true | uu____1555 -> false
let in_cur_mod: env -> FStar_Ident.lident -> tri =
  fun env  ->
    fun l  ->
      let cur = current_module env in
      if l.FStar_Ident.nsstr = cur.FStar_Ident.str
      then Yes
      else
        if FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str
        then
          (let lns = FStar_List.append l.FStar_Ident.ns [l.FStar_Ident.ident] in
           let cur1 =
             FStar_List.append cur.FStar_Ident.ns [cur.FStar_Ident.ident] in
           let rec aux c l1 =
             match (c, l1) with
             | ([],uu____1581) -> Maybe
             | (uu____1585,[]) -> No
             | (hd1::tl1,hd'::tl') when
                 hd1.FStar_Ident.idText = hd'.FStar_Ident.idText ->
                 aux tl1 tl'
             | uu____1597 -> No in
           aux cur1 lns)
        else No
let lookup_qname:
  env ->
    FStar_Ident.lident ->
      (((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2,(FStar_Syntax_Syntax.sigelt,
                                           FStar_Syntax_Syntax.universes
                                             FStar_Pervasives_Native.option)
                                           FStar_Pervasives_Native.tuple2)
         FStar_Util.either,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let cur_mod = in_cur_mod env lid in
      let cache t =
        FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t;
        FStar_Pervasives_Native.Some t in
      let found =
        if cur_mod <> No
        then
          let uu____1657 =
            FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str in
          match uu____1657 with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.find_map env.gamma
                (fun uu___100_1678  ->
                   match uu___100_1678 with
                   | Binding_lid (l,t) ->
                       if FStar_Ident.lid_equals lid l
                       then
                         let uu____1701 =
                           let uu____1711 =
                             let uu____1719 = inst_tscheme t in
                             FStar_Util.Inl uu____1719 in
                           (uu____1711, (FStar_Ident.range_of_lid l)) in
                         FStar_Pervasives_Native.Some uu____1701
                       else FStar_Pervasives_Native.None
                   | Binding_sig
                       (uu____1753,{
                                     FStar_Syntax_Syntax.sigel =
                                       FStar_Syntax_Syntax.Sig_bundle
                                       (ses,uu____1755);
                                     FStar_Syntax_Syntax.sigrng = uu____1756;
                                     FStar_Syntax_Syntax.sigquals =
                                       uu____1757;
                                     FStar_Syntax_Syntax.sigmeta = uu____1758;_})
                       ->
                       FStar_Util.find_map ses
                         (fun se  ->
                            let uu____1767 =
                              FStar_All.pipe_right
                                (FStar_Syntax_Util.lids_of_sigelt se)
                                (FStar_Util.for_some
                                   (FStar_Ident.lid_equals lid)) in
                            if uu____1767
                            then
                              cache
                                ((FStar_Util.Inr
                                    (se, FStar_Pervasives_Native.None)),
                                  (FStar_Syntax_Util.range_of_sigelt se))
                            else FStar_Pervasives_Native.None)
                   | Binding_sig (lids,s) ->
                       let maybe_cache t =
                         match s.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_declare_typ uu____1794 ->
                             FStar_Pervasives_Native.Some t
                         | uu____1798 -> cache t in
                       let uu____1799 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1799 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            maybe_cache
                              ((FStar_Util.Inr
                                  (s, FStar_Pervasives_Native.None)),
                                (FStar_Ident.range_of_lid l)))
                   | Binding_sig_inst (lids,s,us) ->
                       let uu____1839 =
                         FStar_List.tryFind (FStar_Ident.lid_equals lid) lids in
                       (match uu____1839 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Pervasives_Native.None
                        | FStar_Pervasives_Native.Some l ->
                            FStar_Pervasives_Native.Some
                              ((FStar_Util.Inr
                                  (s, (FStar_Pervasives_Native.Some us))),
                                (FStar_Ident.range_of_lid l)))
                   | uu____1883 -> FStar_Pervasives_Native.None)
          | se -> se
        else FStar_Pervasives_Native.None in
      if FStar_Util.is_some found
      then found
      else
        (let uu____1925 =
           (cur_mod <> Yes) || (has_interface env env.curmodule) in
         if uu____1925
         then
           let uu____1936 = find_in_sigtab env lid in
           match uu____1936 with
           | FStar_Pervasives_Native.Some se ->
               FStar_Pervasives_Native.Some
                 ((FStar_Util.Inr (se, FStar_Pervasives_Native.None)),
                   (FStar_Syntax_Util.range_of_sigelt se))
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         else FStar_Pervasives_Native.None)
let rec add_sigelt: env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2002) ->
          add_sigelts env ses
      | uu____2007 ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          (FStar_List.iter
             (fun l  -> FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)
             lids;
           (match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ne ->
                FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                  (FStar_List.iter
                     (fun a  ->
                        let se_let =
                          FStar_Syntax_Util.action_as_lb
                            ne.FStar_Syntax_Syntax.mname a in
                        FStar_Util.smap_add (sigtab env)
                          (a.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                          se_let))
            | uu____2016 -> ()))
and add_sigelts: env -> FStar_Syntax_Syntax.sigelt Prims.list -> Prims.unit =
  fun env  ->
    fun ses  -> FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))
let try_lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
         FStar_Syntax_Syntax.syntax,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun bv  ->
      FStar_Util.find_map env.gamma
        (fun uu___101_2034  ->
           match uu___101_2034 with
           | Binding_var id when FStar_Syntax_Syntax.bv_eq id bv ->
               FStar_Pervasives_Native.Some
                 ((id.FStar_Syntax_Syntax.sort),
                   ((id.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange))
           | uu____2047 -> FStar_Pervasives_Native.None)
let lookup_type_of_let:
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    fun lid  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          ((uu____2068,lb::[]),uu____2070,uu____2071) ->
          let uu____2080 =
            let uu____2085 =
              inst_tscheme
                ((lb.FStar_Syntax_Syntax.lbunivs),
                  (lb.FStar_Syntax_Syntax.lbtyp)) in
            let uu____2091 =
              FStar_Syntax_Syntax.range_of_lbname
                lb.FStar_Syntax_Syntax.lbname in
            (uu____2085, uu____2091) in
          FStar_Pervasives_Native.Some uu____2080
      | FStar_Syntax_Syntax.Sig_let ((uu____2098,lbs),uu____2100,uu____2101)
          ->
          FStar_Util.find_map lbs
            (fun lb  ->
               match lb.FStar_Syntax_Syntax.lbname with
               | FStar_Util.Inl uu____2121 -> failwith "impossible"
               | FStar_Util.Inr fv ->
                   let uu____2128 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                   if uu____2128
                   then
                     let uu____2134 =
                       let uu____2139 =
                         inst_tscheme
                           ((lb.FStar_Syntax_Syntax.lbunivs),
                             (lb.FStar_Syntax_Syntax.lbtyp)) in
                       let uu____2145 = FStar_Syntax_Syntax.range_of_fv fv in
                       (uu____2139, uu____2145) in
                     FStar_Pervasives_Native.Some uu____2134
                   else FStar_Pervasives_Native.None)
      | uu____2157 -> FStar_Pervasives_Native.None
let effect_signature:
  FStar_Syntax_Syntax.sigelt ->
    ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.term)
       FStar_Pervasives_Native.tuple2,FStar_Range.range)
      FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne ->
        let uu____2176 =
          let uu____2181 =
            let uu____2184 =
              let uu____2185 =
                let uu____2188 =
                  FStar_Syntax_Syntax.mk_Total
                    ne.FStar_Syntax_Syntax.signature in
                FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders
                  uu____2188 in
              ((ne.FStar_Syntax_Syntax.univs), uu____2185) in
            inst_tscheme uu____2184 in
          (uu____2181, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____2176
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,us,binders,uu____2202,uu____2203) ->
        let uu____2206 =
          let uu____2211 =
            let uu____2214 =
              let uu____2215 =
                let uu____2218 =
                  FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff in
                FStar_Syntax_Util.arrow binders uu____2218 in
              (us, uu____2215) in
            inst_tscheme uu____2214 in
          (uu____2211, (se.FStar_Syntax_Syntax.sigrng)) in
        FStar_Pervasives_Native.Some uu____2206
    | uu____2229 -> FStar_Pervasives_Native.None
let try_lookup_lid_aux:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                        FStar_Syntax_Syntax.syntax)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let mapper uu____2264 =
        match uu____2264 with
        | (lr,rng) ->
            (match lr with
             | FStar_Util.Inl t -> FStar_Pervasives_Native.Some (t, rng)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_datacon
                      (uu____2314,uvs,t,uu____2317,uu____2318,uu____2319);
                    FStar_Syntax_Syntax.sigrng = uu____2320;
                    FStar_Syntax_Syntax.sigquals = uu____2321;
                    FStar_Syntax_Syntax.sigmeta = uu____2322;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____2332 =
                   let uu____2337 = inst_tscheme (uvs, t) in
                   (uu____2337, rng) in
                 FStar_Pervasives_Native.Some uu____2332
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_declare_typ (l,uvs,t);
                    FStar_Syntax_Syntax.sigrng = uu____2349;
                    FStar_Syntax_Syntax.sigquals = qs;
                    FStar_Syntax_Syntax.sigmeta = uu____2351;_},FStar_Pervasives_Native.None
                  )
                 ->
                 let uu____2359 =
                   let uu____2360 = in_cur_mod env l in uu____2360 = Yes in
                 if uu____2359
                 then
                   let uu____2366 =
                     (FStar_All.pipe_right qs
                        (FStar_List.contains FStar_Syntax_Syntax.Assumption))
                       || env.is_iface in
                   (if uu____2366
                    then
                      let uu____2373 =
                        let uu____2378 = inst_tscheme (uvs, t) in
                        (uu____2378, rng) in
                      FStar_Pervasives_Native.Some uu____2373
                    else FStar_Pervasives_Native.None)
                 else
                   (let uu____2393 =
                      let uu____2398 = inst_tscheme (uvs, t) in
                      (uu____2398, rng) in
                    FStar_Pervasives_Native.Some uu____2393)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2411,uu____2412);
                    FStar_Syntax_Syntax.sigrng = uu____2413;
                    FStar_Syntax_Syntax.sigquals = uu____2414;
                    FStar_Syntax_Syntax.sigmeta = uu____2415;_},FStar_Pervasives_Native.None
                  )
                 ->
                 (match tps with
                  | [] ->
                      let uu____2434 =
                        let uu____2439 = inst_tscheme (uvs, k) in
                        (uu____2439, rng) in
                      FStar_Pervasives_Native.Some uu____2434
                  | uu____2448 ->
                      let uu____2449 =
                        let uu____2454 =
                          let uu____2457 =
                            let uu____2458 =
                              let uu____2461 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2461 in
                            (uvs, uu____2458) in
                          inst_tscheme uu____2457 in
                        (uu____2454, rng) in
                      FStar_Pervasives_Native.Some uu____2449)
             | FStar_Util.Inr
                 ({
                    FStar_Syntax_Syntax.sigel =
                      FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid1,uvs,tps,k,uu____2476,uu____2477);
                    FStar_Syntax_Syntax.sigrng = uu____2478;
                    FStar_Syntax_Syntax.sigquals = uu____2479;
                    FStar_Syntax_Syntax.sigmeta = uu____2480;_},FStar_Pervasives_Native.Some
                  us)
                 ->
                 (match tps with
                  | [] ->
                      let uu____2500 =
                        let uu____2505 = inst_tscheme_with (uvs, k) us in
                        (uu____2505, rng) in
                      FStar_Pervasives_Native.Some uu____2500
                  | uu____2514 ->
                      let uu____2515 =
                        let uu____2520 =
                          let uu____2523 =
                            let uu____2524 =
                              let uu____2527 = FStar_Syntax_Syntax.mk_Total k in
                              FStar_Syntax_Util.flat_arrow tps uu____2527 in
                            (uvs, uu____2524) in
                          inst_tscheme_with uu____2523 us in
                        (uu____2520, rng) in
                      FStar_Pervasives_Native.Some uu____2515)
             | FStar_Util.Inr se ->
                 let uu____2547 =
                   match se with
                   | ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let uu____2558;
                        FStar_Syntax_Syntax.sigrng = uu____2559;
                        FStar_Syntax_Syntax.sigquals = uu____2560;
                        FStar_Syntax_Syntax.sigmeta = uu____2561;_},FStar_Pervasives_Native.None
                      ) ->
                       lookup_type_of_let (FStar_Pervasives_Native.fst se)
                         lid
                   | uu____2570 ->
                       effect_signature (FStar_Pervasives_Native.fst se) in
                 FStar_All.pipe_right uu____2547
                   (FStar_Util.map_option
                      (fun uu____2593  ->
                         match uu____2593 with | (us_t,rng1) -> (us_t, rng1)))) in
      let uu____2610 =
        let uu____2616 = lookup_qname env lid in
        FStar_Util.bind_opt uu____2616 mapper in
      match uu____2610 with
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          FStar_Pervasives_Native.Some
            ((us,
               (let uu___116_2668 = t in
                {
                  FStar_Syntax_Syntax.n =
                    (uu___116_2668.FStar_Syntax_Syntax.n);
                  FStar_Syntax_Syntax.tk =
                    (uu___116_2668.FStar_Syntax_Syntax.tk);
                  FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid);
                  FStar_Syntax_Syntax.vars =
                    (uu___116_2668.FStar_Syntax_Syntax.vars)
                })), r)
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
let lid_exists: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____2689 = lookup_qname env l in
      match uu____2689 with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some uu____2709 -> true
let lookup_bv:
  env ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.typ,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bv  ->
      let bvr = FStar_Syntax_Syntax.range_of_bv bv in
      let uu____2737 = try_lookup_bv env bv in
      match uu____2737 with
      | FStar_Pervasives_Native.None  ->
          let uu____2745 =
            let uu____2746 =
              let uu____2749 = variable_not_found bv in (uu____2749, bvr) in
            FStar_Errors.Error uu____2746 in
          raise uu____2745
      | FStar_Pervasives_Native.Some (t,r) ->
          let uu____2756 = FStar_Syntax_Subst.set_use_range bvr t in
          let uu____2757 = FStar_Range.set_use_range r bvr in
          (uu____2756, uu____2757)
let try_lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2769 = try_lookup_lid_aux env l in
      match uu____2769 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ((us,t),r) ->
          let use_range = FStar_Ident.range_of_lid l in
          let r1 = FStar_Range.set_use_range r use_range in
          let uu____2811 =
            let uu____2816 =
              let uu____2819 = FStar_Syntax_Subst.set_use_range use_range t in
              (us, uu____2819) in
            (uu____2816, r1) in
          FStar_Pervasives_Native.Some uu____2811
let lookup_lid:
  env ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
         FStar_Pervasives_Native.tuple2,FStar_Range.range)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun l  ->
      let uu____2836 = try_lookup_lid env l in
      match uu____2836 with
      | FStar_Pervasives_Native.None  ->
          let uu____2850 =
            let uu____2851 =
              let uu____2854 = name_not_found l in
              (uu____2854, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____2851 in
          raise uu____2850
      | FStar_Pervasives_Native.Some v1 -> v1
let lookup_univ: env -> FStar_Syntax_Syntax.univ_name -> Prims.bool =
  fun env  ->
    fun x  ->
      FStar_All.pipe_right
        (FStar_List.find
           (fun uu___102_2875  ->
              match uu___102_2875 with
              | Binding_univ y -> x.FStar_Ident.idText = y.FStar_Ident.idText
              | uu____2877 -> false) env.gamma) FStar_Option.isSome
let try_lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.tscheme,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun lid  ->
      let uu____2888 = lookup_qname env lid in
      match uu____2888 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2903,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2906;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____2908;_},FStar_Pervasives_Native.None
            ),uu____2909)
          ->
          let uu____2933 =
            let uu____2939 =
              let uu____2942 =
                FStar_Syntax_Subst.set_use_range
                  (FStar_Ident.range_of_lid lid) t in
              (uvs, uu____2942) in
            (uu____2939, q) in
          FStar_Pervasives_Native.Some uu____2933
      | uu____2951 -> FStar_Pervasives_Native.None
let lookup_val_decl:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____2973 = lookup_qname env lid in
      match uu____2973 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____2986,uvs,t);
              FStar_Syntax_Syntax.sigrng = uu____2989;
              FStar_Syntax_Syntax.sigquals = uu____2990;
              FStar_Syntax_Syntax.sigmeta = uu____2991;_},FStar_Pervasives_Native.None
            ),uu____2992)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3016 ->
          let uu____3027 =
            let uu____3028 =
              let uu____3031 = name_not_found lid in
              (uu____3031, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3028 in
          raise uu____3027
let lookup_datacon:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.universes,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____3042 = lookup_qname env lid in
      match uu____3042 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3055,uvs,t,uu____3058,uu____3059,uu____3060);
              FStar_Syntax_Syntax.sigrng = uu____3061;
              FStar_Syntax_Syntax.sigquals = uu____3062;
              FStar_Syntax_Syntax.sigmeta = uu____3063;_},FStar_Pervasives_Native.None
            ),uu____3064)
          -> inst_tscheme_with_range (FStar_Ident.range_of_lid lid) (uvs, t)
      | uu____3090 ->
          let uu____3101 =
            let uu____3102 =
              let uu____3105 = name_not_found lid in
              (uu____3105, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____3102 in
          raise uu____3101
let datacons_of_typ:
  env ->
    FStar_Ident.lident ->
      (Prims.bool,FStar_Ident.lident Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      let uu____3117 = lookup_qname env lid in
      match uu____3117 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3131,uu____3132,uu____3133,uu____3134,uu____3135,dcs);
              FStar_Syntax_Syntax.sigrng = uu____3137;
              FStar_Syntax_Syntax.sigquals = uu____3138;
              FStar_Syntax_Syntax.sigmeta = uu____3139;_},uu____3140),uu____3141)
          -> (true, dcs)
      | uu____3171 -> (false, [])
let typ_of_datacon: env -> FStar_Ident.lident -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      let uu____3189 = lookup_qname env lid in
      match uu____3189 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3200,uu____3201,uu____3202,l,uu____3204,uu____3205);
              FStar_Syntax_Syntax.sigrng = uu____3206;
              FStar_Syntax_Syntax.sigquals = uu____3207;
              FStar_Syntax_Syntax.sigmeta = uu____3208;_},uu____3209),uu____3210)
          -> l
      | uu____3237 ->
          let uu____3248 =
            let uu____3249 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format1 "Not a datacon: %s" uu____3249 in
          failwith uu____3248
let lookup_definition:
  delta_level Prims.list ->
    env ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun delta_levels  ->
    fun env  ->
      fun lid  ->
        let visible quals =
          FStar_All.pipe_right delta_levels
            (FStar_Util.for_some
               (fun dl  ->
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some (visible_at dl)))) in
        let uu____3273 = lookup_qname env lid in
        match uu____3273 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____3288) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_let
                 ((uu____3314,lbs),uu____3316,uu____3317) when
                 visible se.FStar_Syntax_Syntax.sigquals ->
                 FStar_Util.find_map lbs
                   (fun lb  ->
                      let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                      let uu____3334 = FStar_Syntax_Syntax.fv_eq_lid fv lid in
                      if uu____3334
                      then
                        FStar_Pervasives_Native.Some
                          ((lb.FStar_Syntax_Syntax.lbunivs),
                            (lb.FStar_Syntax_Syntax.lbdef))
                      else FStar_Pervasives_Native.None)
             | uu____3355 -> FStar_Pervasives_Native.None)
        | uu____3358 -> FStar_Pervasives_Native.None
let try_lookup_effect_lid:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ftv  ->
      let uu____3379 = lookup_qname env ftv in
      match uu____3379 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr (se,FStar_Pervasives_Native.None ),uu____3392) ->
          let uu____3415 = effect_signature se in
          (match uu____3415 with
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some ((uu____3426,t),r) ->
               let uu____3435 =
                 FStar_Syntax_Subst.set_use_range
                   (FStar_Ident.range_of_lid ftv) t in
               FStar_Pervasives_Native.Some uu____3435)
      | uu____3436 -> FStar_Pervasives_Native.None
let lookup_effect_lid: env -> FStar_Ident.lident -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun ftv  ->
      let uu____3453 = try_lookup_effect_lid env ftv in
      match uu____3453 with
      | FStar_Pervasives_Native.None  ->
          let uu____3455 =
            let uu____3456 =
              let uu____3459 = name_not_found ftv in
              (uu____3459, (FStar_Ident.range_of_lid ftv)) in
            FStar_Errors.Error uu____3456 in
          raise uu____3455
      | FStar_Pervasives_Native.Some k -> k
let lookup_effect_abbrev:
  env ->
    FStar_Syntax_Syntax.universes ->
      FStar_Ident.lident ->
        (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun univ_insts  ->
      fun lid0  ->
        let uu____3473 = lookup_qname env lid0 in
        match uu____3473 with
        | FStar_Pervasives_Native.Some
            (FStar_Util.Inr
             ({
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_effect_abbrev
                  (lid,univs1,binders,c,uu____3491);
                FStar_Syntax_Syntax.sigrng = uu____3492;
                FStar_Syntax_Syntax.sigquals = quals;
                FStar_Syntax_Syntax.sigmeta = uu____3494;_},FStar_Pervasives_Native.None
              ),uu____3495)
            ->
            let lid1 =
              let uu____3522 =
                FStar_Range.set_use_range (FStar_Ident.range_of_lid lid)
                  (FStar_Ident.range_of_lid lid0) in
              FStar_Ident.set_lid_range lid uu____3522 in
            let uu____3523 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___103_3525  ->
                      match uu___103_3525 with
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____3526 -> false)) in
            if uu____3523
            then FStar_Pervasives_Native.None
            else
              (let insts =
                 if
                   (FStar_List.length univ_insts) =
                     (FStar_List.length univs1)
                 then univ_insts
                 else
                   (let uu____3539 =
                      let uu____3540 = FStar_Syntax_Print.lid_to_string lid1 in
                      let uu____3541 =
                        FStar_All.pipe_right (FStar_List.length univ_insts)
                          FStar_Util.string_of_int in
                      FStar_Util.format2
                        "Unexpected instantiation of effect %s with %s universes"
                        uu____3540 uu____3541 in
                    failwith uu____3539) in
               match (binders, univs1) with
               | ([],uu____3547) ->
                   failwith
                     "Unexpected effect abbreviation with no arguments"
               | (uu____3556,uu____3557::uu____3558::uu____3559) ->
                   let uu____3562 =
                     let uu____3563 = FStar_Syntax_Print.lid_to_string lid1 in
                     let uu____3564 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length univs1) in
                     FStar_Util.format2
                       "Unexpected effect abbreviation %s; polymorphic in %s universes"
                       uu____3563 uu____3564 in
                   failwith uu____3562
               | uu____3570 ->
                   let uu____3573 =
                     let uu____3576 =
                       let uu____3577 = FStar_Syntax_Util.arrow binders c in
                       (univs1, uu____3577) in
                     inst_tscheme_with uu____3576 insts in
                   (match uu____3573 with
                    | (uu____3585,t) ->
                        let t1 =
                          FStar_Syntax_Subst.set_use_range
                            (FStar_Ident.range_of_lid lid1) t in
                        let uu____3588 =
                          let uu____3589 = FStar_Syntax_Subst.compress t1 in
                          uu____3589.FStar_Syntax_Syntax.n in
                        (match uu____3588 with
                         | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                             FStar_Pervasives_Native.Some (binders1, c1)
                         | uu____3619 -> failwith "Impossible")))
        | uu____3623 -> FStar_Pervasives_Native.None
let norm_eff_name: env -> FStar_Ident.lident -> FStar_Ident.lident =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun env  ->
    fun l  ->
      let rec find1 l1 =
        let uu____3649 =
          lookup_effect_abbrev env [FStar_Syntax_Syntax.U_unknown] l1 in
        match uu____3649 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (uu____3656,c) ->
            let l2 = FStar_Syntax_Util.comp_effect_name c in
            let uu____3661 = find1 l2 in
            (match uu____3661 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some l2
             | FStar_Pervasives_Native.Some l' ->
                 FStar_Pervasives_Native.Some l') in
      let res =
        let uu____3666 = FStar_Util.smap_try_find cache l.FStar_Ident.str in
        match uu____3666 with
        | FStar_Pervasives_Native.Some l1 -> l1
        | FStar_Pervasives_Native.None  ->
            let uu____3669 = find1 l in
            (match uu____3669 with
             | FStar_Pervasives_Native.None  -> l
             | FStar_Pervasives_Native.Some m ->
                 (FStar_Util.smap_add cache l.FStar_Ident.str m; m)) in
      FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l)
let lookup_effect_quals:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun env  ->
    fun l  ->
      let l1 = norm_eff_name env l in
      let uu____3681 = lookup_qname env l1 in
      match uu____3681 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect
                uu____3693;
              FStar_Syntax_Syntax.sigrng = uu____3694;
              FStar_Syntax_Syntax.sigquals = q;
              FStar_Syntax_Syntax.sigmeta = uu____3696;_},uu____3697),uu____3698)
          -> q
      | uu____3723 -> []
let lookup_projector:
  env -> FStar_Ident.lident -> Prims.int -> FStar_Ident.lident =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____3746 =
          let uu____3747 =
            let uu____3748 = FStar_Util.string_of_int i in
            let uu____3749 = FStar_Syntax_Print.lid_to_string lid in
            FStar_Util.format2
              "Impossible: projecting field #%s from constructor %s is undefined"
              uu____3748 uu____3749 in
          failwith uu____3747 in
        let uu____3750 = lookup_datacon env lid in
        match uu____3750 with
        | (uu____3753,t) ->
            let uu____3755 =
              let uu____3756 = FStar_Syntax_Subst.compress t in
              uu____3756.FStar_Syntax_Syntax.n in
            (match uu____3755 with
             | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3760) ->
                 if
                   (i < (Prims.parse_int "0")) ||
                     (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i in
                    let uu____3781 =
                      FStar_Syntax_Util.mk_field_projector_name lid
                        (FStar_Pervasives_Native.fst b) i in
                    FStar_All.pipe_right uu____3781
                      FStar_Pervasives_Native.fst)
             | uu____3786 -> fail ())
let is_projector: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun l  ->
      let uu____3793 = lookup_qname env l in
      match uu____3793 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ
                (uu____3804,uu____3805,uu____3806);
              FStar_Syntax_Syntax.sigrng = uu____3807;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3809;_},uu____3810),uu____3811)
          ->
          FStar_Util.for_some
            (fun uu___104_3836  ->
               match uu___104_3836 with
               | FStar_Syntax_Syntax.Projector uu____3837 -> true
               | uu____3840 -> false) quals
      | uu____3841 -> false
let is_datacon: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3858 = lookup_qname env lid in
      match uu____3858 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                (uu____3869,uu____3870,uu____3871,uu____3872,uu____3873,uu____3874);
              FStar_Syntax_Syntax.sigrng = uu____3875;
              FStar_Syntax_Syntax.sigquals = uu____3876;
              FStar_Syntax_Syntax.sigmeta = uu____3877;_},uu____3878),uu____3879)
          -> true
      | uu____3906 -> false
let is_record: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____3923 = lookup_qname env lid in
      match uu____3923 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____3934,uu____3935,uu____3936,uu____3937,uu____3938,uu____3939);
              FStar_Syntax_Syntax.sigrng = uu____3940;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____3942;_},uu____3943),uu____3944)
          ->
          FStar_Util.for_some
            (fun uu___105_3973  ->
               match uu___105_3973 with
               | FStar_Syntax_Syntax.RecordType uu____3974 -> true
               | FStar_Syntax_Syntax.RecordConstructor uu____3979 -> true
               | uu____3984 -> false) quals
      | uu____3985 -> false
let is_action: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let uu____4002 = lookup_qname env lid in
      match uu____4002 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                (uu____4013,uu____4014,uu____4015);
              FStar_Syntax_Syntax.sigrng = uu____4016;
              FStar_Syntax_Syntax.sigquals = quals;
              FStar_Syntax_Syntax.sigmeta = uu____4018;_},uu____4019),uu____4020)
          ->
          FStar_Util.for_some
            (fun uu___106_4049  ->
               match uu___106_4049 with
               | FStar_Syntax_Syntax.Action uu____4050 -> true
               | uu____4051 -> false) quals
      | uu____4052 -> false
let is_interpreted: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  let interpreted_symbols =
    [FStar_Parser_Const.op_Eq;
    FStar_Parser_Const.op_notEq;
    FStar_Parser_Const.op_LT;
    FStar_Parser_Const.op_LTE;
    FStar_Parser_Const.op_GT;
    FStar_Parser_Const.op_GTE;
    FStar_Parser_Const.op_Subtraction;
    FStar_Parser_Const.op_Minus;
    FStar_Parser_Const.op_Addition;
    FStar_Parser_Const.op_Multiply;
    FStar_Parser_Const.op_Division;
    FStar_Parser_Const.op_Modulus;
    FStar_Parser_Const.op_And;
    FStar_Parser_Const.op_Or;
    FStar_Parser_Const.op_Negation] in
  fun env  ->
    fun head1  ->
      let uu____4071 =
        let uu____4072 = FStar_Syntax_Util.un_uinst head1 in
        uu____4072.FStar_Syntax_Syntax.n in
      match uu____4071 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          fv.FStar_Syntax_Syntax.fv_delta =
            FStar_Syntax_Syntax.Delta_equational
      | uu____4076 -> false
let is_type_constructor: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun lid  ->
      let mapper x =
        match FStar_Pervasives_Native.fst x with
        | FStar_Util.Inl uu____4114 -> FStar_Pervasives_Native.Some false
        | FStar_Util.Inr (se,uu____4123) ->
            (match se.FStar_Syntax_Syntax.sigel with
             | FStar_Syntax_Syntax.Sig_declare_typ uu____4132 ->
                 FStar_Pervasives_Native.Some
                   (FStar_List.contains FStar_Syntax_Syntax.New
                      se.FStar_Syntax_Syntax.sigquals)
             | FStar_Syntax_Syntax.Sig_inductive_typ uu____4136 ->
                 FStar_Pervasives_Native.Some true
             | uu____4145 -> FStar_Pervasives_Native.Some false) in
      let uu____4146 =
        let uu____4148 = lookup_qname env lid in
        FStar_Util.bind_opt uu____4148 mapper in
      match uu____4146 with
      | FStar_Pervasives_Native.Some b -> b
      | FStar_Pervasives_Native.None  -> false
let num_inductive_ty_params: env -> FStar_Ident.lident -> Prims.int =
  fun env  ->
    fun lid  ->
      let uu____4175 = lookup_qname env lid in
      match uu____4175 with
      | FStar_Pervasives_Native.Some
          (FStar_Util.Inr
           ({
              FStar_Syntax_Syntax.sigel =
                FStar_Syntax_Syntax.Sig_inductive_typ
                (uu____4186,uu____4187,tps,uu____4189,uu____4190,uu____4191);
              FStar_Syntax_Syntax.sigrng = uu____4192;
              FStar_Syntax_Syntax.sigquals = uu____4193;
              FStar_Syntax_Syntax.sigmeta = uu____4194;_},uu____4195),uu____4196)
          -> FStar_List.length tps
      | uu____4228 ->
          let uu____4239 =
            let uu____4240 =
              let uu____4243 = name_not_found lid in
              (uu____4243, (FStar_Ident.range_of_lid lid)) in
            FStar_Errors.Error uu____4240 in
          raise uu____4239
let effect_decl_opt:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.qualifier Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      FStar_All.pipe_right (env.effects).decls
        (FStar_Util.find_opt
           (fun uu____4265  ->
              match uu____4265 with
              | (d,uu____4270) ->
                  FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l))
let get_effect_decl:
  env -> FStar_Ident.lident -> FStar_Syntax_Syntax.eff_decl =
  fun env  ->
    fun l  ->
      let uu____4279 = effect_decl_opt env l in
      match uu____4279 with
      | FStar_Pervasives_Native.None  ->
          let uu____4287 =
            let uu____4288 =
              let uu____4291 = name_not_found l in
              (uu____4291, (FStar_Ident.range_of_lid l)) in
            FStar_Errors.Error uu____4288 in
          raise uu____4287
      | FStar_Pervasives_Native.Some md -> FStar_Pervasives_Native.fst md
let identity_mlift: mlift =
  {
    mlift_wp = (fun t  -> fun wp  -> wp);
    mlift_term =
      (FStar_Pervasives_Native.Some (fun t  -> fun wp  -> fun e  -> e))
  }
let join:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        (FStar_Ident.lident,mlift,mlift) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if FStar_Ident.lid_equals l1 l2
        then (l1, identity_mlift, identity_mlift)
        else
          if
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid)
               &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid))
              ||
              ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)
                 &&
                 (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid))
          then
            (FStar_Parser_Const.effect_GTot_lid, identity_mlift,
              identity_mlift)
          else
            (let uu____4334 =
               FStar_All.pipe_right (env.effects).joins
                 (FStar_Util.find_opt
                    (fun uu____4358  ->
                       match uu____4358 with
                       | (m1,m2,uu____4366,uu____4367,uu____4368) ->
                           (FStar_Ident.lid_equals l1 m1) &&
                             (FStar_Ident.lid_equals l2 m2))) in
             match uu____4334 with
             | FStar_Pervasives_Native.None  ->
                 let uu____4377 =
                   let uu____4378 =
                     let uu____4381 =
                       let uu____4382 = FStar_Syntax_Print.lid_to_string l1 in
                       let uu____4383 = FStar_Syntax_Print.lid_to_string l2 in
                       FStar_Util.format2
                         "Effects %s and %s cannot be composed" uu____4382
                         uu____4383 in
                     (uu____4381, (env.range)) in
                   FStar_Errors.Error uu____4378 in
                 raise uu____4377
             | FStar_Pervasives_Native.Some (uu____4387,uu____4388,m3,j1,j2)
                 -> (m3, j1, j2))
let monad_leq:
  env ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> edge FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        if
          (FStar_Ident.lid_equals l1 l2) ||
            ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) &&
               (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid))
        then
          FStar_Pervasives_Native.Some
            { msource = l1; mtarget = l2; mlift = identity_mlift }
        else
          FStar_All.pipe_right (env.effects).order
            (FStar_Util.find_opt
               (fun e  ->
                  (FStar_Ident.lid_equals l1 e.msource) &&
                    (FStar_Ident.lid_equals l2 e.mtarget)))
let wp_sig_aux decls m =
  let uu____4435 =
    FStar_All.pipe_right decls
      (FStar_Util.find_opt
         (fun uu____4447  ->
            match uu____4447 with
            | (d,uu____4451) ->
                FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)) in
  match uu____4435 with
  | FStar_Pervasives_Native.None  ->
      let uu____4458 =
        FStar_Util.format1 "Impossible: declaration for monad %s not found"
          m.FStar_Ident.str in
      failwith uu____4458
  | FStar_Pervasives_Native.Some (md,_q) ->
      let uu____4467 =
        inst_tscheme
          ((md.FStar_Syntax_Syntax.univs),
            (md.FStar_Syntax_Syntax.signature)) in
      (match uu____4467 with
       | (uu____4474,s) ->
           let s1 = FStar_Syntax_Subst.compress s in
           (match ((md.FStar_Syntax_Syntax.binders),
                    (s1.FStar_Syntax_Syntax.n))
            with
            | ([],FStar_Syntax_Syntax.Tm_arrow
               ((a,uu____4482)::(wp,uu____4484)::[],c)) when
                FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)
                -> (a, (wp.FStar_Syntax_Syntax.sort))
            | uu____4506 -> failwith "Impossible"))
let wp_signature:
  env ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.bv,(FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
                                FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple2
  = fun env  -> fun m  -> wp_sig_aux (env.effects).decls m
let null_wp_for_eff:
  env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun eff_name  ->
      fun res_u  ->
        fun res_t  ->
          if
            FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid
          then
            FStar_Syntax_Syntax.mk_Total' res_t
              (FStar_Pervasives_Native.Some res_u)
          else
            if
              FStar_Ident.lid_equals eff_name
                FStar_Parser_Const.effect_GTot_lid
            then
              FStar_Syntax_Syntax.mk_GTotal' res_t
                (FStar_Pervasives_Native.Some res_u)
            else
              (let eff_name1 = norm_eff_name env eff_name in
               let ed = get_effect_decl env eff_name1 in
               let null_wp =
                 inst_effect_fun_with [res_u] env ed
                   ed.FStar_Syntax_Syntax.null_wp in
               let null_wp_res =
                 let uu____4542 = get_range env in
                 let uu____4543 =
                   let uu____4546 =
                     let uu____4547 =
                       let uu____4557 =
                         let uu____4559 = FStar_Syntax_Syntax.as_arg res_t in
                         [uu____4559] in
                       (null_wp, uu____4557) in
                     FStar_Syntax_Syntax.Tm_app uu____4547 in
                   FStar_Syntax_Syntax.mk uu____4546 in
                 uu____4543 FStar_Pervasives_Native.None uu____4542 in
               let uu____4569 =
                 let uu____4570 =
                   let uu____4576 = FStar_Syntax_Syntax.as_arg null_wp_res in
                   [uu____4576] in
                 {
                   FStar_Syntax_Syntax.comp_univs = [res_u];
                   FStar_Syntax_Syntax.effect_name = eff_name1;
                   FStar_Syntax_Syntax.result_typ = res_t;
                   FStar_Syntax_Syntax.effect_args = uu____4570;
                   FStar_Syntax_Syntax.flags = []
                 } in
               FStar_Syntax_Syntax.mk_Comp uu____4569)
let build_lattice: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect ne ->
          let effects =
            let uu___117_4585 = env.effects in
            {
              decls = ((ne, (se.FStar_Syntax_Syntax.sigquals)) ::
                ((env.effects).decls));
              order = (uu___117_4585.order);
              joins = (uu___117_4585.joins)
            } in
          let uu___118_4590 = env in
          {
            solver = (uu___118_4590.solver);
            range = (uu___118_4590.range);
            curmodule = (uu___118_4590.curmodule);
            gamma = (uu___118_4590.gamma);
            gamma_cache = (uu___118_4590.gamma_cache);
            modules = (uu___118_4590.modules);
            expected_typ = (uu___118_4590.expected_typ);
            sigtab = (uu___118_4590.sigtab);
            is_pattern = (uu___118_4590.is_pattern);
            instantiate_imp = (uu___118_4590.instantiate_imp);
            effects;
            generalize = (uu___118_4590.generalize);
            letrecs = (uu___118_4590.letrecs);
            top_level = (uu___118_4590.top_level);
            check_uvars = (uu___118_4590.check_uvars);
            use_eq = (uu___118_4590.use_eq);
            is_iface = (uu___118_4590.is_iface);
            admit = (uu___118_4590.admit);
            lax = (uu___118_4590.lax);
            lax_universes = (uu___118_4590.lax_universes);
            type_of = (uu___118_4590.type_of);
            universe_of = (uu___118_4590.universe_of);
            use_bv_sorts = (uu___118_4590.use_bv_sorts);
            qname_and_index = (uu___118_4590.qname_and_index)
          }
      | FStar_Syntax_Syntax.Sig_sub_effect sub1 ->
          let compose_edges e1 e2 =
            let composed_lift =
              let mlift_wp r wp1 =
                let uu____4607 = (e1.mlift).mlift_wp r wp1 in
                (e2.mlift).mlift_wp r uu____4607 in
              let mlift_term =
                match (((e1.mlift).mlift_term), ((e2.mlift).mlift_term)) with
                | (FStar_Pervasives_Native.Some
                   l1,FStar_Pervasives_Native.Some l2) ->
                    FStar_Pervasives_Native.Some
                      ((fun t  ->
                          fun wp  ->
                            fun e  ->
                              let uu____4686 = (e1.mlift).mlift_wp t wp in
                              let uu____4687 = l1 t wp e in
                              l2 t uu____4686 uu____4687))
                | uu____4688 -> FStar_Pervasives_Native.None in
              { mlift_wp; mlift_term } in
            {
              msource = (e1.msource);
              mtarget = (e2.mtarget);
              mlift = composed_lift
            } in
          let mk_mlift_wp lift_t r wp1 =
            let uu____4723 = inst_tscheme lift_t in
            match uu____4723 with
            | (uu____4728,lift_t1) ->
                let uu____4730 =
                  let uu____4733 =
                    let uu____4734 =
                      let uu____4744 =
                        let uu____4746 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4747 =
                          let uu____4749 = FStar_Syntax_Syntax.as_arg wp1 in
                          [uu____4749] in
                        uu____4746 :: uu____4747 in
                      (lift_t1, uu____4744) in
                    FStar_Syntax_Syntax.Tm_app uu____4734 in
                  FStar_Syntax_Syntax.mk uu____4733 in
                uu____4730 FStar_Pervasives_Native.None
                  wp1.FStar_Syntax_Syntax.pos in
          let sub_mlift_wp =
            match sub1.FStar_Syntax_Syntax.lift_wp with
            | FStar_Pervasives_Native.Some sub_lift_wp ->
                mk_mlift_wp sub_lift_wp
            | FStar_Pervasives_Native.None  ->
                failwith "sub effect should've been elaborated at this stage" in
          let mk_mlift_term lift_t r wp1 e =
            let uu____4794 = inst_tscheme lift_t in
            match uu____4794 with
            | (uu____4799,lift_t1) ->
                let uu____4801 =
                  let uu____4804 =
                    let uu____4805 =
                      let uu____4815 =
                        let uu____4817 = FStar_Syntax_Syntax.as_arg r in
                        let uu____4818 =
                          let uu____4820 = FStar_Syntax_Syntax.as_arg wp1 in
                          let uu____4821 =
                            let uu____4823 = FStar_Syntax_Syntax.as_arg e in
                            [uu____4823] in
                          uu____4820 :: uu____4821 in
                        uu____4817 :: uu____4818 in
                      (lift_t1, uu____4815) in
                    FStar_Syntax_Syntax.Tm_app uu____4805 in
                  FStar_Syntax_Syntax.mk uu____4804 in
                uu____4801 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos in
          let sub_mlift_term =
            FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term in
          let edge =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift =
                { mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term }
            } in
          let id_edge l =
            {
              msource = (sub1.FStar_Syntax_Syntax.source);
              mtarget = (sub1.FStar_Syntax_Syntax.target);
              mlift = identity_mlift
            } in
          let print_mlift l =
            let bogus_term s =
              let uu____4864 =
                let uu____4865 =
                  FStar_Ident.lid_of_path [s] FStar_Range.dummyRange in
                FStar_Syntax_Syntax.lid_as_fv uu____4865
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____4864 in
            let arg = bogus_term "ARG" in
            let wp = bogus_term "WP" in
            let e = bogus_term "COMP" in
            let uu____4869 =
              let uu____4870 = l.mlift_wp arg wp in
              FStar_Syntax_Print.term_to_string uu____4870 in
            let uu____4871 =
              let uu____4872 =
                FStar_Util.map_opt l.mlift_term
                  (fun l1  ->
                     let uu____4887 = l1 arg wp e in
                     FStar_Syntax_Print.term_to_string uu____4887) in
              FStar_Util.dflt "none" uu____4872 in
            FStar_Util.format2 "{ wp : %s ; term : %s }" uu____4869
              uu____4871 in
          let order = edge :: ((env.effects).order) in
          let ms =
            FStar_All.pipe_right (env.effects).decls
              (FStar_List.map
                 (fun uu____4900  ->
                    match uu____4900 with
                    | (e,uu____4905) -> e.FStar_Syntax_Syntax.mname)) in
          let find_edge order1 uu____4918 =
            match uu____4918 with
            | (i,j) ->
                if FStar_Ident.lid_equals i j
                then
                  FStar_All.pipe_right (id_edge i)
                    (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                else
                  FStar_All.pipe_right order1
                    (FStar_Util.find_opt
                       (fun e  ->
                          (FStar_Ident.lid_equals e.msource i) &&
                            (FStar_Ident.lid_equals e.mtarget j))) in
          let order1 =
            let fold_fun order1 k =
              let uu____4943 =
                FStar_All.pipe_right ms
                  (FStar_List.collect
                     (fun i  ->
                        if FStar_Ident.lid_equals i k
                        then []
                        else
                          FStar_All.pipe_right ms
                            (FStar_List.collect
                               (fun j  ->
                                  if FStar_Ident.lid_equals j k
                                  then []
                                  else
                                    (let uu____4955 =
                                       let uu____4960 =
                                         find_edge order1 (i, k) in
                                       let uu____4962 =
                                         find_edge order1 (k, j) in
                                       (uu____4960, uu____4962) in
                                     match uu____4955 with
                                     | (FStar_Pervasives_Native.Some
                                        e1,FStar_Pervasives_Native.Some e2)
                                         ->
                                         let uu____4971 = compose_edges e1 e2 in
                                         [uu____4971]
                                     | uu____4972 -> []))))) in
              FStar_List.append order1 uu____4943 in
            FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order) in
          let order2 =
            FStar_Util.remove_dups
              (fun e1  ->
                 fun e2  ->
                   (FStar_Ident.lid_equals e1.msource e2.msource) &&
                     (FStar_Ident.lid_equals e1.mtarget e2.mtarget)) order1 in
          (FStar_All.pipe_right order2
             (FStar_List.iter
                (fun edge1  ->
                   let uu____4987 =
                     (FStar_Ident.lid_equals edge1.msource
                        FStar_Parser_Const.effect_DIV_lid)
                       &&
                       (let uu____4988 =
                          lookup_effect_quals env edge1.mtarget in
                        FStar_All.pipe_right uu____4988
                          (FStar_List.contains
                             FStar_Syntax_Syntax.TotalEffect)) in
                   if uu____4987
                   then
                     let uu____4991 =
                       let uu____4992 =
                         let uu____4995 =
                           FStar_Util.format1
                             "Divergent computations cannot be included in an effect %s marked 'total'"
                             (edge1.mtarget).FStar_Ident.str in
                         let uu____4996 = get_range env in
                         (uu____4995, uu____4996) in
                       FStar_Errors.Error uu____4992 in
                     raise uu____4991
                   else ()));
           (let joins =
              FStar_All.pipe_right ms
                (FStar_List.collect
                   (fun i  ->
                      FStar_All.pipe_right ms
                        (FStar_List.collect
                           (fun j  ->
                              let join_opt =
                                if FStar_Ident.lid_equals i j
                                then
                                  FStar_Pervasives_Native.Some
                                    (i, (id_edge i), (id_edge i))
                                else
                                  FStar_All.pipe_right ms
                                    (FStar_List.fold_left
                                       (fun bopt  ->
                                          fun k  ->
                                            let uu____5059 =
                                              let uu____5064 =
                                                find_edge order2 (i, k) in
                                              let uu____5066 =
                                                find_edge order2 (j, k) in
                                              (uu____5064, uu____5066) in
                                            match uu____5059 with
                                            | (FStar_Pervasives_Native.Some
                                               ik,FStar_Pervasives_Native.Some
                                               jk) ->
                                                (match bopt with
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     FStar_Pervasives_Native.Some
                                                       (k, ik, jk)
                                                 | FStar_Pervasives_Native.Some
                                                     (ub,uu____5089,uu____5090)
                                                     ->
                                                     let uu____5094 =
                                                       let uu____5097 =
                                                         let uu____5098 =
                                                           find_edge order2
                                                             (k, ub) in
                                                         FStar_Util.is_some
                                                           uu____5098 in
                                                       let uu____5100 =
                                                         let uu____5101 =
                                                           find_edge order2
                                                             (ub, k) in
                                                         FStar_Util.is_some
                                                           uu____5101 in
                                                       (uu____5097,
                                                         uu____5100) in
                                                     (match uu____5094 with
                                                      | (true ,true ) ->
                                                          if
                                                            FStar_Ident.lid_equals
                                                              k ub
                                                          then
                                                            (FStar_Util.print_warning
                                                               "Looking multiple times at the same upper bound candidate";
                                                             bopt)
                                                          else
                                                            failwith
                                                              "Found a cycle in the lattice"
                                                      | (false ,false ) ->
                                                          bopt
                                                      | (true ,false ) ->
                                                          FStar_Pervasives_Native.Some
                                                            (k, ik, jk)
                                                      | (false ,true ) ->
                                                          bopt))
                                            | uu____5120 -> bopt)
                                       FStar_Pervasives_Native.None) in
                              match join_opt with
                              | FStar_Pervasives_Native.None  -> []
                              | FStar_Pervasives_Native.Some (k,e1,e2) ->
                                  [(i, j, k, (e1.mlift), (e2.mlift))])))) in
            let effects =
              let uu___119_5159 = env.effects in
              { decls = (uu___119_5159.decls); order = order2; joins } in
            let uu___120_5160 = env in
            {
              solver = (uu___120_5160.solver);
              range = (uu___120_5160.range);
              curmodule = (uu___120_5160.curmodule);
              gamma = (uu___120_5160.gamma);
              gamma_cache = (uu___120_5160.gamma_cache);
              modules = (uu___120_5160.modules);
              expected_typ = (uu___120_5160.expected_typ);
              sigtab = (uu___120_5160.sigtab);
              is_pattern = (uu___120_5160.is_pattern);
              instantiate_imp = (uu___120_5160.instantiate_imp);
              effects;
              generalize = (uu___120_5160.generalize);
              letrecs = (uu___120_5160.letrecs);
              top_level = (uu___120_5160.top_level);
              check_uvars = (uu___120_5160.check_uvars);
              use_eq = (uu___120_5160.use_eq);
              is_iface = (uu___120_5160.is_iface);
              admit = (uu___120_5160.admit);
              lax = (uu___120_5160.lax);
              lax_universes = (uu___120_5160.lax_universes);
              type_of = (uu___120_5160.type_of);
              universe_of = (uu___120_5160.universe_of);
              use_bv_sorts = (uu___120_5160.use_bv_sorts);
              qname_and_index = (uu___120_5160.qname_and_index)
            }))
      | uu____5161 -> env
let comp_to_comp_typ:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun c  ->
      let c1 =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some u)
        | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.None ) ->
            let u = env.universe_of env t in
            FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some u)
        | uu____5183 -> c in
      FStar_Syntax_Util.comp_to_comp_typ c1
let rec unfold_effect_abbrev:
  env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun env  ->
    fun comp  ->
      let c = comp_to_comp_typ env comp in
      let uu____5191 =
        lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs
          c.FStar_Syntax_Syntax.effect_name in
      match uu____5191 with
      | FStar_Pervasives_Native.None  -> c
      | FStar_Pervasives_Native.Some (binders,cdef) ->
          let uu____5201 = FStar_Syntax_Subst.open_comp binders cdef in
          (match uu____5201 with
           | (binders1,cdef1) ->
               (if
                  (FStar_List.length binders1) <>
                    ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) +
                       (Prims.parse_int "1"))
                then
                  (let uu____5218 =
                     let uu____5219 =
                       let uu____5222 =
                         let uu____5223 =
                           FStar_Util.string_of_int
                             (FStar_List.length binders1) in
                         let uu____5229 =
                           FStar_Util.string_of_int
                             ((FStar_List.length
                                 c.FStar_Syntax_Syntax.effect_args)
                                + (Prims.parse_int "1")) in
                         let uu____5237 =
                           let uu____5238 = FStar_Syntax_Syntax.mk_Comp c in
                           FStar_Syntax_Print.comp_to_string uu____5238 in
                         FStar_Util.format3
                           "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s"
                           uu____5223 uu____5229 uu____5237 in
                       (uu____5222, (comp.FStar_Syntax_Syntax.pos)) in
                     FStar_Errors.Error uu____5219 in
                   raise uu____5218)
                else ();
                (let inst1 =
                   let uu____5242 =
                     let uu____5248 =
                       FStar_Syntax_Syntax.as_arg
                         c.FStar_Syntax_Syntax.result_typ in
                     uu____5248 :: (c.FStar_Syntax_Syntax.effect_args) in
                   FStar_List.map2
                     (fun uu____5255  ->
                        fun uu____5256  ->
                          match (uu____5255, uu____5256) with
                          | ((x,uu____5270),(t,uu____5272)) ->
                              FStar_Syntax_Syntax.NT (x, t)) binders1
                     uu____5242 in
                 let c1 = FStar_Syntax_Subst.subst_comp inst1 cdef1 in
                 let c2 =
                   let uu____5287 =
                     let uu___121_5288 = comp_to_comp_typ env c1 in
                     {
                       FStar_Syntax_Syntax.comp_univs =
                         (uu___121_5288.FStar_Syntax_Syntax.comp_univs);
                       FStar_Syntax_Syntax.effect_name =
                         (uu___121_5288.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ =
                         (uu___121_5288.FStar_Syntax_Syntax.result_typ);
                       FStar_Syntax_Syntax.effect_args =
                         (uu___121_5288.FStar_Syntax_Syntax.effect_args);
                       FStar_Syntax_Syntax.flags =
                         (c.FStar_Syntax_Syntax.flags)
                     } in
                   FStar_All.pipe_right uu____5287
                     FStar_Syntax_Syntax.mk_Comp in
                 unfold_effect_abbrev env c2)))
let effect_repr_aux only_reifiable env c u_c =
  let uu____5318 =
    let uu____5323 = norm_eff_name env (FStar_Syntax_Util.comp_effect_name c) in
    effect_decl_opt env uu____5323 in
  match uu____5318 with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
      let uu____5339 =
        only_reifiable &&
          (let uu____5340 =
             FStar_All.pipe_right qualifiers
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
           Prims.op_Negation uu____5340) in
      if uu____5339
      then FStar_Pervasives_Native.None
      else
        (match (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
         | uu____5353 ->
             let c1 = unfold_effect_abbrev env c in
             let uu____5355 =
               let uu____5364 =
                 FStar_List.hd c1.FStar_Syntax_Syntax.effect_args in
               ((c1.FStar_Syntax_Syntax.result_typ), uu____5364) in
             (match uu____5355 with
              | (res_typ,wp) ->
                  let repr =
                    inst_effect_fun_with [u_c] env ed
                      ([], (ed.FStar_Syntax_Syntax.repr)) in
                  let uu____5398 =
                    let uu____5401 = get_range env in
                    let uu____5402 =
                      let uu____5405 =
                        let uu____5406 =
                          let uu____5416 =
                            let uu____5418 =
                              FStar_Syntax_Syntax.as_arg res_typ in
                            [uu____5418; wp] in
                          (repr, uu____5416) in
                        FStar_Syntax_Syntax.Tm_app uu____5406 in
                      FStar_Syntax_Syntax.mk uu____5405 in
                    uu____5402 FStar_Pervasives_Native.None uu____5401 in
                  FStar_Pervasives_Native.Some uu____5398))
let effect_repr:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option
  = fun env  -> fun c  -> fun u_c  -> effect_repr_aux false env c u_c
let reify_comp:
  env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun u_c  ->
        let no_reify l =
          let uu____5462 =
            let uu____5463 =
              let uu____5466 =
                let uu____5467 = FStar_Ident.string_of_lid l in
                FStar_Util.format1 "Effect %s cannot be reified" uu____5467 in
              let uu____5468 = get_range env in (uu____5466, uu____5468) in
            FStar_Errors.Error uu____5463 in
          raise uu____5462 in
        let uu____5469 = effect_repr_aux true env c u_c in
        match uu____5469 with
        | FStar_Pervasives_Native.None  ->
            no_reify (FStar_Syntax_Util.comp_effect_name c)
        | FStar_Pervasives_Native.Some tm -> tm
let is_reifiable_effect: env -> FStar_Ident.lident -> Prims.bool =
  fun env  ->
    fun effect_lid  ->
      let quals = lookup_effect_quals env effect_lid in
      FStar_List.contains FStar_Syntax_Syntax.Reifiable quals
let is_reifiable:
  env ->
    (FStar_Syntax_Syntax.lcomp,FStar_Syntax_Syntax.residual_comp)
      FStar_Util.either -> Prims.bool
  =
  fun env  ->
    fun c  ->
      let effect_lid =
        match c with
        | FStar_Util.Inl lc -> lc.FStar_Syntax_Syntax.eff_name
        | FStar_Util.Inr (eff_name,uu____5501) -> eff_name in
      is_reifiable_effect env effect_lid
let is_reifiable_comp: env -> FStar_Syntax_Syntax.comp -> Prims.bool =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Comp ct ->
          is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name
      | uu____5514 -> false
let is_reifiable_function: env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____5521 =
        let uu____5522 = FStar_Syntax_Subst.compress t in
        uu____5522.FStar_Syntax_Syntax.n in
      match uu____5521 with
      | FStar_Syntax_Syntax.Tm_arrow (uu____5525,c) ->
          is_reifiable_comp env c
      | uu____5537 -> false
let push_in_gamma: env -> binding -> env =
  fun env  ->
    fun s  ->
      let rec push1 x rest =
        match rest with
        | (Binding_sig uu____5555)::uu____5556 -> x :: rest
        | (Binding_sig_inst uu____5561)::uu____5562 -> x :: rest
        | [] -> [x]
        | local::rest1 ->
            let uu____5571 = push1 x rest1 in local :: uu____5571 in
      let uu___122_5573 = env in
      let uu____5574 = push1 s env.gamma in
      {
        solver = (uu___122_5573.solver);
        range = (uu___122_5573.range);
        curmodule = (uu___122_5573.curmodule);
        gamma = uu____5574;
        gamma_cache = (uu___122_5573.gamma_cache);
        modules = (uu___122_5573.modules);
        expected_typ = (uu___122_5573.expected_typ);
        sigtab = (uu___122_5573.sigtab);
        is_pattern = (uu___122_5573.is_pattern);
        instantiate_imp = (uu___122_5573.instantiate_imp);
        effects = (uu___122_5573.effects);
        generalize = (uu___122_5573.generalize);
        letrecs = (uu___122_5573.letrecs);
        top_level = (uu___122_5573.top_level);
        check_uvars = (uu___122_5573.check_uvars);
        use_eq = (uu___122_5573.use_eq);
        is_iface = (uu___122_5573.is_iface);
        admit = (uu___122_5573.admit);
        lax = (uu___122_5573.lax);
        lax_universes = (uu___122_5573.lax_universes);
        type_of = (uu___122_5573.type_of);
        universe_of = (uu___122_5573.universe_of);
        use_bv_sorts = (uu___122_5573.use_bv_sorts);
        qname_and_index = (uu___122_5573.qname_and_index)
      }
let push_sigelt: env -> FStar_Syntax_Syntax.sigelt -> env =
  fun env  ->
    fun s  ->
      let env1 =
        push_in_gamma env
          (Binding_sig ((FStar_Syntax_Util.lids_of_sigelt s), s)) in
      build_lattice env1 s
let push_sigelt_inst:
  env -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.universes -> env =
  fun env  ->
    fun s  ->
      fun us  ->
        let env1 =
          push_in_gamma env
            (Binding_sig_inst ((FStar_Syntax_Util.lids_of_sigelt s), s, us)) in
        build_lattice env1 s
let push_local_binding: env -> binding -> env =
  fun env  ->
    fun b  ->
      let uu___123_5601 = env in
      {
        solver = (uu___123_5601.solver);
        range = (uu___123_5601.range);
        curmodule = (uu___123_5601.curmodule);
        gamma = (b :: (env.gamma));
        gamma_cache = (uu___123_5601.gamma_cache);
        modules = (uu___123_5601.modules);
        expected_typ = (uu___123_5601.expected_typ);
        sigtab = (uu___123_5601.sigtab);
        is_pattern = (uu___123_5601.is_pattern);
        instantiate_imp = (uu___123_5601.instantiate_imp);
        effects = (uu___123_5601.effects);
        generalize = (uu___123_5601.generalize);
        letrecs = (uu___123_5601.letrecs);
        top_level = (uu___123_5601.top_level);
        check_uvars = (uu___123_5601.check_uvars);
        use_eq = (uu___123_5601.use_eq);
        is_iface = (uu___123_5601.is_iface);
        admit = (uu___123_5601.admit);
        lax = (uu___123_5601.lax);
        lax_universes = (uu___123_5601.lax_universes);
        type_of = (uu___123_5601.type_of);
        universe_of = (uu___123_5601.universe_of);
        use_bv_sorts = (uu___123_5601.use_bv_sorts);
        qname_and_index = (uu___123_5601.qname_and_index)
      }
let push_bv: env -> FStar_Syntax_Syntax.bv -> env =
  fun env  -> fun x  -> push_local_binding env (Binding_var x)
let pop_bv:
  env ->
    (FStar_Syntax_Syntax.bv,env) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun env  ->
    match env.gamma with
    | (Binding_var x)::rest ->
        FStar_Pervasives_Native.Some
          (x,
            (let uu___124_5622 = env in
             {
               solver = (uu___124_5622.solver);
               range = (uu___124_5622.range);
               curmodule = (uu___124_5622.curmodule);
               gamma = rest;
               gamma_cache = (uu___124_5622.gamma_cache);
               modules = (uu___124_5622.modules);
               expected_typ = (uu___124_5622.expected_typ);
               sigtab = (uu___124_5622.sigtab);
               is_pattern = (uu___124_5622.is_pattern);
               instantiate_imp = (uu___124_5622.instantiate_imp);
               effects = (uu___124_5622.effects);
               generalize = (uu___124_5622.generalize);
               letrecs = (uu___124_5622.letrecs);
               top_level = (uu___124_5622.top_level);
               check_uvars = (uu___124_5622.check_uvars);
               use_eq = (uu___124_5622.use_eq);
               is_iface = (uu___124_5622.is_iface);
               admit = (uu___124_5622.admit);
               lax = (uu___124_5622.lax);
               lax_universes = (uu___124_5622.lax_universes);
               type_of = (uu___124_5622.type_of);
               universe_of = (uu___124_5622.universe_of);
               use_bv_sorts = (uu___124_5622.use_bv_sorts);
               qname_and_index = (uu___124_5622.qname_and_index)
             }))
    | uu____5623 -> FStar_Pervasives_Native.None
let push_binders: env -> FStar_Syntax_Syntax.binders -> env =
  fun env  ->
    fun bs  ->
      FStar_List.fold_left
        (fun env1  ->
           fun uu____5636  ->
             match uu____5636 with | (x,uu____5640) -> push_bv env1 x) env bs
let binding_of_lb:
  FStar_Syntax_Syntax.lbname ->
    (FStar_Syntax_Syntax.univ_name Prims.list,(FStar_Syntax_Syntax.term',
                                                FStar_Syntax_Syntax.term')
                                                FStar_Syntax_Syntax.syntax)
      FStar_Pervasives_Native.tuple2 -> binding
  =
  fun x  ->
    fun t  ->
      match x with
      | FStar_Util.Inl x1 ->
          let x2 =
            let uu___125_5660 = x1 in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___125_5660.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___125_5660.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)
            } in
          Binding_var x2
      | FStar_Util.Inr fv ->
          Binding_lid
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v), t)
let push_let_binding:
  env -> FStar_Syntax_Syntax.lbname -> FStar_Syntax_Syntax.tscheme -> env =
  fun env  ->
    fun lb  -> fun ts  -> push_local_binding env (binding_of_lb lb ts)
let push_module: env -> FStar_Syntax_Syntax.modul -> env =
  fun env  ->
    fun m  ->
      add_sigelts env m.FStar_Syntax_Syntax.exports;
      (let uu___126_5690 = env in
       {
         solver = (uu___126_5690.solver);
         range = (uu___126_5690.range);
         curmodule = (uu___126_5690.curmodule);
         gamma = [];
         gamma_cache = (uu___126_5690.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = FStar_Pervasives_Native.None;
         sigtab = (uu___126_5690.sigtab);
         is_pattern = (uu___126_5690.is_pattern);
         instantiate_imp = (uu___126_5690.instantiate_imp);
         effects = (uu___126_5690.effects);
         generalize = (uu___126_5690.generalize);
         letrecs = (uu___126_5690.letrecs);
         top_level = (uu___126_5690.top_level);
         check_uvars = (uu___126_5690.check_uvars);
         use_eq = (uu___126_5690.use_eq);
         is_iface = (uu___126_5690.is_iface);
         admit = (uu___126_5690.admit);
         lax = (uu___126_5690.lax);
         lax_universes = (uu___126_5690.lax_universes);
         type_of = (uu___126_5690.type_of);
         universe_of = (uu___126_5690.universe_of);
         use_bv_sorts = (uu___126_5690.use_bv_sorts);
         qname_and_index = (uu___126_5690.qname_and_index)
       })
let push_univ_vars: env_t -> FStar_Syntax_Syntax.univ_names -> env =
  fun env  ->
    fun xs  ->
      FStar_List.fold_left
        (fun env1  -> fun x  -> push_local_binding env1 (Binding_univ x)) env
        xs
let open_universes_in:
  env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.term Prims.list ->
        (env,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term
                                              Prims.list)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun uvs  ->
      fun terms  ->
        let uu____5714 = FStar_Syntax_Subst.univ_var_opening uvs in
        match uu____5714 with
        | (univ_subst,univ_vars) ->
            let env' = push_univ_vars env univ_vars in
            let uu____5730 =
              FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms in
            (env', univ_vars, uu____5730)
let set_expected_typ: env -> FStar_Syntax_Syntax.typ -> env =
  fun env  ->
    fun t  ->
      let uu___127_5740 = env in
      {
        solver = (uu___127_5740.solver);
        range = (uu___127_5740.range);
        curmodule = (uu___127_5740.curmodule);
        gamma = (uu___127_5740.gamma);
        gamma_cache = (uu___127_5740.gamma_cache);
        modules = (uu___127_5740.modules);
        expected_typ = (FStar_Pervasives_Native.Some t);
        sigtab = (uu___127_5740.sigtab);
        is_pattern = (uu___127_5740.is_pattern);
        instantiate_imp = (uu___127_5740.instantiate_imp);
        effects = (uu___127_5740.effects);
        generalize = (uu___127_5740.generalize);
        letrecs = (uu___127_5740.letrecs);
        top_level = (uu___127_5740.top_level);
        check_uvars = (uu___127_5740.check_uvars);
        use_eq = false;
        is_iface = (uu___127_5740.is_iface);
        admit = (uu___127_5740.admit);
        lax = (uu___127_5740.lax);
        lax_universes = (uu___127_5740.lax_universes);
        type_of = (uu___127_5740.type_of);
        universe_of = (uu___127_5740.universe_of);
        use_bv_sorts = (uu___127_5740.use_bv_sorts);
        qname_and_index = (uu___127_5740.qname_and_index)
      }
let expected_typ:
  env -> FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option =
  fun env  ->
    match env.expected_typ with
    | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
let clear_expected_typ:
  env ->
    (env,FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun env_  ->
    let uu____5756 = expected_typ env_ in
    ((let uu___128_5759 = env_ in
      {
        solver = (uu___128_5759.solver);
        range = (uu___128_5759.range);
        curmodule = (uu___128_5759.curmodule);
        gamma = (uu___128_5759.gamma);
        gamma_cache = (uu___128_5759.gamma_cache);
        modules = (uu___128_5759.modules);
        expected_typ = FStar_Pervasives_Native.None;
        sigtab = (uu___128_5759.sigtab);
        is_pattern = (uu___128_5759.is_pattern);
        instantiate_imp = (uu___128_5759.instantiate_imp);
        effects = (uu___128_5759.effects);
        generalize = (uu___128_5759.generalize);
        letrecs = (uu___128_5759.letrecs);
        top_level = (uu___128_5759.top_level);
        check_uvars = (uu___128_5759.check_uvars);
        use_eq = false;
        is_iface = (uu___128_5759.is_iface);
        admit = (uu___128_5759.admit);
        lax = (uu___128_5759.lax);
        lax_universes = (uu___128_5759.lax_universes);
        type_of = (uu___128_5759.type_of);
        universe_of = (uu___128_5759.universe_of);
        use_bv_sorts = (uu___128_5759.use_bv_sorts);
        qname_and_index = (uu___128_5759.qname_and_index)
      }), uu____5756)
let finish_module: env -> FStar_Syntax_Syntax.modul -> env =
  let empty_lid = FStar_Ident.lid_of_ids [FStar_Ident.id_of_text ""] in
  fun env  ->
    fun m  ->
      let sigs =
        if
          FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid
        then
          let uu____5770 =
            FStar_All.pipe_right env.gamma
              (FStar_List.collect
                 (fun uu___107_5774  ->
                    match uu___107_5774 with
                    | Binding_sig (uu____5776,se) -> [se]
                    | uu____5780 -> [])) in
          FStar_All.pipe_right uu____5770 FStar_List.rev
        else m.FStar_Syntax_Syntax.exports in
      add_sigelts env sigs;
      (let uu___129_5785 = env in
       {
         solver = (uu___129_5785.solver);
         range = (uu___129_5785.range);
         curmodule = empty_lid;
         gamma = [];
         gamma_cache = (uu___129_5785.gamma_cache);
         modules = (m :: (env.modules));
         expected_typ = (uu___129_5785.expected_typ);
         sigtab = (uu___129_5785.sigtab);
         is_pattern = (uu___129_5785.is_pattern);
         instantiate_imp = (uu___129_5785.instantiate_imp);
         effects = (uu___129_5785.effects);
         generalize = (uu___129_5785.generalize);
         letrecs = (uu___129_5785.letrecs);
         top_level = (uu___129_5785.top_level);
         check_uvars = (uu___129_5785.check_uvars);
         use_eq = (uu___129_5785.use_eq);
         is_iface = (uu___129_5785.is_iface);
         admit = (uu___129_5785.admit);
         lax = (uu___129_5785.lax);
         lax_universes = (uu___129_5785.lax_universes);
         type_of = (uu___129_5785.type_of);
         universe_of = (uu___129_5785.universe_of);
         use_bv_sorts = (uu___129_5785.use_bv_sorts);
         qname_and_index = (uu___129_5785.qname_and_index)
       })
let uvars_in_env:
  env ->
    (FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2 FStar_Util.set
  =
  fun env  ->
    let no_uvs1 = FStar_Syntax_Syntax.new_uv_set () in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_univ uu____5835)::tl1 -> aux out tl1
      | (Binding_lid (uu____5838,(uu____5839,t)))::tl1 ->
          let uu____5848 =
            let uu____5852 = FStar_Syntax_Free.uvars t in ext out uu____5852 in
          aux uu____5848 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5856;
            FStar_Syntax_Syntax.index = uu____5857;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5863 =
            let uu____5867 = FStar_Syntax_Free.uvars t in ext out uu____5867 in
          aux uu____5863 tl1
      | (Binding_sig uu____5871)::uu____5872 -> out
      | (Binding_sig_inst uu____5877)::uu____5878 -> out in
    aux no_uvs1 env.gamma
let univ_vars: env -> FStar_Syntax_Syntax.universe_uvar FStar_Util.set =
  fun env  ->
    let no_univs = FStar_Syntax_Syntax.no_universe_uvars in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5915)::tl1 -> aux out tl1
      | (Binding_univ uu____5922)::tl1 -> aux out tl1
      | (Binding_lid (uu____5925,(uu____5926,t)))::tl1 ->
          let uu____5935 =
            let uu____5937 = FStar_Syntax_Free.univs t in ext out uu____5937 in
          aux uu____5935 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____5939;
            FStar_Syntax_Syntax.index = uu____5940;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____5946 =
            let uu____5948 = FStar_Syntax_Free.univs t in ext out uu____5948 in
          aux uu____5946 tl1
      | (Binding_sig uu____5950)::uu____5951 -> out in
    aux no_univs env.gamma
let univnames: env -> FStar_Syntax_Syntax.univ_name FStar_Util.set =
  fun env  ->
    let no_univ_names = FStar_Syntax_Syntax.no_universe_names in
    let ext out uvs = FStar_Util.set_union out uvs in
    let rec aux out g =
      match g with
      | [] -> out
      | (Binding_sig_inst uu____5988)::tl1 -> aux out tl1
      | (Binding_univ uname)::tl1 ->
          let uu____5998 = FStar_Util.set_add uname out in aux uu____5998 tl1
      | (Binding_lid (uu____6000,(uu____6001,t)))::tl1 ->
          let uu____6010 =
            let uu____6012 = FStar_Syntax_Free.univnames t in
            ext out uu____6012 in
          aux uu____6010 tl1
      | (Binding_var
          { FStar_Syntax_Syntax.ppname = uu____6014;
            FStar_Syntax_Syntax.index = uu____6015;
            FStar_Syntax_Syntax.sort = t;_})::tl1
          ->
          let uu____6021 =
            let uu____6023 = FStar_Syntax_Free.univnames t in
            ext out uu____6023 in
          aux uu____6021 tl1
      | (Binding_sig uu____6025)::uu____6026 -> out in
    aux no_univ_names env.gamma
let bound_vars_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.bv Prims.list =
  fun bs  ->
    FStar_All.pipe_right bs
      (FStar_List.collect
         (fun uu___108_6042  ->
            match uu___108_6042 with
            | Binding_var x -> [x]
            | Binding_lid uu____6045 -> []
            | Binding_sig uu____6048 -> []
            | Binding_univ uu____6052 -> []
            | Binding_sig_inst uu____6053 -> []))
let binders_of_bindings:
  binding Prims.list -> FStar_Syntax_Syntax.binder Prims.list =
  fun bs  ->
    let uu____6063 =
      let uu____6065 = bound_vars_of_bindings bs in
      FStar_All.pipe_right uu____6065
        (FStar_List.map FStar_Syntax_Syntax.mk_binder) in
    FStar_All.pipe_right uu____6063 FStar_List.rev
let bound_vars: env -> FStar_Syntax_Syntax.bv Prims.list =
  fun env  -> bound_vars_of_bindings env.gamma
let all_binders: env -> FStar_Syntax_Syntax.binders =
  fun env  -> binders_of_bindings env.gamma
let print_gamma: env -> Prims.unit =
  fun env  ->
    let uu____6081 =
      let uu____6082 =
        FStar_All.pipe_right env.gamma
          (FStar_List.map
             (fun uu___109_6086  ->
                match uu___109_6086 with
                | Binding_var x ->
                    let uu____6088 = FStar_Syntax_Print.bv_to_string x in
                    Prims.strcat "Binding_var " uu____6088
                | Binding_univ u ->
                    Prims.strcat "Binding_univ " u.FStar_Ident.idText
                | Binding_lid (l,uu____6091) ->
                    let uu____6092 = FStar_Ident.string_of_lid l in
                    Prims.strcat "Binding_lid " uu____6092
                | Binding_sig (ls,uu____6094) ->
                    let uu____6097 =
                      let uu____6098 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6098
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig " uu____6097
                | Binding_sig_inst (ls,uu____6104,uu____6105) ->
                    let uu____6108 =
                      let uu____6109 =
                        FStar_All.pipe_right ls
                          (FStar_List.map FStar_Ident.string_of_lid) in
                      FStar_All.pipe_right uu____6109
                        (FStar_String.concat ", ") in
                    Prims.strcat "Binding_sig_inst " uu____6108)) in
      FStar_All.pipe_right uu____6082 (FStar_String.concat "::\n") in
    FStar_All.pipe_right uu____6081 (FStar_Util.print1 "%s\n")
let eq_gamma: env -> env -> Prims.bool =
  fun env  ->
    fun env'  ->
      let uu____6121 = FStar_Util.physical_equality env.gamma env'.gamma in
      if uu____6121
      then true
      else
        (let g = all_binders env in
         let g' = all_binders env' in
         ((FStar_List.length g) = (FStar_List.length g')) &&
           (FStar_List.forall2
              (fun uu____6138  ->
                 fun uu____6139  ->
                   match (uu____6138, uu____6139) with
                   | ((b1,uu____6149),(b2,uu____6151)) ->
                       FStar_Syntax_Syntax.bv_eq b1 b2) g g'))
let fold_env env f a =
  FStar_List.fold_right (fun e  -> fun a1  -> f a1 e) env.gamma a
let lidents: env -> FStar_Ident.lident Prims.list =
  fun env  ->
    let keys =
      FStar_List.fold_left
        (fun keys  ->
           fun uu___110_6194  ->
             match uu___110_6194 with
             | Binding_sig (lids,uu____6198) -> FStar_List.append lids keys
             | uu____6201 -> keys) [] env.gamma in
    FStar_Util.smap_fold (sigtab env)
      (fun uu____6203  ->
         fun v1  ->
           fun keys1  ->
             FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)
      keys
let dummy_solver: solver_t =
  {
    init = (fun uu____6207  -> ());
    push = (fun uu____6208  -> ());
    pop = (fun uu____6209  -> ());
    mark = (fun uu____6210  -> ());
    reset_mark = (fun uu____6211  -> ());
    commit_mark = (fun uu____6212  -> ());
    encode_modul = (fun uu____6213  -> fun uu____6214  -> ());
    encode_sig = (fun uu____6215  -> fun uu____6216  -> ());
    preprocess = (fun e  -> fun g  -> [(e, g)]);
    solve = (fun uu____6223  -> fun uu____6224  -> fun uu____6225  -> ());
    is_trivial = (fun uu____6229  -> fun uu____6230  -> false);
    finish = (fun uu____6231  -> ());
    refresh = (fun uu____6232  -> ())
  }