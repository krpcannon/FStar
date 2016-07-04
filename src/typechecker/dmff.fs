(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.TypeChecker.DMFF

open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module U  = FStar.Syntax.Util

let gen_wps_for_free env binders a wp_a tc_term (ed: Syntax.eff_decl): Syntax.eff_decl =
  (* A series of macros and combinators to automatically build WP's. In these
   * definitions, both [binders] and [a] are opened. This means that macros
   * close over [binders] and [a], and this means that combinators do not expect
   * [binders] and [a] when applied. *)
  let normalize = N.normalize [ N.Beta; N.Inline; N.UnfoldUntil S.Delta_constant ] env in

  let d s = Util.print1 "\x1b[01;36m%s\x1b[00m\n" s in
  let normalize_and_make_binders_explicit tm =
    let tm = normalize tm in
    let rec visit_term tm =
      let n = match (SS.compress tm).n with
        | Tm_arrow (binders, comp) ->
            let comp = visit_comp comp in
            let binders = List.map visit_binder binders in
            Tm_arrow (binders, comp)
        | Tm_abs (binders, term, comp) ->
            let comp = visit_maybe_lcomp comp in
            let term = visit_term term in
            let binders = List.map visit_binder binders in
            Tm_abs (binders, term, comp)
        | _ ->
            tm.n
      in
      { tm with n = n }
    and visit_binder (bv, a) =
      { bv with sort = visit_term bv.sort }, S.as_implicit false
    and visit_maybe_lcomp lcomp =
      match lcomp with
      | Some (Inl lcomp) ->
          Some (Inl (U.lcomp_of_comp (visit_comp (lcomp.comp ()))))
      | comp ->
          comp
    and visit_comp comp =
      let n = match comp.n with
        | Total tm ->
            Total (visit_term tm)
        | GTotal tm ->
            GTotal (visit_term tm)
        | comp ->
            comp
      in
      { comp with n = n }
    and visit_args args =
      List.map (fun (tm, q) -> visit_term tm, q) args
    in
    visit_term tm
  in

  (* A debug / sanity check. *)
  let check str t =
    if Env.debug env (Options.Other "ED") then begin
      Util.print2 "Generated term for %s: %s\n" str (Print.term_to_string t);
      let t = normalize t in
      let t = SS.compress t in
      let e, { res_typ = res_typ }, _ = tc_term env t in
      Util.print2 "Inferred type for %s: %s\n" str (Print.term_to_string (normalize res_typ));
      Util.print2 "Elaborated term for %s: %s\n" str (Print.term_to_string (normalize e))
    end
  in

  (* Consider the predicate transformer st_wp:
   *   let st_pre_h  (heap:Type)          = heap -> GTot Type0
   *   let st_post_h (heap:Type) (a:Type) = a -> heap -> GTot Type0
   *   let st_wp_h   (heap:Type) (a:Type) = st_post_h heap a -> Tot (st_pre_h heap)
   * after reduction we get:
   *   let st_wp_h (heap: Type) (a: Type) = (a -> heap -> GTot Type0) -> heap -> GTot Type0
   * we want:
   *   type st2_gctx (heap: Type) (a:Type) (t:Type) = (a -> heap -> GTot Type0) -> heap -> GTot t
   * we thus generate macros parameterized over [e] that build the right
   * context. [gamma] is the series of binders the precede the return type of
   * the context. *)
  let rec collect_binders (t : term) =
    match (compress t).n with
    | Tm_arrow (bs, comp) ->
        let rest = match comp.n with
                   | Total t -> t
                   | _ -> failwith "wp_a contains non-Tot arrow" in
        bs @ (collect_binders rest)
    | Tm_type _ ->
        []
    | _ ->
        failwith "wp_a doesn't end in Type0" in

  let mk_ctx, mk_gctx, mk_gamma =
    let i = ref 0 in
    let wp_binders = collect_binders (normalize wp_a) in
    (fun t -> U.arrow wp_binders (mk_Total t)),
    (fun t -> U.arrow wp_binders (mk_GTotal t)),
    (fun () -> List.map (fun (bv, _) ->
          (* Note: just returning [wp_binders] here would be wrong, because the
           * identity of binders relies on the _physical equality_ of the [bv]
           * data structure. So, arguments passed to [mk_ctx] should never refer
           * to [wp_binders]; one way to enforce that is to generate fresh
           * binders whenever the client asks for it. *)
          i := !i + 1;
          S.gen_bv ("g" ^ string_of_int !i) None bv.sort
        ) wp_binders)
  in

  (* A variation where we can specify implicit parameters. *)
  let binders_of_list = List.map (fun (t, b) -> t, S.as_implicit b) in

  let implicit_binders_of_list = List.map (fun t -> t, S.as_implicit true) in

  let args_of_bv = List.map (fun bv -> S.as_arg (S.bv_to_name bv)) in

  (* val st2_pure : #heap:Type -> #a:Type -> #t:Type -> x:t ->
       Tot (st2_ctx heap a t)
     let st2_pure #heap #a #t x = fun _post _h -> x *)
  let c_pure =
    let t = S.gen_bv "t" None U.ktype in
    let x = S.gen_bv "x" None (S.bv_to_name t) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_ctx (S.bv_to_name t))))) in
    let gamma = mk_gamma () in
    let body = U.abs (implicit_binders_of_list gamma) (S.bv_to_name x) ret in
    U.abs (binders_of_list [ t, true; x, false ]) body ret
  in
  check "pure" (U.abs (binders @ [ S.mk_binder a ]) c_pure None);

  (* val st2_app : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                  l:st2_gctx heap a (t1 -> GTot t2) ->
                  r:st2_gctx heap a t1 ->
                  Tot (st2_gctx heap a t2)
    let st2_app #heap #a #t1 #t2 l r = fun p h -> l p h (r p h) *)
  let c_app =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let l = S.gen_bv "l" None (mk_gctx
      (U.arrow [ S.mk_binder (S.new_bv None (S.bv_to_name t1)) ] (S.mk_GTotal (S.bv_to_name t2))))
    in
    let r = S.gen_bv "r" None (mk_gctx (S.bv_to_name t1)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t2))))) in
    let outer_body =
      let gamma = mk_gamma () in
      let gamma_as_args = args_of_bv gamma in
      let inner_body =
        U.mk_app
          (S.bv_to_name l)
          (gamma_as_args @ [ S.as_arg (U.mk_app (S.bv_to_name r) gamma_as_args)])
      in
      U.abs (implicit_binders_of_list gamma) inner_body ret
    in
    U.abs (binders_of_list [ t1, true; t2, true; l, false; r, false ]) outer_body ret
  in
  check "app" (U.abs (binders @ [ S.mk_binder a ]) c_app None);

  (* val st2_liftGA1 : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                       f : (t1 -> GTot t2) ->
                       st2_gctx heap a t1 ->
                       Tot (st2_gctx heap a t2)
    let st2_liftGA1 #heap #a #t1 #t2 f a1 =
                    st2_app (st2_pure f) a1
  *)
  let unknown = mk Tm_unknown None Range.dummyRange in
  let c_lift1 =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t_f = U.arrow [ S.null_binder (S.bv_to_name t1) ] (S.mk_GTotal (S.bv_to_name t2)) in
    let f = S.gen_bv "f" None t_f in
    let a1 = S.gen_bv "a1" None (mk_gctx (S.bv_to_name t1)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t2))))) in
    U.abs (binders_of_list [ t1, true; t2, true; f, false; a1, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [ unknown; S.bv_to_name f ]);
        S.bv_to_name a1 ])
    ) ret
  in
  check "lift1" (U.abs (binders @ [ S.mk_binder a ]) c_lift1 None);


  (* val st2_liftGA2 : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type -> #t3:Type ->
                       f : (t1 -> t2 -> GTot t3) ->
                       a1: st2_gctx heap a t1 ->
                       a2: st2_gctx heap a t2 ->
                       Tot (st2_gctx heap a t3)
    let st2_liftGA2 #heap #a #t1 #t2 #t3 f a1 a2 =
      st2_app (st2_app (st2_pure f) a1) a2
  *)
  let c_lift2 =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t3 = S.gen_bv "t3" None U.ktype in
    let t_f = U.arrow
      [ S.null_binder (S.bv_to_name t1); S.null_binder (S.bv_to_name t2) ]
      (S.mk_GTotal (S.bv_to_name t3))
    in
    let f = S.gen_bv "f" None t_f in
    let a1 = S.gen_bv "a1" None (mk_gctx (S.bv_to_name t1)) in
    let a2 = S.gen_bv "a2" None (mk_gctx (S.bv_to_name t2)) in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_gctx (S.bv_to_name t3))))) in
    U.abs (binders_of_list [ t1, true; t2, true; t3, true; f, false; a1, false; a2, false ]) (
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_app (List.map S.as_arg [
          unknown; unknown;
          U.mk_app c_pure (List.map S.as_arg [ unknown; S.bv_to_name f ]);
          S.bv_to_name a1 ]);
        S.bv_to_name a2 ])
    ) ret
  in
  check "lift2" (U.abs (binders @ [ S.mk_binder a ]) c_lift2 None);

  (* val st2_push : #heap:Type -> #a:Type -> #t1:Type -> #t2:Type ->
                    f:(t1 -> Tot (st2_gctx heap a t2)) ->
                    Tot (st2_ctx heap a (t1->GTot t2))
    let st2_push #heap #a #t1 #t2 f = fun p h e1 -> f e1 p h *)
  let c_push =
    let t1 = S.gen_bv "t1" None U.ktype in
    let t2 = S.gen_bv "t2" None U.ktype in
    let t_f = U.arrow
      [ S.null_binder (S.bv_to_name t1) ]
      (S.mk_Total (mk_gctx (S.bv_to_name t2)))
    in
    let f = S.gen_bv "f" None t_f in
    let ret = Some (Inl (U.lcomp_of_comp (mk_Total (mk_ctx (
      U.arrow [ S.null_binder (S.bv_to_name t1) ] (S.mk_GTotal (S.bv_to_name t2)))))))
    in
    let e1 = S.gen_bv "e1" None (S.bv_to_name t1) in
    let gamma = mk_gamma () in
    let body = U.abs (S.binders_of_list gamma @ [ S.mk_binder e1 ]) (
      U.mk_app (S.bv_to_name f) (S.as_arg (S.bv_to_name e1) :: args_of_bv gamma)
    ) ret in
    U.abs (binders_of_list [ t1, true; t2, true; f, false ]) body ret
  in
  check "push" (U.abs (binders @ [ S.mk_binder a ]) c_push None);

  let ret_tot_wp_a = Some (Inl (U.lcomp_of_comp (mk_Total wp_a))) in

  (* val st2_if_then_else : heap:Type -> a:Type -> c:Type0 ->
                            st2_wp heap a -> st2_wp heap a ->
                            Tot (st2_wp heap a)
    let st2_if_then_else heap a c = st2_liftGA2 (l_ITE c) *)
  let wp_if_then_else =
    let c = S.gen_bv "c" None U.ktype in
    (* Note that this one *does* abstract over [a]. This is in line with the
     * expected shape of the combinator in the effect declaration. (But it does
     * not abstract over [binders]; [tc_eff_decl] will take care of closing
     * [binders]. *)
    U.abs (S.binders_of_list [ a; c ]) (
      let l_ite = fvar Const.ite_lid (S.Delta_unfoldable 2) None in
      U.mk_app c_lift2 (List.map S.as_arg [
        unknown; unknown; unknown;
        U.mk_app l_ite [S.as_arg (S.bv_to_name c)]
      ])
    ) ret_tot_wp_a
  in
  let wp_if_then_else = normalize_and_make_binders_explicit wp_if_then_else in
  check "wp_if_then_else" (U.abs binders wp_if_then_else None);

  (* val st2_assert_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assert_p heap a q wp = st2_app (st2_pure (l_and q)) wp *)
  let wp_assert =
    let q = S.gen_bv "q" None U.ktype0 in
    let wp = S.gen_bv "wp" None wp_a in
    let l_and = fvar Const.and_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          U.mk_app l_and [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assert = normalize_and_make_binders_explicit wp_assert in
  check "wp_assert" (U.abs binders wp_assert None);

  (* val st2_assume_p : heap:Type ->a:Type -> q:Type0 -> st2_wp heap a ->
                       Tot (st2_wp heap a)
    let st2_assume_p heap a q wp = st2_app (st2_pure (l_imp q)) wp *)
  let wp_assume =
    let q = S.gen_bv "q" None U.ktype0 in
    let wp = S.gen_bv "wp" None wp_a in
    let l_imp = fvar Const.imp_lid (S.Delta_unfoldable 1) None in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          U.mk_app l_imp [S.as_arg (S.bv_to_name q)]]);
        S.bv_to_name wp])
    in
    U.abs (S.binders_of_list [ a; q; wp ]) body ret_tot_wp_a
  in
  let wp_assume = normalize_and_make_binders_explicit wp_assume in
  check "wp_assume" (U.abs binders wp_assume None);

  let tforall = U.mk_app (S.mk_Tm_uinst U.tforall [ U_unknown ]) [ S.as_arg unknown ] in

  (* val st2_close_wp : heap:Type -> a:Type -> b:Type ->
                        f:(b->Tot (st2_wp heap a)) ->
                        Tot (st2_wp heap a)
    let st2_close_wp heap a b f = st2_app (st2_pure l_Forall) (st2_push f) *)
  let wp_close =
    let b = S.gen_bv "b" None U.ktype in
    let t_f = U.arrow [ S.null_binder (S.bv_to_name b) ] (S.mk_Total wp_a) in
    let f = S.gen_bv "f" None t_f in
    let body =
      U.mk_app c_app (List.map S.as_arg [
        unknown; unknown;
        U.mk_app c_pure (List.map S.as_arg [
          unknown;
          tforall]);
        U.mk_app c_push (List.map S.as_arg [
          unknown; unknown;
          S.bv_to_name f])])
    in
    U.abs (S.binders_of_list [ a; b; f ]) body ret_tot_wp_a
  in
  let wp_close = normalize_and_make_binders_explicit wp_close in
  check "wp_close" (U.abs binders wp_close None);

  let ret_tot_type0 = Some (Inl (U.lcomp_of_comp <| S.mk_Total U.ktype0)) in
  let mk_forall (x: S.bv) (body: S.term): S.term =
    let tforall = U.mk_app (S.mk_Tm_uinst U.tforall [ U_unknown ]) [ S.as_arg x.sort ] in
    S.mk (Tm_app (tforall, [ S.as_arg (U.abs [ S.mk_binder x ] body ret_tot_type0)])) None Range.dummyRange
  in

  (* For each (target) type t, we define a binary relation in t called ≤_t.

      x ≤_t y            =def=       x = y      [t is base type]
      x ≤_Type0 y        =def=       x ==> y
      x ≤_{a->b} y       =def=   ∀a1 a2, a1 ≤_a a2 ==> x a1 ≤_b y a2
  *)
  (* Invariant: [x] and [y] have type [t] *)
  let rec mk_leq t x y =
    match (normalize (SS.compress t)).n with
    | Tm_type _ ->
        (* Util.print2 "type0, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        U.mk_imp x y
    | Tm_arrow ([ binder ], { n = GTotal b })
    | Tm_arrow ([ binder ], { n = Total b }) when S.is_null_binder binder ->
        let a = (fst binder).sort in
        (* Util.print2 "arrow, a=%s, b=%s\n" (Print.term_to_string a) (Print.term_to_string b); *)
        let a1 = S.gen_bv "a1" None a in
        let a2 = S.gen_bv "a2" None a in
        let body = U.mk_imp
          (mk_leq a (S.bv_to_name a1) (S.bv_to_name a2))
          (mk_leq b
            (U.mk_app x [ S.as_arg (S.bv_to_name a1) ])
            (U.mk_app y [ S.as_arg (S.bv_to_name a2) ]))
        in
        mk_forall a1 (mk_forall a2 body)
    | Tm_arrow (binder :: binders, comp) ->
        let t = { t with n = Tm_arrow ([ binder ], S.mk_Total (U.arrow binders comp)) } in
        mk_leq t x y
    | Tm_arrow _ ->
        failwith "unhandled arrow"
    | _ ->
        (* TODO: assert that this is a base type. *)
        (* Util.print2 "base, x=%s, y=%s\n" (Print.term_to_string x) (Print.term_to_string y); *)
        U.mk_eq t t x y
  in
  let stronger =
    let wp1 = S.gen_bv "wp1" None wp_a in
    let wp2 = S.gen_bv "wp2" None wp_a in
    let body = mk_leq wp_a (S.bv_to_name wp1) (S.bv_to_name wp2) in
    U.abs (S.binders_of_list [ wp1; wp2 ]) body ret_tot_type0
  in
  check "stronger" (U.abs (binders @ [ S.mk_binder a ]) stronger None);

  let null_wp = snd ed.null_wp in

  (* val st2_trivial : heap:Type ->a:Type -> st2_wp heap a -> Tot Type0
    let st2_trivial heap a wp = st2_stronger heap a (st2_null_wp heap a) wp *)
  let wp_trivial =
    let wp = S.gen_bv "wp" None wp_a in
    let body = U.mk_app stronger (List.map S.as_arg [
      U.mk_app null_wp [ S.as_arg (S.bv_to_name a) ];
      S.bv_to_name wp
    ]) in
    U.abs (S.binders_of_list [ a; wp ]) body ret_tot_type0
  in
  let wp_trivial = normalize_and_make_binders_explicit wp_trivial in
  check "wp_trivial" (U.abs binders wp_trivial None);

  { ed with
    if_then_else = ([], wp_if_then_else);
    assert_p     = ([], wp_assert);
    assume_p     = ([], wp_assume);
    close_wp     = ([], wp_close);
    trivial      = ([], wp_trivial)
  }


// N-arrows are "normal" arrows of pure computations. T-arrows are arrows that
// denote effectful computations (terminology from the paper).
type n_or_t =
  | N of typ
  | T of typ

let is_monadic = function
  | None ->
      failwith "un-annotated lambda?!"
  | Some (Inl { eff_name = lid }) | Some (Inr lid) ->
      lid_equals lid Const.monadic_lid

let is_monadic_arrow n =
  match n with
  | Tm_arrow (_, { n = Comp c}) when lid_equals c.effect_name Const.monadic_lid ->
      T c.result_typ
  | Tm_arrow (_, { n = Total t}) ->
      N t
  | Tm_arrow _ ->
      raise (Err "Prims.M and Prims.Tot are the only possible effects in the \
        definition language")
  | _ ->
      failwith "unexpected_argument: [is_monadic_arrow]"

// The star-transformation from the POPL'17 submission, for types. The
// definition language is stratified, so there's two separate functions for
// types and terms. Some checks are intertwined with the *-transformation,
// eventually, these should be performed in a proper type-checker.
let rec mk_star_to_type mk a =
  mk (Tm_arrow (
    [S.null_bv (star_type a), S.as_implicit false],
    mk_Total Util.ktype
  ))

and star_type t =
  let mk x = mk x None t.pos in
  let mk_star_to_type = mk_star_to_type mk in
  let t = SS.compress t in
  match t.n with
  | Tm_arrow (binders, _) ->
      // N-arrows and T-arrows
      let binders = List.map (fun (bv, aqual) ->
        { bv with sort = star_type bv.sort }, aqual
      ) binders in
      begin match is_monadic_arrow t.n with
      | N hn ->
          (* Simple case:
           *   (H_0  -> ... -> H_n)* =
           *    H_0* -> ... -> H_n*
           *)
          mk (Tm_arrow (binders, mk_Total (star_type hn)))
      | T a ->
          (* F*'s arrows are n-ary (and the intermediary arrows are pure), so the rule is:
           *   (H_0  -> ... -> H_n  -t-> A)* =
           *    H_0* -> ... -> H_n* -> (A* -> Type) -> Type
           *)
          mk (Tm_arrow (
            binders @ [ S.null_bv (mk_star_to_type a), S.as_implicit false ],
            mk_Total Util.ktype))
      end

  | Tm_app (head, args) ->
      // Sums and products
      let rec is_valid_application head =
        match (SS.compress head).n with
        | Tm_fvar fv when (
          // TODO: implement a better check (non-dependent, user-defined data type)
          fv_eq_lid fv Const.option_lid ||
          fv_eq_lid fv Const.either_lid ||
          is_tuple_constructor (SS.compress head)
        ) ->
            true
        | Tm_uinst (head, _) ->
            is_valid_application head
        | _ ->
            false
      in
      if is_valid_application head then
        mk (Tm_app (head, List.map (fun (t, qual) -> star_type t, qual) args))
      else
        raise (Err (Util.format1 "For now, only [either] and [option] are \
          supported in the definition language (got: %s)"
            (Print.term_to_string t)))

  | Tm_bvar _
  | Tm_name _
  | Tm_type _ // TODO check
  | Tm_fvar _ ->
      t

  | Tm_abs _
  | Tm_uinst _
  | Tm_constant _
  | Tm_refine _
  | Tm_match _
  | Tm_ascribed _
  | Tm_let _
  | Tm_uvar _
  | Tm_meta _
  | Tm_unknown ->
      raise (Err (Util.format1 "The following term is outside of the definition language: %s"
        (Print.term_to_string t)))

  | Tm_delayed _ ->
      failwith "impossible"

// The star-transformation, for expressions. The transformation is syntax-directed
// (following the paper) and type-directed. The concrete implementation strategy is
// as follows:
//   - [let x = e1 in e2] where [e1] has type [M _] is understood to be
//     [bind e1 (fun x -> e2)] and is translated accordingly
//   - [let x = e1 in e2] is understood to be a regular let-binding and is
//     translated as [let x = e1* in e2*]
//   - [match e0 with xi -> ei] where [e0] has type [M _] is an error (todo:
//     rewrite as [let y = e0 in match y with ...])
//   - [match e0 with xi -> ei] is translated as [match e0* with xi -> ei*]
//   - for all other expressions: if the type provided from the context is [M _]
//     then this is understood to be a [return], otherwise, recursively descend
type mode = | InMonad of typ | InPure

let wrap_if (m: mode) (e: term) =
  let mk x = mk x None e.pos in
  let mk_star_to_type = mk_star_to_type mk in
  match m with
  | InPure ->
      e
  | InMonad t ->
      let p_type = mk_star_to_type t in
      let p = S.gen_bv "p" None p_type in
      let body = mk (Tm_app (mk (Tm_bvar p), [ e, S.as_implicit false ])) in
      U.abs [ S.mk_binder p ] body None

let rec star_expr (e: term) (m: mode) =
  let mk x = mk x None e.pos in
  let mk_star_to_type = mk_star_to_type mk in
  match (SS.compress e).n with
  | Tm_let ((false, [ binding ]), e2) ->
      let is_monadic = lid_equals binding.lbeff Const.monadic_lid in
      let e1 = binding.lbdef in
      // This is [let x = e1 in e2]. Open [x] in [e2].
      let x = Util.left binding.lbname in
      let x_binders = [ S.mk_binder x ] in
      let x_binders, e2 = SS.open_term x_binders e2 in
      // Two cases.
      if is_monadic then begin
        match m with
          | InPure ->
              raise (Err ("monadic [let] in a context that does not return [M]"))
          | InMonad t ->
              // p: A* -> Type
              let p_type = mk_star_to_type t in
              let p = S.gen_bv "p" None p_type in
              // e1*
              let e1 = star_expr e1 InPure in
              // e2*
              let e2 = star_expr e2 m in
              // e2* p
              let e2 = mk (Tm_app (e2, [ mk (Tm_bvar p), S.as_implicit false ])) in
              // fun x -> e2* p; this takes care of closing [x].
              let e2 = U.abs x_binders e2 None in
              // e1* (fun x -> e2* p)
              let body = mk (Tm_app (e1, [ e2, S.as_implicit false ])) in
              U.abs [ S.mk_binder p ] body None
      end else
        let e1 = star_expr e1 InPure in
        let e2 = star_expr e2 InPure in
        mk (Tm_let ((false, [ { binding with lbdef = e1 } ]), SS.close x_binders e2))

  | Tm_let _ ->
      raise (Err ("[let rec] and [let and] not supported in the definition
        language"))

  | Tm_abs (binders, body, what) ->
      // OPEN ALL THE THINGS
      let binders = SS.open_binders binders in
      let subst = SS.opening_of_binders binders in
      let body = SS.subst subst body in

      let ret_type =
        (* match (SS.compress t).n with
        | Tm_arrow (binders, comp) ->
            let binders, comp = open_comp binders comp in
            begin match comp.n with
            | Total t | GTotal t | Comp { result_typ = t } ->
                t
            end *)
        match what with
        | Some (Inl { res_typ = t }) ->
            t
        | _ ->
            failwith "what impossible"
      in

      let binders = List.map (fun (bv, qual) ->
        let sort = star_type bv.sort in
        { bv with sort = sort }, qual
      ) binders in
      let body = star_expr body (if is_monadic what then InMonad ret_type else InPure) in
      let body = close binders body in
      let binders = close_binders binders in
      wrap_if m (mk (Tm_abs (binders, body, what)))

  | Tm_ascribed (e, _, _) ->
      star_expr e m

  | Tm_match (e0, branches) ->
      // TODO: currently, no one is checking that [e0] is a pure computation
      let e0 = star_expr e0 InPure in
      let branches = List.map (fun b ->
        match open_branch b with
        | pat, None, body ->
            let body = star_expr body m in
            close_branch (pat, None, body)
        | _ ->
            raise (Err ("No when clauses in the definition language"))
      ) branches in
      mk (Tm_match (e0, branches))

  | Tm_app (head, args) ->
      // [args] cannot be monadic computations, because one cannot write in the
      // definition language a function that takes an [M t]... for [head], the
      // type-checking rules of the definition language will disallow it
      let head = star_expr head InPure in
      let args = List.map (fun (arg, qual) -> star_expr arg InPure, qual) args in
      let t = mk (Tm_app (head, args)) in
      wrap_if m t

  | Tm_bvar _
  | Tm_name _
  | Tm_fvar _ ->
      wrap_if m e

  | Tm_uinst _ ->
      failwith "TODO: Tm_uinst"
  | Tm_constant _ ->
      failwith "TODO: Tm_constant"
  | Tm_type _ ->
      failwith "TODO: Tm_type"
  | Tm_arrow _ ->
      failwith "TODO: Tm_arrow"
  | Tm_refine _ ->
      failwith "TODO: Tm_refine"
  | Tm_uvar _ ->
      failwith "TODO: Tm_uvar"
  | Tm_meta _ ->
      failwith "TODO: Tm_meta"
  | Tm_unknown ->
      failwith "TODO: Tm_unknown"

  | Tm_delayed _ ->
      failwith "Impossible"

let star_expression (e: term) (t: typ) =
  // Actually, can't use [t] here, because the type-checking routine reduces the
  // return type and the [M] disappears; instead, check the [Tm_abs] node which
  // seems more reliable
  match (SS.compress e).n with
  | Tm_abs (_, _, what) ->
      if is_monadic what then
        star_expr e InPure
      else
        raise (Err (Util.format2 "The following effect combinator should return in [M]: %s; \
          instead, it has type: %s\n" (Print.term_to_string e) (Print.term_to_string t)))
  | _ ->
      failwith "Not an arrow?!"