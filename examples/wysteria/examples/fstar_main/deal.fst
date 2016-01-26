(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:FStar.Ghost.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.IO.fsti FStar.List.fst FStar.List.Tot.fst FStar.ListProperties.fst FStar.Relational.fst ordset.fsi ../../prins.fsi ../ffi.fst ../wysteria.fsi
 --*)

module SMC

open FStar.List
open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let charlie_s = singleton charlie
let ab = union alice_s bob_s
let bc = union bob_s charlie_s
let ac = union alice_s charlie_s
let abc = union ab charlie_s


type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

val check_fresh:
  l:list (Sh int){forall s. FStar.List.mem s l ==> ps_of_sh s = abc} -> s:Sh int{ps_of_sh s = abc}
  -> Wys bool (pre (Mode Par abc)) post
let rec check_fresh l s =
  if l = mk_nil () then true
  else
    let x = hd_of_cons l in

    let get_tmp: p:prin -> unit -> Wys int (pre (Mode Par (singleton p))) post =
      fun _ _ -> 2
    in
    let t1 = as_par alice_s (get_tmp alice) in
    let t2 = as_par bob_s (get_tmp bob) in
    let t3 = as_par charlie_s (get_tmp charlie) in

    let check_one: unit -> Wys bool (pre (Mode Sec abc)) post =
      fun _ ->
      let t1' = unbox_s t1 in
      let t2' = unbox_s t2 in
      let t3' = unbox_s t3 in
      let t4' = t1' > t2' in
      let t5' = t3' = t1' in
 
      let c1 = comb_sh x in
      let c2 = comb_sh s in
      c1 = c2
    in
    let b = as_sec abc check_one in
    if b then false
    else check_fresh (tl_of_cons l) s

val deal:
  ps:prins{ps = abc}
  -> shares:list (Sh int){forall x. FStar.List.mem x shares ==> ps_of_sh x = abc}
  -> rands:Wire int ps -> deal_to:prin
  -> Wys (list (Sh int) * int) (pre (Mode Par abc)) post
let deal ps shares rands deal_to =
  let proj: p:prin{FStar.OrdSet.mem p abc} -> unit
	    -> Wys int (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p rands
  in

  let r1 = as_par alice_s (proj alice) in
  let r2 = as_par bob_s (proj bob) in
  let r3 = as_par charlie_s (proj charlie) in

  let add: unit -> Wys (Sh int) (pre (Mode Sec abc)) (fun _ r _ -> b2t (ps_of_sh r = abc)) =
    fun _ ->
    let r1' = unbox_s r1 in
    let r2' = unbox_s r2 in
    let r3' = unbox_s r3 in
    let t1 = r1' + r2' in
    let t2 = t1 + r3' in
    mk_sh t2
  in

  (* shares of new card *)
  let new_sh = as_sec abc add in
  let fresh = check_fresh shares new_sh in

  if fresh then  
    let card: unit -> Wys int (pre (Mode Sec abc)) post =
      fun _ ->
      let r1' = unbox_s r1 in
      let r2' = unbox_s r2 in
      let r3' = unbox_s r3 in
      let t1 = r1' > r2' in
      let t2 = r3' = r1' in
      comb_sh new_sh
    in
    let c = as_sec abc card in
    mk_tuple (mk_cons new_sh shares) c
  else
    let x = 52 in
    mk_tuple shares 52

  

  (* let c = as_sec abc card in *)

  
  
  (* (mk_tuple (mk_cons new_sh shares)  *)

  (* let get_tmp: p:prin -> unit -> Wys int (pre (Mode Par (singleton p))) post = *)
  (*   fun _ _ -> 2 *)
  (* in *)

  (* let t1 = as_par alice_s (get_tmp alice) in *)
  (* let t2 = as_par bob_s (get_tmp bob) in *)
  (* let t3 = as_par charlie_s (get_tmp charlie) in *)

  (* let tmp: unit -> Wys (Sh int) (pre (Mode Sec abc)) (fun _ r _ -> b2t (ps_of_sh r = abc)) = *)
  (*   fun _ -> *)
  (*   let r1' = unbox_s r1 in *)
  (*   let r2' = unbox_s r2 in *)
  (*   let r3' = unbox_s r3 in *)
  (*   let _ = r1' > r2' in *)
  (*   let _ = r3' = r1' in *)
  (*   let t3 = unbox_s t1 in *)
  (*   mk_sh t3 *)
  (* in *)

  (* let new_sh' = as_sec abc tmp in *)

  (* let check_eq: unit -> Wys int (pre (Mode Sec abc)) post = *)
  (*   fun _ -> *)
  (*   let r1' = unbox_s r1 in *)
  (*   let r2' = unbox_s r2 in *)
  (*   let r3' = unbox_s r3 in *)
  (*   let t1 = r1' > r2' in *)
  (*   let t2 = r3' = r1' in *)
  (*   let t3 = comb_sh new_sh in *)
  (*   let t4 = comb_sh new_sh' in *)
  (*   t3 - t4 *)
  (* in *)
  (* let b = as_sec abc check_eq in *)
  (* b *)

  

  (* c *)
  (* let fresh = check_fresh shares new_sh in *)

  (* if fresh then mk_tuple (mk_cons new_sh shares) c *)
  (* else mk_tuple shares c *)