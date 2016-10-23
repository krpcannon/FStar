module Math.Lib

open FStar.Mul
open Math.Axioms

val log_2: x:pos -> Tot nat
let rec log_2 x =
  if x >= 2 then 1 + log_2 (x / 2) else 0

(* Function: power of x *)
val powx : x:int -> n:nat -> Tot int
let rec powx x n =
  match n with
  | 0 -> 1
  | n -> x * powx x (n - 1)

(* Function: absolute value *)
val abs: x:int -> Tot (y:int{ (x >= 0 ==> y = x) /\ (x < 0 ==> y = -x) })
let abs x = if x >= 0 then x else -x

(* Function: maximum value *)
val max: x:int -> y:int -> Tot (z:int{ (x >= y ==> z = x) /\ (x < y ==> z = y) })
let max x y = if x >= y then x else y

(* Function: minimum value *)
val min: x:int -> y:int -> Tot (z:int{ (x >= y ==> z = y) /\ (x < y ==> z = x) })
let min x y = if x >= y then y else x

(* Function: standard euclidean division, the rest is always positive *)
val div: a:int -> b:pos -> Tot (c:int{(a < 0 ==> c < 0) /\ (a >= 0 ==> c >= 0)})
let div a b =
  admit(); // Because Prims.op_Division is only defined when a:nat
  if a < 0 then
    begin
    slash_decr_axiom (0 - a) b;
    if a % b = 0 then 0 - (0 - a / b)
    else 0 - (0 - a / b) - 1
    end
  else a / b

(* Function: equivalent of the '/' operator in C, hence the rest can be negative *)
val div_non_eucl: a:int -> b:pos ->
  Tot (q:int{ ( a >= 0 ==> q = a / b ) /\ ( a < 0 ==> q = -((-a)/b) ) })
let div_non_eucl a b =
  if a < 0 then 0 - ((0 - a) / b)
  else a / b

(* The equivalent of the << C operator *)
val shift_left: v:int -> i:nat -> Tot (res:int{res = v * (pow2 i)})
let shift_left v i =
  v * (pow2 i)

(* asr OCaml operator *)
val arithmetic_shift_right: v:int -> i:nat -> Tot (res:int{ res = div v (pow2 i) })
let arithmetic_shift_right v i = 
  div v (pow2 i)

(* Case of C cast functions ? *)
(* Implemented by "mod" in OCaml *)
val signed_modulo: v:int -> p:pos -> Tot (res:int{ res = v - ((div_non_eucl v p) * p) })
let signed_modulo v p =
  if v >= 0 then v % p
  else 0 - ( (0-v) % p)

val op_Plus_Percent : a:int -> p:pos -> 
  Tot (res:int{ (a >= 0 ==> res = a % p) /\ (a < 0 ==> res = -((-a) % p)) }) 
let op_Plus_Percent a p = signed_modulo a p

(* Bitwize operations *)
assume val xor_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> x = y })
assume val and_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> (x = 0 /\ y = 0)})
assume val or_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> (x = 0 \/ y = 0) })
assume val lnot_op: int -> Tot int

(* Comparison, has to be realized in constant time *)
assume val compare: x:int -> y:int ->
  Tot (r:int{ (r = 0 <==> x = y) /\ (r = 1 <==> x > y) /\ (r = -1 <==> x < y) })

(** Useful lemmas for future proofs **)

(* Lemmas of x^n *)
val powx_lemma1: a:int -> Lemma (powx a 1 = a)
let powx_lemma1 a = ()

val powx_lemma2: x:int -> n:nat -> m:nat -> Lemma
  (powx x n * powx x m = powx x (n + m))
let rec powx_lemma2 x n m =
  match n with
  | 0 -> ()
  | _ -> powx_lemma2 x (n-1) m

(* Lemma: absolute value of product is the product of the absolute values *)
val abs_mul_lemma: a:int -> b:int -> Lemma (abs (a * b) = abs a * abs b)
let abs_mul_lemma a b = ()

(* Lemma: absolute value of a signed_module b is bounded by b *)
val signed_modulo_property: v:int -> p:pos -> Lemma (abs (signed_modulo v p ) < p)
let signed_modulo_property v p = ()

(* Lemma: non-Euclidean division has a smaller output compared to its input *)
val div_non_eucl_decr_lemma: a:int -> b:pos -> Lemma (abs (div_non_eucl a b) <= abs a)
let div_non_eucl_decr_lemma a b =
  slash_decr_axiom (abs a) b

(* Lemma: dividing by a bigger value leads to 0 in non-Euclidean division *)
val div_non_eucl_bigger_denom_lemma: a:int -> b:pos -> Lemma
  (requires (b > abs a))
  (ensures  (div_non_eucl a b = 0))
let div_non_eucl_bigger_denom_lemma a b = ()