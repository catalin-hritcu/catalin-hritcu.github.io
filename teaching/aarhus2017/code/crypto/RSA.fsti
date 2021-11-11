module RSA
open FStar.Mul

(*! 1. write a function that computes [g^e] naively *)

val pow: g:nat -> e:nat -> nat

// Test: evaluate pow 2 16

// A convenient notation [but it breaks proofs?]
// unfold let (^) = pow


(*! 2. prove [g^(e1 + e2) = g^e1 * g^e2] *)

val lemma_pow_add (g: nat) (e1 e2: nat): Lemma (pow g (e1 + e2) = pow g e1 * pow g e2)

#set-options "--initial_fuel 1 --initial_ifuel 1"
let rec lemma_pow_add g e1 e2 =
  admit()

(*! 3. prove [(g^e1)^ e2 = g^(e1 * e2)] *)

val lemma_pow_mul (g:nat) (e1 e2:nat): Lemma (pow (pow g e1) e2 = pow g (e1 * e2))

let rec lemma_pow_mul g e1 e2 =
  admit()

(*! 4. Implement exponentiation by squaring using
       [ g^e = g^(e/2)^2]       when [g % 2 = 0]
       [ g^e = g*(x^(e-1)/2)^2] when [g % 2 = 1 ] *)

val fast_pow: nat -> nat -> nat

(*! 5. Prove that exponentiation by squaring is correct *)

val lemma_fast_pow (g:nat) (e:nat): Lemma (fast_pow g e = pow g e)

// You will need the lemmas from exercises 2 and 3
// Hint: think how to relate e to e/2 and e%2

let lemma_fast_pow g e =
  admit()

(*! 6. Extended Euclidean division. *)

// We aim to define a function [gcd: a:nat -> b:nat -> (u:int * v:int * gcd:nat)]
// such that [a*u + b*v = gcd] (by induction on b)
//
// [val gcd: a:nat -> b:nat -> (u:nat & v:nat & gcd:nat) { a*u + b*v = gcd }]

let rec gcd (a:nat) (b:nat): Tot _ (decreases b)
  =
  match b with
  | 0 -> (1, 0, a)
  | _ -> let (u, v, g) = gcd b (a % b) in (v, u - v * (a / b), g)

// Prove that this implementation is correct, that is:
// val lemma_gcd: a:nat -> b:nat -> Lemma
//   (let u, v, g = gcd a b in a*u+v*b = g)
// don't hesitate to split your proof into simpler sub-lemmas

let rec lemma_gcd (a:nat) (b:nat) : Lemma
  (requires True)
  (ensures (let u, v, g = gcd a b in a*u + b*v = g))
  (decreases b)
  =
  admit()

// Some useful types for elements of Z/nZ
type modulus = n:nat{n >= 2}
type elem (n:modulus) = e:nat{0 <= e /\ e < n}
type coprime (n:modulus) (e:elem n) =
  (let _, _, g = gcd n e in g = 1)
type inverse (n:modulus) (e:elem n{coprime n e}) (e':elem n) =
  (e * e') % n = 1

// 5c. Implement and prove the correctness of a function
// that computes the inverse of an element e in Z/nZ:
// val inverse: n:nat -> (e:elem n{coprime n e}) -> Tot (r:elem n{inverse n e r})
// For this proof you are allowed a couple admitted lemmas
// (they are proved in FStar.Math.Lemmas)
// Bonus points: prove those 2 lemmas

let lemma_inverse_1 (n:modulus) (x:int) (y:int)
  : Lemma ((n * x + y) % n = y % n)
  = admit()

let lemma_inverse_2 (n:modulus) (e:elem n) (x:int)
  : Lemma ((e * x) % n = (e * (x % n)) % n)
  = admit()

let get_inverse (n:modulus) (e:elem n{coprime n e})
  : Tot (e':elem n{inverse n e e'}) =
  admit()

// Primality is an abstract predicate
assume type prime (p:nat)
let phi (p:nat{p>2 /\ prime p}) (q:nat{q>2 /\ prime q}) : modulus = (p-1) * (q-1)

abstract type key = p:nat{p > 2 /\ prime p} & q:nat{q > 2 /\ prime q}
  & e:nat{e < phi p q /\ coprime (phi p q) e}

let group (k:key) : modulus = (let (|p, q, e|) = k in p*q)
let unitgroup (k:key) : modulus = (let (|p, q, e|) = k in phi p q)
let exponent (k:key) : e:elem (unitgroup k){coprime (unitgroup k) e} =
  let (|p, q, e|) = k in e

let encrypt (k:key) (m:elem (group k)) : elem (group k) =
  (fast_pow m (exponent k)) % (group k)

let decrypt (k:key) (m:elem (group k)) : elem (group k) =
  let d = get_inverse (unitgroup k) (exponent k) in
  (fast_pow m d) % (group k)

(*! 7. Prove that the above RSA implementation is correct
  (that is, decrypt k (encrypt k m) = m) using the provided
  formulation of Euler's theorem and the two provided lemmas
  from FStar.Math.Lemmas *)

val lemma_rsa_correct: k:key -> m:elem (group k) -> Lemma
  (decrypt k (encrypt k m) = m)

let lemma_euler (p:nat{p > 1 /\ prime p}) (q:nat{q > 1 /\ prime q}) (a:nat)
  : Lemma (pow a ((p-1)*(q-1)) % p*q = 1)
  = admit()

let lemma_pow_mod (n:modulus) (m:elem n) (e1 e2:nat)
  : Lemma (pow (pow m e1 % n) e2 % n = pow (pow m e1) e2 % n)
  = admit()

let lemma_mod_mul (n:modulus) (x y:nat)
  : Lemma ((x * y) % n = ((x % n) * (y % n)) % n)
  = admit()

let lemma_mod_trivial (n:modulus) (x:elem n)
  : Lemma (x % n = x)
  = ()

// Solution
let lemma_rsa_correct k m =
  let c = encrypt k m in
  let n = group k in
  let n' = unitgroup k in
  let e = exponent k in
  let d = get_inverse n' e in
  let (| p, q, _ |) = k in
  let plain = decrypt k c in
  admit()

type blinder (k:key) =
  (let (| p, q ,e |) = k in
  r:nat{r < p*q /\ coprime (p*q) r})

let blind (k:key) (r:blinder k) (m:elem (group k)) =
  (m * encrypt k r) % (group k)

let unblind (k:key) (r:blinder k) (p:elem (group k)) =
  (p * get_inverse (group k) r) % (group k)

(*! 8. Prove the correctness of blinded RSA signatures, that is,
  unblind k r (decrypt k (blind k r m)) = m
  For this proof, you are allowed to admit (or prove if you have time!)
  decrypt k ((m1 * m2) % (group k)) = (decrypt k m1 * decrypt k m2) % (group k)

  It is recommanded to first prove:
  unblind k r ((decrypt k m * r) % (group k)) = decrypt k m
*)

let rec lemma_decrypt (k:key) (m1 m2:elem (group k))
  : Lemma (decrypt k ((m1 * m2) % (group k)) = (decrypt k m1 * decrypt k m2) % (group k))
  = admit()

let lemma_unpad_decrypt (k:key) (r:blinder k) (m:elem (group k))
  : Lemma (unblind k r ((decrypt k m * r) % (group k)) = decrypt k m)
  =
  let n = group k in
  let n' = unitgroup k in
  let s = decrypt k m in
  let m' = unblind k r ((s * r) % n) in
  let r' = get_inverse n r in
  admit()


let lemma_blinding (k:key) (r:blinder k) (m:elem (group k))
  : Lemma (unblind k r (decrypt k (blind k r m)) = decrypt k m)
  =
  let n = group k in
  let b = blind k r m in
  let s = decrypt k b in
  admit()
