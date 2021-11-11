## F* as a proof assistant ## {#proofs}
* Type theoretic foundations:
  - dependent types, inductive types, universes
    (like Coq, Agda, ...)
* Intrinsic, extrinsic, and constructive proof styles
  - intrinsic = one specification chosen at definition time&br;
    (e.g. pre-post condition)
  - extrinsic = lemmas proved after definition time
    + can do this for any *terminating* computation

Related tools: Coq, Isabelle, HOL4, ACL2, PVS, Agda
{.fragment}

## Quicksort ## {#qsc}

~Fragment
```
val quicksort: #a:Type -> f:(a -> a -> Tot bool){total_order a f} ->
    l:list a -> Tot (m:(list a){sorted f m /\ forall i. count i l = count i m})
      (decreases (length l))
```
~
<!-- TODO: syntax highlighting for types a total mess -->

```
open List
let rec quicksort f l =
  match l with
  | [] -> []
  | pivot::tl -> let hi, lo = partition (f pivot) tl in 
                 append (quicksort f lo) (pivot::quicksort f hi)
```

~Fragment
The `List` library contains:

```
val partition: #a:Type -> (a -> Tot bool) -> list a -> Tot (list a * list a)
val append:    #a:Type -> list a -> list a -> Tot (list a)
```
~

## Spec helpers are just total functions ## {#qsc-helpers}

```
val sorted: #a:Type -> (a -> a -> Tot bool) -> list a -> Tot bool
let rec sorted f l =
  match l with
  | x::y::tl -> f x y && sorted f (y::tl)
  | _ -> true
  
val count: #a:Type -> a -> list a -> Tot nat
let count x l =
  match l with
  | [] -> 0 
  | hd::tl -> if hd=x then 1 + count x tl else count x tl
```

```
type total_order (a:Type) (f: (a -> a -> Tot bool)) =
     (forall a. f a a)                                  (* reflexivity   *)
  /\ (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2)  (* anti-symmetry *)
  /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)  (* transitivity  *)
  /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                 (* totality  *)
```

## Are we done? ##
```
val quicksort: #a:Type -> f:(a -> a -> Tot bool){total_order a f} ->
    l:list a -> Tot (m:(list a){sorted f m /\ forall i. count i l = count i m})
      (decreases (length l))
```
```
open List
let rec quicksort f l =
  match l with
  | [] -> []
  | pivot::tl -> let hi, lo = partition (f pivot) tl in 
                 append (quicksort f lo) (pivot::quicksort f hi)
```

~Fragment {.console}
``` html
Subtyping check failed; 
  expected type lo:list a{ %[length lo] << %[length l] }; 
  got type (list a) (qsc.fst(99,19-99,21))
```
~

## Lemmas (extrinsic proofs) ##
```
val partition_lemma: f:('a -> Tot bool) -> l:list 'a -> Lemma (requires True)
      (ensures (forall hi lo. (hi, lo) = partition f l
                ==> (length l = length hi + length lo
                 /\ (forall x. (mem x hi ==> f x)
                            /\ (mem x lo ==> not (f x))
                            /\ (count x l = count x hi + count x lo)))))
      [SMTPat (partition f l)]
let rec partition_lemma f l = match l with
    | [] -> ()
    | hd::tl -> partition_lemma f tl
```
~Fragment {.console}
``` html
mono ../../bin/fstar.exe --fstar_home ../..  ../../lib/list.fst qsc.fst
Verified module: Prims
Verified module: List
Verified module: QuickSort
All verification conditions discharged successfully
```
~

## A gentle introduction to F* basics ## {#gentle}
* Following part of the [F* tutorial] today
  - Structure of a file, modules
  - Pure, Tot, Lemma (stripped 2.2, on board)
  - Function types (2.3, on board)
  - Nat, Factorial, Fibonacci (3.2)
  - Lemmas (3.3)
  - Admit (3.4) + assert (nowhere unfortunately)
  - Intrinsic vs. extrinsic proofs (4.2)
  - Defining List (4.0)
  - Append and mem (4.1)
  - Map, Find (4.3)
  - Discriminators and Projectors (4.4)

[F* tutorial]: https://www.fstar-lang.org/tutorial/tutorial.html


## Pure, Tot, Lemma, function types
* done on board ([part 1](http://prosecco.gforge.inria.fr/personal/hritcu/talks/fstar-sb-2015/stuff/20150316_115904.jpg), [part 2](http://prosecco.gforge.inria.fr/personal/hritcu/talks/fstar-sb-2015/stuff/20150316_115930.jpg))
* `Tot` and `Lemma` can be seen as abbreviations of `Pure`
```
Lemma t (requires r) (ensures e) = Pure unit (requires r) (ensures (fun _ -> e))
Tot t = Pure (requires True) (ensures True)
```
