module Sum

open FStar.ST
open FStar.Heap
open FStar.Mul

(* simplest version: counter *)

let rec count r (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> sel h1 r = sel h0 r + n)) = 
  if n > 0 then (r := !r + 1; count r (n-1))

let rec count' r (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> h1 `equal` upd h0 r (sel h0 r + n))) = 
  if n > 0 then (r := !r + 1; count' r (n-1))

(* simpler version *)

let rec sum_rec (n:nat) = if n > 0 then n + sum_rec (n-1) else 0

 let sum_tot n = (n * (n-1)) / 2 (* not so useful, only to specify sum_rec,
                                    but that's highly non-linear stuff *)
let rec sum_rec_correct (n:nat) :
    Lemma (sum_rec n = (if n = 0 then 0 else (n * (n-1)) / 2)) =
  match n with
  | 0 -> ()
  | _ -> admit() (* sum_rec_correct (n-1) *)

let rec sum r (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> sel h1 r == sel h0 r + sum_rec n)) = 
  if n > 0 then (r := !r + n; sum r (n-1))

let rec sum' r (n:nat) : ST unit (requires (fun h0 -> True))
    (ensures (fun h0 () h1 -> h1 `equal` upd h0 r (sel h0 r + sum_rec n))) =
  if n > 0 then (r := !r + n; sum' r (n-1))

(* fancier version *)

(* let sum_up_tot i lo hi = i + (lo - hi) * lo + ((hi - 1) * (hi - 2) / 2) *)

let rec sum_up_rec i lo hi : Pure int (requires (b2t (lo <= hi)))
                               (ensures (fun _ -> True)) (decreases (hi - lo)) =
  if lo < hi then lo + (sum_up_rec i (lo + 1) hi) else i

let rec sum_up r lo hi : ST unit (requires (fun _ -> True))
    (ensures (fun h0 () h1 -> if lo < hi
                              then h1 `equal` upd h0 r (sum_up_rec (sel h0 r) lo hi)
                              else h1 `equal` h0)) =
  if lo < hi then (r := !r + lo; sum_up r (lo + 1) hi)
