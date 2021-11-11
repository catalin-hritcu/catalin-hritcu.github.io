module AppIntrinsic

open FStar.List.Tot

let rec append (#a:Type) (xs : list a) (ys : list a) : Tot (list a) =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

let rec append' (#a:Type) (xs : list a) (ys : list a) : Pure (list a)
    (requires True) (ensures (fun zs -> length zs = length xs + length ys)) =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append' xs' ys
