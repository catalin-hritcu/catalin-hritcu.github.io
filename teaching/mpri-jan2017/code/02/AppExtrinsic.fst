module AppExtrinsic

open FStar.List.Tot

let rec append (#a:Type) (xs : list a) (ys : list a) : Tot (list a) =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

let rec append_length (#a:Type) (xs : list a) (ys : list a) : Pure unit
    (requires True)
    (ensures (fun _ -> length (append xs ys) = length xs + length ys)) =
  match xs with
  | [] -> ()
  | x :: xs' -> append_length xs' ys

let rec append_length_lemma (#a:Type) (xs : list a) (ys : list a) : Lemma
    (ensures (length (append xs ys) = length xs + length ys)) =
  match xs with
  | [] -> ()
  | x :: xs' -> append_length xs' ys
