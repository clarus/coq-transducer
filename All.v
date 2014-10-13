Require Import Coq.Lists.List.
Require Import FunCombinators.All.

Import ListNotations.
Local Open Scope list.

Module Red.
  Definition t (A B : Type) : Type := A -> B -> A.
End Red.

Module List.
  Fixpoint fold {A B : Type} (a : A) (red : Red.t A B) (l : list B) : A :=
    match l with
    | [] => a
    | x :: l => fold (red a x) red l
    end.

  Definition cons {A : Type} (a : list A) (x : A) : list A :=
    x :: a.
End List.

Definition map {A B C : Type} (f : B -> C) (red : Red.t A C) : Red.t A B :=
  fun a x =>
    red a (f x).

Definition filter {A B : Type} (f : B -> bool) (red : Red.t A B) : Red.t A B :=
  fun a x =>
    if f x then
      red a x
    else
      a.

Definition take {A B : Type} (red : Red.t A B) : A * nat -> B -> A * nat :=
  fun a x =>
    match a with
    | (a, S n) => (red a x, n)
    | (a, O) => (a, O)
    end.  

Definition transduce {A B C D : Type} {T : Type -> Type}
  (transducer : Red.t C D -> Red.t A B) (red : Red.t C D) (a : A)
  (fold : A -> Red.t A B -> T B -> A) (stream : T B) : A :=
  fold a (transducer red) stream.


Module Test.
  Definition l := [Some 1; None; Some 2; Some 3].

  Definition of_option n :=
    match n with
    | None => 1
    | Some n => n
    end.

  Definition is_some {A : Type} (x : option A) : bool :=
    match x with
    | None => false
    | Some _ => true
    end.

  Compute l |> List.fold 0 (map of_option plus).
  Compute l |> List.fold 0 (plus |> map of_option |> filter is_some).
  Compute l |> List.fold (0, 3) (plus |> map of_option |> filter is_some |> take).
  Compute l |> List.fold ([], 3) (List.cons |> map of_option |> filter is_some |> take).

  Compute transduce (map of_option) plus 0 List.fold l.
  Compute [1; 2; 3] |> List.fold 0 plus.
  Compute [1; 2; 3] |> List.fold 0 (map S plus).
  Compute l |> List.fold (0, 3) (
    take @@
    filter is_some @@
    map of_option @@
    map S @@
    plus).
End Test.