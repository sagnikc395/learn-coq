Inductive bool :=
| true 
| false.

(* negation funciton*)
(*
when we are doing pattern matching in coq, 
we need to give all the constructor functions
    *)
Definition negb (b: bool): bool :=
    match b with
    | true => false 
    | false => true
    end.

(* basic evaluation criteria*)
Eval compute in negb (negb true).

(* can prove properties about our evaluation using this*)

(* taking any boolean value b and apply any negation value on this, it will remain the same*)
(*
negb (negb b) = b 
*)
Theorem negb_proof1: forall (b: bool), negb(negb b) = b.
(* now writing the proof of the same*)
Proof.
    (*assume arbitary boolean value and puts it at the top of the line*)
    intros b.
    (* destructing b and get the value*)
    destruct b.
    (* now 2 statements are there to be proofed, negation and negation of true is true*)
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.


(* trying to prove something that is false*)
(*Theorem i_belive_its_true: forall (b: bool),negb b = b.
(* trying to prove this *)
Proof.
    intros b.
    destruct b.
    (* anything which is false, is getting proved true here*)
    (*+ simpl. *)
    *)

Theorem negb_negb: forall (b: bool), negb (negb b) = b.
Proof.
    intros b.
    destruct b.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.


(* taking negation three times*)
Theorem negb_thrice: forall (b: bool), negb (negb (negb b)) = negb b.
Proof.
    (* coming up with statements here needs to check and the datatype and what property it holds*)
    intros b.
    (* destruct into types for b *)
    destruct b.
    (* simplification and reflexivity check*)
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Definition andb (b1 b2: bool): bool := 
    (* function definition for boolean and operation*)
    match b1,b2 with 
    | true,true => true 
    (* | false, true => false
    | true, false => false 
    | false, false => false
     other cases are all false so we can do as *)
    | _,_ => false
    end. 
(* these are literally assiting us whenever if we miss a case *)


Definition orb (b1 b2 : bool): bool :=
    match b1, b2 with 
    | true,true => true
    | false,false => false
    | true, false =>true
    | false,true => true 
    end.

(* for all arbitary values of types bool, if b1 is true and b2 is true , then the whole expression will be true *)
Theorem andb_true_both_arg_true: forall (b1 b2: bool),
    b1 = true -> b2 = true -> andb b1 b2 = true.
Proof.
    (* set up hypothesis *)
    intros b1 b2 Hb1 Hb2.
    destruct b1.
    destruct b2.
    + simpl. reflexivity.
    + simpl. inversion Hb2.
    + destruct b2.
      ++ simpl. inversion Hb1.
      ++ simpl. inversion Hb1.
Qed.

(* in a more simpler way*)
Theorem andb_true_both_arg_true_v2: forall (b1 b2: bool),
b1 = true -> b2 = true -> andb b1 b2 = true.
Proof.
    intros b1 b2 Hb1 Hb2.
    (* replace left side with true *)
    rewrite Hb1.
    rewrite Hb2.
    simpl. reflexivity.
Qed. 
(* /\ -> & symbol*)
Theorem andb_true_otherside: forall(b1 b2: bool),
    andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
    intros b1 b2 Hb.
    destruct b1.
    destruct b2.
    (* split gives us 2 ands in our goal -> and breaks them into 2 goals*)
    split. reflexivity.
    reflexivity.
    (* now goal 1 is false = true which we can't prove*)
    split. reflexivity.
    simpl in Hb.
    inversion Hb.
    destruct b2.
    simpl in Hb.
    inversion Hb.
    simpl in Hb.
    inversion Hb.
Qed.
