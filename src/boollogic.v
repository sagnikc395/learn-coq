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



