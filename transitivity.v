Require Import PeanoNat.
Local Open Scope nat_scope.
From Coq Require Import Bool String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import calculus.

(* =================== Helpers =================== *)

(* Lemma all_sub_nil: forall K rt,
  wf_typ K (typ_record rt) -> 
  subtype K (typ_record rt) (typ_record nil).
Proof. 
  intros. induction rt.
  - econstructor; eauto.
  - inversion H; subst. eapply sub_rec; auto.
    intros. inversion H0.
Qed.

Lemma rec_supertype: forall K T rt,
  subtype K (typ_record rt) T -> 
  exists rt', T = (typ_record rt').
Proof. 
  intros. remember (typ_record rt) as RT.
  generalize dependent rt.
  induction H. all: intros. all: try solve [inversion HeqRT].
  - exists rt. auto.
  - exists rj. eauto.
Qed.

Lemma nil_supertype: forall K rt,
  subtype K (typ_record nil) (typ_record rt) -> rt = nil.
Proof.
  intros. remember (typ_record rt) as RT.
  remember (typ_record nil) as RNIL. generalize dependent rt. 
  induction H. all: intros.
  - subst. inversion HeqRT; auto.
  - inversion HeqRT.
  - inversion HeqRNIL.
  - inversion HeqRNIL; subst. inversion HeqRT; subst.
     destruct rt; auto.
     destruct p as (s, Ts). assert (W: set_In (s, Ts) ((s, Ts) :: rt)).
     simpl; auto. apply H in W. inversion W as [Tt [set sub]].
     inversion set.
Qed. *)

(* =================== Inversion Lemmas ===================*)

Theorem inv_subtype_nat: forall K T,
  subtype K T typ_nat -> T = typ_nat.
Proof.
  intros. remember typ_nat as T'.
  induction H; auto. all: try solve [inversion HeqT'].
  - subst. assert (W: typ_record typdef = typ_nat). auto.
     inversion W.
Qed.

Theorem inv_subtype_bool: forall K T,
  subtype K T typ_bool -> T = typ_bool.
Proof.
  intros. remember typ_bool as T'.
  induction H; auto. all: try solve [inversion HeqT'].
  - subst. assert (W: typ_record typdef = typ_bool). auto.
      inversion W.
Qed.

Theorem inv_subtype_path: forall K T a R,
  subtype K T (typ_path a R) -> T = (typ_path a R).
Proof.
  intros. remember (typ_path a R) as T'.
  induction H; auto. all: try solve [inversion HeqT'].
  - subst. assert (W: typ_record typdef = (typ_path a R)). auto.
      inversion W.
Qed.

(* every subtype of an arrow type is an arrow type *)
Theorem inv_subtype_arrow: forall K S'' T T',
  subtype K S'' (typ_arrow T T') ->
  (exists S S', S'' = (typ_arrow S S') /\ subtype K T S /\ subtype K S' T').
Proof. 
  intros. remember (typ_arrow T T') as T''.
  generalize dependent T'. generalize dependent T.
  induction H; auto. all: intros.
  all: try solve [inversion HeqT''].
  - exists T0, T'. repeat split; auto; econstructor.
  - exists T1, T1'. split; auto. inversion HeqT''; subst.
     split; auto.
  - eapply IHsubtype in HeqT''. destruct HeqT'' as [Si [Si' [Hi Hi']]].
     inversion Hi.
Qed.

(* every subtype of a record type is a record type or a path type *)
Theorem inv_subtype_record: forall K T rj,
  subtype K T (typ_record rj) ->
  (exists ri, T = (typ_record ri) /\ 
      (forall fj Tj, set_In (fj, Tj) rj -> (exists T, set_In (fj, T) ri /\ subtype K T Tj))) 
  \/ 
  (exists a R L typdef, 
    T = (typ_path a R) /\ 
    wf_path K a /\ link_comp_ex a L /\ set_In (R, Equal, typdef) L.(types) /\ 
    subtype K (typ_record typdef) (typ_record rj)).
Proof. 
  intros. remember (typ_record rj) as RT.
  generalize dependent rj.
  induction H.
  4: { intros. inversion HeqRT; clear HeqRT. subst.
        left. exists ri. repeat split; try auto. }
  - left. exists rj. repeat split; try auto.
    intros. exists Tj. split; auto. econstructor.
  - intros. inversion HeqRT.
  - intros. right. exists a, R, L, typdef. split; auto.
Qed.


Lemma transitivity_of_subtyping: forall K T1 T2 T3, 
  subtype K T1 T2 -> subtype K T2 T3 -> subtype K T1 T3.
Proof. intros. generalize dependent T1. generalize dependent T3.
  induction T2 using typ_ind; intros.
  - apply inv_subtype_nat in H; subst. inversion H0. econstructor.
  - apply inv_subtype_bool in H; subst. inversion H0. econstructor.
  - apply inv_subtype_path in H; subst. auto.
  - apply inv_subtype_arrow in H. 
    destruct H as [T1in [T1out [Hx [Hy Hz]]]].
    inversion H0; subst.
    + econstructor; eauto.
    + econstructor; eauto.
  - inversion H0; subst; eauto.
    apply inv_subtype_record in H1; eauto.
    inversion H1; clear H1; subst.
    + inversion H2 as [ri [HT1 HT2]]; subst. clear H2.
      econstructor; eauto. intros. eapply H3 in H1.
      inversion H1 as [Tx [X Y]]. 
      assert (V: exists T : typ, set_In (fj, T) ri /\ subtype K T Tx).
      eapply HT2 in X; eauto.
      inversion V as [Tz [Z W]]. exists Tz. split; eauto.
    + inversion H2 as [a [R [L [typdef X]]]]; subst. clear H2.
      inversion X as [HTx [HWF [HLINK [HSET HSUB]]]]. subst.
      clear X. econstructor; eauto.
      (* now, it's just subtyping of records *)
      inversion HSUB; subst; eauto.
      econstructor; eauto. 
      intros. eapply H3 in H1.
      inversion H1 as [Tx [X Y]]. 
      assert (V: exists T : typ, set_In (fj, T) typdef /\ subtype K T Tx).
      apply H4 in X; eauto.
      inversion V as [Tt [Hset Hsub]].
      exists Tt; split; eauto.
Qed.