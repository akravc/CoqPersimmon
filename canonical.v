Require Import PeanoNat.
Local Open Scope nat_scope.
From Coq Require Import Bool String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import calculus.
Require Import transitivity.


Theorem canonical_fun: forall K G e T T', 
    has_typ K G e (typ_arrow T T') ->
    value e ->
    exists x S e', subtype K T S /\ (e = exp_lam x S e').
Proof.
    intros. 
    remember (typ_arrow T T') as tarr in *.
    generalize dependent T'. generalize dependent T.
    induction H; intros.
    all: try solve [inversion Heqtarr].
    all: try solve [inversion H0; eauto].
    - (* Lam case *)
      inversion Heqtarr; subst. 
      exists x, T0, e. split; eauto. 
      econstructor.
    - (* Subsumption case *)
      subst. apply inv_subtype_arrow in H1.
      inversion H1 as [S [S' [X [Y Z]]]]. clear H1.
      assert (W: forall T T'0 : typ, 
        T' = typ_arrow T T'0 ->
        exists (x : varname) (S : typ) (e' : exp),
        subtype K T S /\ e = exp_lam x S e'). 
      eauto. apply W in X. 
      inversion X as [xx [SS [ee [Hs He]]]].
      exists xx, SS, ee. split; eauto.
      eapply transitivity_of_subtyping; eauto.
Qed.

Lemma canonical_rec: forall K G e rt, 
  has_typ K G e (typ_record rt) ->
  value e ->
  ((exists rdef, e = (exp_recd rdef) /\ 
    forall f T, set_In (f, T) rt -> 
      exists e', set_In (f, e') rdef /\ has_typ K G e' T)
  \/
  (exists a R rdef, e = exp_instance_recd a R rdef /\
    has_typ K G e (typ_path a R) /\
    subtype K (typ_path a R) (typ_record rt))).
Proof.
 (* WIP 
  intros. remember (typ_record rt) as trt in *.
  generalize dependent rt.
  induction H; intros. Focus 8.
  all: try solve [inversion Heqtrt].
  all: try solve [inversion H0; eauto].
  - (* Rec case *)
    intros. left. inversion Heqtrt; subst. 
    exists rdef. split; eauto.
    intros. apply H in H1.
    inversion H1 as [T [Hs Ht]].
    exists T; eauto.
  - (* Subsumption case *)
    subst. apply inv_subtype_record in H1.
    (* record ri is a subtype of rt *)
    inversion H1 as [Hrec | Hpath]; clear H1.
    + (* Rec case *)
      left. inversion Hrec as [ri [HT' Hfr]]; subst.
      clear Hrec.
      eapply IHhas_typ in H0; clear IHhas_typ; try reflexivity.
      inversion H0 as [Hrec | Hpath]; clear H0.
      ++ inversion Hrec as [x [H0 H1]]. exists x.
        split; eauto. 
        intros. apply H1 in H2. inversion H2.
    + (* Path case *)

*)
Admitted.






  Admitted.
  