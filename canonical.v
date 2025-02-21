Require Import PeanoNat.
Local Open Scope nat_scope.
From Coq Require Import Bool String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import calculus.
Require Import transitivity.


(*-----------------Helpers----------------------*)

Theorem linkage_comp_eq: forall a L L', 
  link_comp_ex a L -> 
  link_comp_ex a L' ->
  L = L'.
Proof.
Admitted.

Theorem linkage_fam_rec_def_eq: forall R rt1 rt2 L,
  set_In (R, Equal, rt1) (types L) ->
  set_In (R, Equal, rt2) (types L) -> 
  rt1 = rt2.
Proof.
Admitted.

Theorem linkage_named_type_excl: forall R rdef L,
  set_In (R, Equal, rdef) (types L) ->
  ~exists adtdef, set_In (R, Equal, adtdef) (adts L).
Proof.
Admitted.

(*======================Canonical Thms===========================*)

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

Lemma canonical_fam: forall K G e a R, 
  has_typ K G e (typ_path a R) ->
  value e ->
  ((exists rdef L rtyp,
    e = (exp_instance_recd a R rdef) /\
    wf_path K a /\
    link_comp_ex a L /\
    set_In (R, Equal, rtyp) L.(types) /\
    (* TODO: add defaults here *)
    (forall f T, set_In (f, T) rtyp -> 
      exists e, set_In (f, e) rdef /\ has_typ K G e T))) \/
  (exists c rdef L adtdef rtyp,
    e = (exp_instance_adt a R c rdef) /\
    wf_path K a /\ 
    link_comp_ex a L /\
    set_In (R, Equal, adtdef) L.(adts) /\
    set_In (c, rtyp) adtdef /\
    (forall f T, set_In (f, T) rtyp -> 
      exists e, set_In (f, e) rdef /\ has_typ K G e T)).
Proof.
  intros. 
  remember (typ_path a R) as tpath in *.
  induction H; intros.
  all: try solve [inversion Heqtpath].
  all: try solve [inversion H0; eauto].
  - (* Subsumption *)
    subst. apply inv_subtype_path in H1.
    apply IHhas_typ in H1; eauto.
  - (* record instance *)
    left. exists rdef, L, rtyp.
    repeat split; try eauto; inversion Heqtpath; subst; eauto.
  - (* ADT instance *) 
    right. exists c, rdef, L, adtdef, rtyp.
    repeat split; try eauto; inversion Heqtpath; subst; eauto.
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
  intros. remember (typ_record rt) as trt in *.
  generalize dependent rt.
  induction H; intros.
  all: try solve [inversion Heqtrt].
  all: try solve [inversion H0; eauto].
  - (* Rec case *)
    left. inversion Heqtrt; subst. 
    exists rdef. split; eauto.
  - (* Subsumption case *)
    subst. apply inv_subtype_record in H1.
    (* record ri is a subtype of rt *)
    inversion H1 as [Hrec | Hpath]; clear H1.
    + (* Rec case *)
      inversion Hrec as [ri [HT' Hfr]]; subst.
      clear Hrec.
      eapply IHhas_typ in H0; clear IHhas_typ; try reflexivity.
      inversion H0 as [Hrec | Hpath]; clear H0.
      ++ left. inversion Hrec as [rdef' [A B]].
        exists rdef'; split; auto. 
        intros. apply Hfr in H0.
        inversion H0 as [T0 [Hset Hsub]].
        apply B in Hset. inversion Hset as [e' [Hset' Htyp]].
        exists e'; split; auto.
        econstructor; eauto.
      ++ right. inversion Hpath as [a [R [rdef [He [Ht Hs]]]]].
        exists a, R, rdef; repeat split; auto.
        assert (X: subtype K (typ_record ri) (typ_record rt)).
        econstructor. eauto.
        inversion Hs. econstructor; eauto.
        eapply transitivity_of_subtyping; eauto.
    + clear IHhas_typ.
      inversion Hpath as [a [R [L [typdef [Ht [Hwf [Hl [Hset Hsub]]]]]]]].
      clear Hpath. subst.
      eapply canonical_fam in H; auto.
      inversion H as [Hrdef | Hadtdef]; clear H.
      ++ inversion Hrdef as [rdef' [L' [rtyp' X]]].
         inversion X as [He [Hwf' [Hl' [Hset' Hsub']]]].
         clear Hrdef X. right.
         exists a, R, rdef'. split; eauto. split.
         { rewrite He. eapply T_Constr; eauto. }
         { econstructor; eauto.
           assert (HL: L = L'). eapply linkage_comp_eq; eauto. subst.
           assert (Hrt: typdef = rtyp').
           eapply linkage_fam_rec_def_eq; eauto. subst. auto. }
      ++ inversion Hadtdef as [c [rdef [L' [adtdef [rtyp X]]]]].
         inversion X as [He [Hwf' [Hl' [Hset' [Hset'' Hsub']]]]].
         clear Hadtdef X. apply linkage_named_type_excl in Hset.
         exfalso. assert (HL: L = L'). 
         eapply linkage_comp_eq; eauto. subst.
         apply Hset. exists adtdef; eauto.
Qed.