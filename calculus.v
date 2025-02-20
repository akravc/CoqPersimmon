Require Import PeanoNat.
Local Open Scope nat_scope.
From Coq Require Import Bool String.
Require Import Coq.Lists.ListSet.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

(* This version has records represented as sets *)

(*============= Syntax =============*)

Definition familyname := string.
Definition typename := string.
Definition fieldname := string.
Definition varname := string.
Definition funname := string.
Definition casesname := string.
Definition cnstrname := string.

Inductive relpath : Type := 
  prog | self (a: path) (A: familyname)
with path : Type :=
| selfpath: relpath -> path
| anypath: path -> familyname -> path.

Unset Elimination Schemes.

Inductive typ : Type :=
| typ_nat: typ
| typ_bool: typ
| typ_path: path -> typename -> typ
| typ_arrow: typ -> typ -> typ
| typ_record: set (fieldname * typ) -> typ.

Set Elimination Schemes.

Section typ_ind.

  Variables (P : typ -> Prop)
      (HPNat : P typ_nat)
      (HPBool : P typ_bool)
      (HPPath : forall a R, P (typ_path a R))
      (HPArrow : forall T T', 
            P T -> P T' -> P (typ_arrow T T'))
      (HPRecord : forall rt, 
            (forall f t, set_In (f, t) rt -> P t) -> P (typ_record rt)).

  Fixpoint typ_ind t : P t.
  Proof.
      destruct t.
      + apply HPNat.
      + apply HPBool.
      + apply HPPath.
      + apply HPArrow; eapply typ_ind.
      + apply HPRecord. 
        induction s.
        { intros. inversion H. }
        { intros f t [E | H].
            {specialize (typ_ind (snd a)); now subst. }
            {apply IHs with (1 := H). } } 
  Qed. 

End typ_ind. 

Inductive exp : Type := 
| exp_nat: nat -> exp
| exp_bool: bool -> exp
| exp_var: varname -> exp
| exp_fun_sel: path -> funname -> exp
| exp_cases_sel: path -> casesname -> exp
| exp_app: exp -> exp -> exp
| exp_proj: exp -> fieldname -> exp
| exp_lam: varname -> typ -> exp -> exp
| exp_if: exp -> exp -> exp -> exp
| exp_recd: set (fieldname * exp) -> exp
| exp_instance_recd: path -> typename -> set (fieldname * exp) -> exp
| exp_instance_adt: path -> typename -> cnstrname -> set (fieldname * exp) -> exp
| exp_match: exp -> path -> casesname -> set (fieldname * exp) -> exp.

Inductive value: exp -> Prop :=
  | v_nat: forall n, value (exp_nat n)
  | v_bool: forall b, value (exp_bool b)
  | v_lam: forall x T e, value (exp_lam x T e)
  | v_recd: forall r, 
        (forall f e, set_In (f, e) r -> value e) -> value (exp_recd r)
  | v_instance_recd: forall pth nm r, 
        (forall f e, set_In (f, e) r -> value e) -> value (exp_instance_recd pth nm r) 
        (* should there be some assurance here that the fields match up to the type? *)
  | v_instance_adt: forall pth nm c r, 
        (forall f e, set_In (f, e) r -> value e) -> value (exp_instance_adt pth nm c r).
            (* should there be some assurance here that the fields match up to the type? *)

Definition expvalue: Type := {e: exp | value(e)}.

(*============= Linkages =============*)

Definition pathCtxK := list(relpath).

Inductive marker := Equal | PlusEq.

(* R = {(f_i : T_i)*} *)
Definition type_entry := (typename * marker * set (fieldname * typ))%type.
(* Definition typdef_pluseq := (typename * set (fieldname * typ * expvalue)) %type. *)
(* R = {(f_i = v_i)*} *)
Definition default_entry := (typename * marker * set (fieldname * exp))%type.
(* R = overline{C_i {(f_j : T_j)*}}  *)
Definition adt_entry := (typename * marker * set (cnstrname * set (fieldname * typ)))%type.
(* m: T -> T' = lam (x: T). e *)
Definition fun_entry := (funname * typ * exp)%type.
(* c <a.R>: T -> T' = lam (x: T). {(C_i = e_i)*} *)
Definition cases_entry := (casesname * typ * typ * exp)%type.

(* TODO: separate typing and operational linkages *)

Record linkage: Type := mkLinkage 
  { (* self and super *)
    ref_self: relpath;
    ref_super: path;

    (* definitions *)
    types: set (type_entry);
    defs: set (default_entry);
    adts: set (adt_entry);
    funs: set (fun_entry);
    cases: set (cases_entry)
  }.

(*============= Contexts =============*)

(* partial maps for any id type and output type *)
Definition partial_map (id: Type) (A: Type) := id -> option A.
Definition emp_map {id: Type} {A: Type} : partial_map id A := (fun _ => None).
Definition extend {id: Type } {A:Type} (G: partial_map id A) (x: id) (T: A) (eq: id -> id -> bool) :=
   fun x' => if eq x x' then Some T else G x'.

(* path equality we need for linkage contexts *)
Fixpoint relpath_eq (r r': relpath): bool :=
  match r, r' with
  | prog, prog => true
  | self a A, self a' A' => (path_eq a a') && eqb A A'
  | _, _ => false
  end
with path_eq (p p': path): bool :=
  match p, p' with 
  | selfpath sp, selfpath sp' => relpath_eq sp sp'
  | anypath a A, anypath a' A' => path_eq a a' && eqb A A'
  | _, _ => false
  end.

(* typing context *)
Definition ctxGamma := partial_map varname typ.
Definition var_eq := eqb.
Definition extendG (G: ctxGamma) (x: varname) (T: typ) := 
      extend G x T var_eq.

(*============= Helpers =============*)

(*TODO: placeholder for exact linkage computation *)
Inductive link_comp_ex (p: path): linkage -> Prop := 
  | comp: forall l, link_comp_ex p l.

(* TODO: placeholder for path WF *)
Inductive wf_path(K: pathCtxK): path -> Prop :=
  | wfcomp: forall a, wf_path K a.


(*============= TYPING =============*)

(* well-formedness of types *)
Inductive wf_typ (K: pathCtxK): typ -> Prop :=
  | wf_nat: wf_typ K typ_nat
  | wf_bool: wf_typ K typ_bool
  | wf_arrow: forall T T', 
        wf_typ K T -> wf_typ K T' -> wf_typ K (typ_arrow T T')
  | wf_named: forall a R L typdef adtdef,
        wf_path K a -> 
        link_comp_ex a L ->
        (set_In (R, Equal, typdef) L.(types) \/ 
            set_In (R, Equal, adtdef) L.(adts)) ->
        wf_typ K (typ_path a R)
  | wf_rec: forall rt, 
        NoDup rt ->
        (forall f t, set_In (f, t) rt -> wf_typ K t) ->
        wf_typ K (typ_record rt).

(* subtyping relation *)
Inductive subtype (K: pathCtxK): typ -> typ -> Prop := 
  | sub_refl: forall T, subtype K T T
  | sub_fun: forall T1 T1' T2 T2', 
        subtype K T2 T1 -> 
        subtype K T1' T2' ->
        subtype K (typ_arrow T1 T1') (typ_arrow T2 T2')
  | sub_fam: forall a R T' L typdef, 
        wf_path K a ->
        link_comp_ex a L ->
        set_In (R, Equal, typdef) L.(types) ->
        subtype K (typ_record typdef) T' ->
        subtype K (typ_path a R) T'
  | sub_rec: forall ri rj,
        (* each field in the supertype has a 
        field with a subtype in the subtype *)
        (forall fj Tj, set_In (fj, Tj) rj ->
          (exists T, set_In (fj, T) ri /\ subtype K T Tj)) ->
        subtype K (typ_record ri) (typ_record rj).

Fixpoint fields {A: Type} (r: set(fieldname * A)): set(fieldname) := 
  match r with
  | nil => nil
  | (f, x) :: tail => f :: (fields tail)
  end.

(* typing judgment with path context K and typing context G *)
Inductive has_typ (K: pathCtxK) (G: ctxGamma): exp -> typ -> Prop :=
  | T_Nat: forall n, has_typ K G (exp_nat n) typ_nat
  | T_Bool: forall b, has_typ K G (exp_bool b) typ_bool
  | T_Var: forall x T, 
        G x = Some T -> 
        has_typ K G (exp_var x) T
  | T_Lam: forall x T e T',
        wf_typ K T ->
        has_typ K (extendG G x T) e T' -> 
        has_typ K G (exp_lam x T e) (typ_arrow T T')
  | T_App: forall g e T T',
        has_typ K G e T ->
        has_typ K G g (typ_arrow T T') ->
        has_typ K G (exp_app g e) T'
  | T_Rec: forall rdef rtyp,
        (forall f T, set_In (f, T) rtyp -> 
            exists e, set_In (f, e) rdef /\ has_typ K G e T) ->
        (fields rdef = fields rtyp) ->
        has_typ K G (exp_recd rdef) (typ_record rtyp)
  | T_Proj: forall e rtyp f T,
        has_typ K G e (typ_record rtyp) ->
        set_In (f, T) rtyp ->
        has_typ K G (exp_proj e f) T
  | T_Subs: forall e T T',
        has_typ K G e T' ->
        subtype K T' T -> 
        has_typ K G e T
  | T_If: forall e T g g', 
        has_typ K G e typ_bool -> 
        has_typ K G g T ->
        has_typ K G g' T -> 
        has_typ K G (exp_if e g g') T
  (* rules that rely on linkages *)
  | T_Constr: forall a R rdef L rtyp,
        wf_path K a ->
        link_comp_ex a L -> 
        set_In (R, Equal, rtyp) L.(types) ->
        (* TODO: add defaults here *)
        (*has_typ K G (exp_recd rdef) (typ_record rtyp) -> *)
        (* all fields in rdef and rtyp match up *)
        (forall f T, set_In (f, T) rtyp -> 
            exists e, set_In (f, e) rdef /\ has_typ K G e T) ->
        has_typ K G (exp_instance_recd a R rdef) (typ_path a R)
  | T_ADT: forall a R c rdef L adtdef rtyp,
        wf_path K a -> 
        link_comp_ex a L ->
        set_In (R, Equal, adtdef) L.(adts) ->
        set_In (c, rtyp) adtdef ->
        (*alternative: has_typ K G (exp_recd rdef) (typ_record rtyp) -> *)
        (forall f T, set_In (f, T) rtyp -> 
            exists e, set_In (f, e) rdef /\ has_typ K G e T) ->
        has_typ K G (exp_instance_adt a R c rdef) (typ_path a R)
  | T_FamFun: forall a m T T' L e,
        wf_path K a -> 
        link_comp_ex a L ->
        set_In (m, (typ_arrow T T'), e) L.(funs) ->
        has_typ K G (exp_fun_sel a m) (typ_arrow T T')
  | T_Cases: forall a c rt_arg rt_handlers L a' R e,
        wf_path K a -> 
        link_comp_ex a L ->
        set_In 
          (c, (typ_path a' R), 
            (typ_arrow (typ_record rt_arg) (typ_record rt_handlers)), e)
          L.(cases) ->
        has_typ K G (exp_cases_sel a c) (typ_arrow (typ_record rt_arg) (typ_record rt_handlers))
  | T_Match: forall e a c rec_arg T L a' R adtdef rt_arg rt_handlers,
        has_typ K G e (typ_path a' R) ->
        link_comp_ex a' L ->
        set_In (R, Equal, adtdef) L.(adts) ->
        has_typ K G (exp_cases_sel a c) (typ_arrow (typ_record rt_arg) (typ_record rt_handlers)) ->
        has_typ K G (exp_recd rec_arg) (typ_record rt_arg) ->
        has_typ K G (exp_match e a c rec_arg) T.