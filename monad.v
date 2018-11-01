From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype finset rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint order finmap.

Module Monad.

(* Here we generalize monads not to be Type -> Type but rather dom -> Type, where dom is an arbitrary kind. This enables T to be from choiceType to Type, etc. clof then is the projection from dom back down to Type (ie, Choice.sort) 

  Additionally we generalize the monad laws to be over an arbitrary relation mrel. in many cases this will be equal to (fun A => @eq (T A)) but could also be =1, in the case of state monad (not extensional)
*)

  Record axiom (dom : Type) (clof : dom -> Type) (T : dom -> Type) (mrel : forall A, T A -> T A -> Prop) (mret : forall A, clof A -> T A) (bind : forall A B, T A -> (clof A -> T B) -> T B) :=
    {
      _ : forall A B (x : clof A) (f : clof A -> T B) , mrel _ (bind _ _ (mret _ x) f) (f x);
      _ : forall A (m : T A), mrel _ (bind _ _ m (mret A)) m;
      _ : forall A B C (m : T A) (f : clof A -> T B) (g : clof B -> T C),
          mrel _ (bind _ _ (bind _ _ m f) g) (bind _ _ m (fun x => bind _ _ (f x) g));
      }.

Record mixin_of (dom : Type) (clof : dom -> Type) (T : dom -> Type) (mrel : forall A, T A -> T A -> Prop) : Type := Mixin { mret : forall A, clof A -> T A; bind : forall A B, T A -> (clof A -> T B) -> T B; _ : axiom dom clof T mrel mret bind }.
    Notation class_of := mixin_of (only parsing).
  
  Section ClassDef.

    Structure type := Pack {dom; clof; sort; mrel; _ : class_of dom clof sort mrel; _ : dom -> Type}.
    Local Coercion sort : type >-> Funclass.

Variables (dom0 : Type) (T : dom0 -> Type) (clof0 : dom0 -> Type) (mrel0 : forall A, T A -> T A -> Prop) (cT : type).
Definition class : mixin_of _ (clof cT) (sort cT) (mrel cT).
destruct cT; rewrite //=.
Defined.

Print Equality.pack.

Definition pack mrel (m : mixin_of dom0 clof0 T mrel) : type.
econstructor.
apply m.
apply T.
Defined.

Definition clone c of phant_id class c := @Pack dom0 clof0 T mrel0 c T.

End ClassDef.

Module Exports.
Coercion sort : type >-> Funclass.
Notation monadType := type.
Notation MonadMixin := Mixin.
Notation MonadType d c T r m := (@pack d c T r m).

Check clone.
Notation "[ 'monadType' 'of' T 'for' cT ]" := (@clone _ T _ _ cT _ idfun)
  (at level 0, format "[ 'monadType' 'of' T 'for' cT ]") : form_scope.
Notation "[ 'monadType' 'of' T ]" := (@clone _ T _ _ _ _ id)
  (at level 0, format "[ 'monadType' 'of' T ]") : form_scope.

End Exports.
End Monad.

Export Monad.Exports.
Definition mbind T := Monad.bind _ _ _ _ (Monad.class T).
Definition mret T := Monad.mret _ _ _ _ (Monad.class T).
Definition mrel T A x y := Monad.mrel T A x y.

Notation "'ret' x" := (mret _ _ x) (at level 70).
Notation "x <- c ; d" := (mbind _ _ _ c (fun x => d)) (right associativity, at level 80, d at next level).
Notation "c1 ~~ c2"  := (mrel _ _ c1 c2) (at level 70).

Section MonadDefs.
  Variable (m : monadType).
  Lemma bind_ret A (c : m A) : (x <- c; ret x) ~~ c.
    rewrite /mbind //=.
  destruct m.
  destruct m0.
  destruct a.
  simpl in *.
  apply m1.
  Qed.

  Lemma ret_bind (A : Monad.dom m)  B (a : Monad.clof m A) (c : Monad.clof m A -> m B) : (x <- (ret a); c x) ~~ c a.
  rewrite /mbind /mret //=.
  destruct m.
  destruct m0.
  destruct a0; simpl.
  apply m0.
  Qed.

  Lemma bindA A B C (a : m A) (c : Monad.clof m A -> m B) (d : Monad.clof m B -> m C) :
    (x <- (y <- a; c y); d x) ~~ (x <- a; (y <- c x; d y)).
  rewrite /mbind /mret //=.
  destruct m.
  destruct m0.
  destruct a0; simpl.
  apply m2.
  Qed.
End MonadDefs.


(* option *)

Lemma option_monad : Monad.axiom Type id option (fun A => @eq (option A)) (fun A (x : A) => Some x) (fun A B (x : option A) (y : A -> option B) => obind y x).
  constructor.
  rewrite //=.
  move => A; case; rewrite //=.
  move => A B C ma f g.
  case ma; rewrite //=.
Qed.

Canonical optionMonadMixin := Eval hnf in MonadMixin _ _ _ _ _ _ option_monad.
Canonical optionMonadType := Eval hnf in MonadType _ _ _ _ optionMonadMixin.

(* seq *)

Lemma seq_monad : Monad.axiom Type id seq (fun A => @eq (seq A)) (fun A (x : A) => [:: x]) (fun A B (x : seq A) (f : A -> seq B) => flatten (map f x)).
  constructor.
  rewrite //= => A B x f; rewrite cats0 //=. 
  move => A m; rewrite //= flatten_seq1 //=.
  move => A B C m f g.
  induction m; rewrite //=.
  rewrite map_cat flatten_cat IHm //=.
Qed.

Canonical seqMonadMixin := Eval hnf in MonadMixin _ _ _ _ _ _ seq_monad.
Canonical seqMonadType := Eval hnf in MonadType _ _ _ _ seqMonadMixin.

(* state *)

Definition State (S : Type) (A : Type) := S -> A * S.

Lemma state_monadax (S : Type) : Monad.axiom Type id (State S) (fun A f1 f2 => f1 =1 f2)
                                             (fun A (x : A) => fun s => (x, s))
                                             (fun A B (x : State S A) (f : A -> State S B) s =>
                                                let p := x s in
                                                f (p.1) (p.2)).
  constructor; rewrite //=.
  move => A m x.
  destruct (m x); rewrite //=.
Qed.

Definition get {S} : State S S := fun (s : S) => (s, s).
Definition put {S} (s : S) : State S unit := fun (_ : S) => (tt, s).

Canonical stateMonadMixin S := Eval hnf in MonadMixin _ _ _ _ _ _ (state_monadax S).
Canonical stateMonadType S := Eval hnf in MonadType _ _ _ _ (stateMonadMixin S).

Check (fun (c : State _ _) => (x <- c; put x)).

(* finset *)

Lemma finset_monadax : Monad.axiom finType Finite.sort (fun A => {set A}) (fun A => @eq {set A})
                                   (fun (A : finType) (x : A) => set1 x)
                                   (fun A B (x : {set A}) (f : A -> {set B}) =>
                                     \bigcup_(a in x) (f a)).
  constructor; rewrite //=.
  move => A B x f; rewrite big_set1 //=.
  move => A m; apply/setP => x; apply Bool.eq_iff_eq_true; split.
  move/bigcupP; elim => x0 Hx0; rewrite in_set; move/eqP => ->; done.
  move => H; apply/bigcupP; eexists.
  apply H.
  rewrite in_set //=.
  move=>A B C m f g.

  apply/setP => x; apply Bool.eq_iff_eq_true; split.
  move/bigcupP; elim => b /bigcupP => [[i Hi] Hb] Hc.
  apply/bigcupP; eexists.
  apply Hi.
  apply/bigcupP; eexists.
  apply Hb.
  done.

  move/bigcupP; elim => a Ha /bigcupP => [[i Hi] Hb]; apply/bigcupP; eexists.
  apply/bigcupP; eexists.
  apply Ha.
  apply Hi.
  done.
Qed.

Canonical setMonadMixin := Eval hnf in MonadMixin _ _ _ _ _ _ (finset_monadax).
Canonical setMonadType := Eval hnf in MonadType _ _ _ _ (setMonadMixin).

(* fset *)

Lemma fset_monadax : Monad.axiom choiceType Choice.sort (fun A => {fset A}) (fun A => @eq {fset A})
                                   (fun (A : choiceType) (x : A) => fset1 x)
                                   (fun A B (x : {fset A}) (f : A -> {fset B}) =>
                                     \bigcup_(a <- x) (f a))%fset.
  constructor; rewrite //=.
  move => A B x f; rewrite big_seq_fset1 //=.
  move => A m; apply/fsetP => x; apply Bool.eq_iff_eq_true; split.
  move/bigfcupP; elim => x0 Hx0; rewrite in_fset //= in_cons //= in_nil orbF; move/eqP => ->; elim (andP Hx0); done.
  move => H; apply/bigfcupP; eexists.
  apply/andP; split; [apply H | done].
  rewrite in_fset in_cons eq_refl //=.

  move=>A B C m f g.
  apply/fsetP => x; apply Bool.eq_iff_eq_true; split.
  move/bigfcupP; elim => b /andP ; elim => /bigfcupP; elim => a /andP [Ha _] Hb _ Hg.
  apply/bigfcupP; eexists.
  apply/andP; split; [apply Ha | done].
  apply/bigfcupP; eexists.
  apply/andP; split; [apply Hb | done].
  done.

  move/bigfcupP; elim => a /andP [Ha _] /bigfcupP => [[i /andP [Hi _]] Hg].
  apply/bigfcupP; eexists.
  apply/andP; split; [apply/bigfcupP; eexists| done].
  apply/andP; split; [apply Ha | done].
  apply Hi.
  done.
Qed.

Canonical fsetMonadMixin := Eval hnf in MonadMixin _ _ _ _ _ _ (fset_monadax).
Canonical fsetMonadType := Eval hnf in MonadType _ _ _ _ (fsetMonadMixin).