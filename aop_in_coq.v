Require Import Coq.Program.Basics.
Require Import Coq.Program.Syntax.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Classes.Morphisms.
Require Import ineqchain.

Open Local Scope program_scope.
Open Local Scope list_scope.
Open Local Scope type_scope.

Set Primitive Projections.

Lemma compose_associativity :
  forall {A B C D : Type} (f : A -> B) (g : B -> C) (h : C -> D),
    (h ∘ g) ∘ f = h ∘ (g ∘ f).
Proof.
  easy.
Qed.

Hint Resolve compose_associativity.
  
Definition id {A : Type} : A -> A
  := fun (x : A) => x.

Lemma id_is_right_identity :
  forall {A B : Type} (f : A -> B), f ∘ id = f.
Proof.
  intros A B f.
  extensionality x.
  easy.
Qed.

Lemma id_is_left_identity :
  forall {A B : Type} (g : A -> B), id ∘ g = g.
Proof.
  intros A B g.
  extensionality x.
  easy.
Qed.    

Hint Resolve id_is_left_identity.
Hint Resolve id_is_right_identity.

Inductive InitialObj : Type :=.
Inductive TerminalObj : Type
  := singletonobj : TerminalObj.

Notation "0" := InitialObj.
Notation "1" := TerminalObj.
Notation "●" := singletonobj.

(* Pair *)

Inductive Pair {A B : Type} : Type :=
| pair (x : A) (y : B) : @Pair A B.

Notation "A × B" := (@Pair A B) (at level 50).
Notation "( a , b , .. , c )" := (pair .. (pair a b) .. c).

Definition outl {A B : Type} (l : A × B) :=
  match l with
  | pair x y => x
  end.

Definition outr {A B : Type} (l : A × B) :=
  match l with
  | pair x y => y
  end.

Definition Pairf {A B X : Type} (f : X -> A) (g : X -> B) :=
  fun (x : X) => (f x, g x).

Notation "⟨ f , g , .. , h ⟩" := (Pairf .. (Pairf f g) .. h).

Lemma split_fusion_l :
  forall {A B X : Type} (f : X -> A) (g : X -> B), (outl ∘ ⟨f, g⟩) = f.
Proof.
  compute; easy.
Qed.

Lemma split_fusion_r :
  forall {A B X : Type} (f : X -> A) (g : X -> B), (outr ∘ ⟨f, g⟩) = g.
Proof.
  compute; easy.
Qed.

Lemma fusion_func :
  forall {A B X Y : Type} (f : X -> A) (g : X -> B) (h : Y -> X),
    ⟨f, g⟩ ∘ h = ⟨f ∘ h, g ∘ h⟩.
Proof.
  compute; easy.
Qed.

Lemma pair_id :
  forall {A B : Type} , ⟨ @outl A B , @outr A B ⟩ = id.
Proof.
  intros A B.
  extensionality x.
  induction x.
  easy.
Qed.
  
(* Coproduct *)
Inductive Either {A B : Type} : Type :=
| inl (a : A) : @Either A B
| inr (b : B) : @Either A B.

Notation "A + B" := (@Either A B).

Definition Eitherf {A B X : Type} (f : A -> X) (g : B -> X) :=
  fun (ab : @Either A B) => match ab with
                            | inl a  => f a
                            | inr b => g b
                            end.

Notation "[ f , g , .. , h ]" := (Eitherf .. (Eitherf f g) .. h).

Lemma either_cancel_l :
  forall {A B X : Type} (f : A -> X) (g : B -> X), [f, g] ∘ inl = f.
Proof.
  compute; easy.
Qed.

Lemma either_cancel_r :
  forall {A B X : Type} (f : A -> X) (g : B -> X), [f, g] ∘ inr = g.
Proof.
  compute; easy.
Qed.

Lemma either_fusion_law :
  forall {A B X Y : Type} (f : A -> X) (g : B -> X) (h : X -> Y),
    h ∘ [f, g] = [h ∘ f, h ∘ g].
Proof.
  intros A B X Y f g h.
  extensionality x.
  induction x.
  - easy.
  - easy.
Qed.  

Lemma coprod_id :
  forall (A B : Type), [fun x : A => inl (id x), fun x : B => inr (id x)] = id.
Proof.
  intros A B.
  extensionality x.
  induction x.
  - easy.
  - easy.
Qed.

Class Functor (F : Type -> Type)
      (Fhom : forall (A B : Type), (A -> B) -> F A -> F B)
  :=
  {
    Fmap := Fhom;
    Fhom_identity : forall {A : Type}, Fhom A A (@id A) = @id (F A);
    Fhom_composition : forall {A B C : Type} (f : A -> B) (g : B -> C),
        Fhom A C (g ∘ f) = (Fhom B C g ∘ Fhom A B f)
  }.

Inductive Polynominal_Functor :=
| Top              : Polynominal_Functor
| Var              : Polynominal_Functor
| Const (A : Type) : Polynominal_Functor
| Product          : Polynominal_Functor -> Polynominal_Functor -> Polynominal_Functor
| CoProduct        : Polynominal_Functor -> Polynominal_Functor -> Polynominal_Functor.

Fixpoint Eval_PF (FABS : Polynominal_Functor) (X : Type) : Type :=
  match FABS with
  | Top => 1
  | Var => X
  | Const A => A
  | Product F G => Eval_PF F X × Eval_PF G X
  | CoProduct F G => @Either (Eval_PF F X) (Eval_PF G X)
  end.

Fixpoint PFhom (F : Polynominal_Functor) {A B : Type} (f : A -> B) : Eval_PF F A ->  Eval_PF F B :=
  match F with
  | Top             => (@id 1)
  | Var             => f
  | Const C         => (@id C)
  | Product F' G'   => Pairf ((@PFhom F' A B f) ∘ outl) ((@PFhom G' A B f) ∘ outr)
  | CoProduct F' G' => (Eitherf (fun x => @inl (Eval_PF F' B) (Eval_PF G' B) (@PFhom F' A B f x))
                                (fun x => @inr (Eval_PF F' B) (Eval_PF G' B) (@PFhom G' A B f x)))
                       : Eval_PF (CoProduct F' G') A -> Eval_PF (CoProduct F' G') B
  end.

Coercion Eval_PF : Polynominal_Functor >-> Funclass.

Instance PF_is_exact_Funcotr :
  forall PF : Polynominal_Functor, (Functor (Eval_PF PF) (@PFhom PF)) := {}.
Proof.
  - intros A.
    induction PF.
    + easy.
    + easy.
    + easy.
    + simpl.
      rewrite IHPF1.
      rewrite IHPF2.
      repeat rewrite id_is_left_identity.
      apply pair_id.
    + simpl.
      rewrite IHPF1.
      rewrite IHPF2.
      extensionality x.
      rewrite coprod_id;easy.
  - intros A B C f g.
    induction PF.
    + easy.
    + easy.
    + easy.
    + simpl.
      rewrite IHPF1; rewrite IHPF2.
      extensionality x.
      induction x.
      easy.
    + simpl.
      rewrite IHPF1; rewrite IHPF2.
      extensionality x.
      induction x.
      * easy.
      * easy.
Qed.

Notation "F [ f ]" := (@Fmap F _ _ _ _ f) (at level 10).

Hint Resolve Fhom_identity.
Hint Resolve Fhom_composition.

Class F_initial_algebra
      (F : Type -> Type)
      (Fhom : forall (A B : Type), (A -> B) -> F A -> F B)
      (I : Type)
      (eval : F I -> I)
      (bf : forall (X : Type) (f : F X -> X), I -> X)
  :=
  {
    F_isFunctor :> Functor F Fhom;
    cata := bf;
    initial_commutativity :
      forall {X : Type} (f : F X -> X), (cata X f) ∘ eval = f ∘ (F[cata X f]);
    initial_uniqueness :
      forall {X : Type} (f : F X -> X) (cata' : I -> X),
        cata' ∘ eval = f ∘ F[cata'] -> cata X f = cata'
  }.

Hint Resolve initial_commutativity.
Hint Resolve initial_uniqueness.

Notation "(| f |)" := (@cata _ _ _ _ _ _ _ f).
Notation "([ f , g , .. , h ])" := (@cata _ _ _ _ _ _ _ (Eitherf .. (Eitherf f g) .. h)).

Lemma cata_eval_eq_id :
  forall {F : Type -> Type}
         {Fhom : forall (A B : Type), (A -> B) -> F A -> F B}
         {I : Type}
         {eval : F I -> I}
         {bf : forall (X : Type) (f : F X -> X), I -> X}
         {fi : F_initial_algebra F Fhom I eval bf},
    (| eval |) = id.
Proof.
  intros F Fhom I α bf fi.
  apply initial_uniqueness.
  rewrite Fhom_identity.
  easy.
Qed.

Lemma initial_fusion : 
  forall {F : Type -> Type}
         {Fhom : forall {A B : Type}, (A -> B) -> F A -> F B}
         {I : Type}
         {eval : F I -> I}
         {bf : forall (X : Type) (f : F X -> X), I -> X}
         {fi : F_initial_algebra F (fun A B => @Fhom _ _) I eval bf}
         {A B : Type}
         (f : F A -> A) (g : F B -> B) (h : A -> B),
    h ∘ f = g ∘ F[h] -> h ∘ (|f|) = (|g|).
Proof. 
  intros F Fhom I α bf fi A B f g h H.
  symmetry.
  apply initial_uniqueness.
  rewrite Fhom_composition.
  rewrite <- compose_associativity.
  rewrite <- H.
  rewrite compose_associativity.
  rewrite initial_commutativity.
  easy.
Qed.

Lemma eval_fusion : 
  forall {F : Type -> Type}
         {Fhom : forall (A B : Type), (A -> B) -> F A -> F B}
         {I : Type}
         {eval : F I -> I}
         {bf : forall (X : Type) (f : F X -> X), I -> X}
         {fi : F_initial_algebra F Fhom I eval bf},
    eval ∘ (|F[eval]|) = (|eval|).
Proof.
  intros F Fhom I eval bf fi.
  apply initial_fusion.
  easy.
Qed.

Theorem eval_is_iso_l :
  forall {F : Type -> Type}
         {Fhom : forall (A B : Type), (A -> B) -> F A -> F B}
         {I : Type}
         {α : F I -> I}
         {bf : forall (X : Type) (f : F X -> X), I -> X}
         {fi : F_initial_algebra F Fhom I α bf},
    α ∘ (|F[α]|) = id. 
Proof.
  intros F Fhom I α bf fi.
  Left
  = (α ∘ (|F[α]|)).
  = ((|α|))        { by eval_fusion }.
  = (@id I)        { by cata_eval_eq_id }.
  = Right.
Qed.  

Theorem eval_is_iso_r :
  forall {F : Type -> Type}
         {Fhom : forall (A B : Type), (A -> B) -> F A -> F B}
         {I : Type}
         {α : F I -> I}
         {bf : forall (X : Type) (f : F X -> X), I -> X}
         {fi : F_initial_algebra F Fhom I α bf},
    (|F[α]|) ∘ α = id.
Proof.
  intros F Fhom I α bf fi.
  Left
  = ( (|F[α]|) ∘ α ).
  = ( F[α] ∘ F[(|F[α]|)] ).
  = ( F[ α ∘(| F[α] |)] )   { by Fhom_composition }.
  = ( F[@id I] )            { by eval_is_iso_l }.
  = ( @id (F I) )           { by Fhom_identity }.
  = Right.
Qed.

Theorem banana_split_law :
  forall {F : Type -> Type}
         {Fhom : forall (A B : Type), (A -> B) -> F A -> F B}
         {I : Type}
         {α : F I -> I}
         {bf : forall (X : Type) (f : F X -> X), I -> X}
         {fi : F_initial_algebra F Fhom I α bf}
         {A B : Type} (h : F A -> A) (k : F B -> B),
    ⟨(|h|),(|k|)⟩ = (| ⟨h ∘ F[outl], k ∘ F[outr]⟩ |).
Proof.
  intros F Fhom I α bf fi A B h k; symmetry.
  apply initial_uniqueness.
  @ goal : ( ⟨ (|h|), (|k|) ⟩ ∘ α = ⟨ h ∘ F [outl], k ∘ F [outr] ⟩ ∘ F [⟨ (|h|), (|k|) ⟩] ).
  Left
  = (⟨(|h|), (|k|)⟩ ∘ α).
  = ⟨(|h|) ∘ α, (|k|) ∘ α⟩.
  = ⟨h ∘ F[(|h|)], k ∘ F[(|k|)]⟩
      { repeat rewrite initial_commutativity }.
  = ⟨h ∘ F[outl ∘ ⟨(|h|), (|k|)⟩], k ∘ F[outr ∘ ⟨(|h|), (|k|)⟩]⟩.
  = ⟨h ∘ F[outl] ∘ F[ ⟨(|h|), (|k|)⟩], k ∘ F[outr] ∘ F[⟨(|h|), (|k|)⟩]⟩
      { repeat rewrite Fhom_composition }.
  = ⟨(h ∘ F[outl] ) ∘ F[⟨(|h|), (|k|)⟩], (k ∘ F[outr] ) ∘ F[⟨(|h|), (|k|)⟩]⟩.
  = (⟨h ∘ F[outl], k ∘ F[outr]⟩ ∘ F[⟨(|h|), (|k|)⟩] ).
  = Right.
Qed.

Section nat.

  Definition F_nat (X : Type) := 1 + X.

  Definition nat_hom {A B : Type} (f : A -> B) (x : F_nat A)
    := match x with
       | inl ●  => inl ●
       | inr x' => inr (f x')
       end.

  Instance nat_functor : Functor F_nat (@nat_hom) :=
    {}.
  Proof.
    - intros A.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + easy.
    - intros A B C f g.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + easy.
  Qed.    

  Definition nat_eval :=
    fun (x : F_nat nat) =>
      match x with
      | inl ● => O
      | inr n => S n
      end.

  Definition nat_cata {X : Type} (f : F_nat X -> X) :=
    fix F x :=
      (match x with
       | O   => f (inl singletonobj)
       | S n => f (inr (F n))
       end).
  
  Instance nat_initial : (F_initial_algebra F_nat (@nat_hom) nat nat_eval (@nat_cata)) :=
    {
    }.
  Proof.
    - intros X f.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + easy.
    - intros X f cata' H.
      extensionality x.
      induction x.
      + Right
        = (cata' O).
        = (cata' (nat_eval (inl ●))).
        = ((cata' ∘ nat_eval) (inl ●)).
        = ((f ∘ nat_hom cata') (inl ●))  {by H}.
        = (f (inl ●)).
        = Left.
      + simpl ; rewrite IHx.
        @ goal : (f (inr (cata' x)) = cata' (S x)).
        Right
        = (cata' (nat_eval (inr x))).
        = ((cata' ∘ nat_eval) (inr x)).
        = ((f ∘ nat_hom cata') (inr x))  {by H}.
        = (f (inr (cata' x))).
        = Left.
  Qed.

  Definition plus :=
    ([ fun (t : 1) => (fun (y : nat) => y), fun (f : nat -> nat) => fun (y : nat) => S (f y) ]).
  
End nat.

Section list.
  Variable A : Type.
  
  Definition F_listA (X : Type) := 1 + (A × X).
  
  Definition listA_hom {X Y : Type} (f : X -> Y) (x : F_listA X)
    := match x with
       | inl ●  => inl ●
       | inr x' => inr (outl x', f (outr x'))
       end.

  Instance listA_functor : Functor F_listA (@listA_hom) :=
    {}.
  Proof.
    - intros A0.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + induction b.
        easy.
    - intros A0 B C f g.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + easy.
  Qed.
  
  Definition listA_eval :=
    fun (x : F_listA (list A)) =>
      match x with
      | inl ●  => []
      | inr x' => (outl x') :: (outr x')
      end.

  Definition listA_cata {X : Type} (f : F_listA X -> X) :=
    fix F x :=
      (match (x : list A) with
       | []     => f (inl ●)
       | h :: t => f (inr (h, F t))
       end).
  
  Instance listA_initial : (F_initial_algebra F_listA (@listA_hom) (list A) listA_eval (@listA_cata)) :=
    {
    }.
  Proof.
    - intros X f.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + induction b.
        easy.
    - intros X f cata' H.
      extensionality x.
      induction x.
      + Right
        = (cata' nil).
        = (cata' (listA_eval (inl ●))).
        = ((cata' ∘ listA_eval) (inl ●)).
        = ((f ∘ listA_hom cata') (inl ●))  {by H}.
        = (f (inl ●)).
        = Left.
      + simpl.
        rewrite IHx.
        @ goal : (f (inr (a, cata' x)) = cata' (a :: x)).
        Right
        = (cata' (a :: x)).
        = ((cata' ∘ listA_eval) (inr (a, x))).
        = ((f ∘ listA_hom cata') (inr (a, x)))  {by H}.
        = (f (inr (a, cata' x))).
        = Left.
  Qed.

  Definition length : (list A) -> nat :=
    ([ fun (t : 1) => O , S ∘ outr]).
  
  Definition fold_f (c : A) (f : A -> A -> A) : (list A) -> A :=
    ([ fun (t : 1) => c , fun (p : A × A)  => f (outl p) (outr p) ]) .
End list.

Definition sum := fold_f nat O plus.

Eval compute in (length nat (cons 10 (cons 2 (cons 3 (cons 12 nil)))) ).

Definition zeros := ⟨ fun (t : nat) => O , fun (t : nat) => O ⟩.
Definition pluss p := (plus (outl p) (outl (outr p)), S (outr (outr p))).

Print pluss.

Theorem nat_ave :
  ⟨ sum , length nat ⟩ = (| ⟨ zeros , pluss ⟩ |).
  


Require Import Coq.Sorting.Heap.
Section Tree.
  Variable A : Type.
  
  Definition F_treeA (X : Type) := 1 + (A × X × X).
  
  Definition treeA_hom {X Y : Type} (f : X -> Y) (x : F_treeA X) : F_treeA Y
    := match x with
       | inl ●  => inl ●
       | inr x' => inr ((outl (outl x'), (f (outr (outl x'))), (f (outr x'))))
       end.
  
  Instance treeA_functor : Functor F_treeA (@treeA_hom) :=
    {}.
  Proof.
    - intros A0.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + induction b; induction x.
        easy.
    - intros A0 B C f g.
      extensionality x.
      induction x.
      + induction a.
        easy.
      + easy.
  Qed.

  Definition treeA_eval :=     
    fun (x : F_treeA (Tree A)) =>
      match x with
      | inl ●  => @Tree_Leaf A
      | inr x' => @Tree_Node A (outl (outl x')) (outr (outl x')) (outr x')
      end.

  Definition treeA_cata {X : Type} (f : F_treeA X -> X) :=     
    fix F x :=
      (match (x : Tree A) with
       | Tree_Leaf _         => f (inl ●)
       | Tree_Node _ a T1 T2 => f (inr (a, F T1, F T2))
       end).

  Instance treeA_initial : (F_initial_algebra F_treeA (@treeA_hom) (Tree A) treeA_eval (@treeA_cata)) :=
    {
    }.
  Proof.
    - intros X f.
      extensionality x.
      induction x.
      + induction a; easy.
      + induction b; easy.
    - intros X f cata' H.
      extensionality x.
      induction x.
      + Right
        = (cata' (Tree_Leaf A)).
        = (cata' (treeA_eval (inl ●))).
        = ((cata' ∘ treeA_eval) (inl ●)).
        = ((f ∘ treeA_hom cata') (inl ●))  {by H}.
        = (f (inl ●)).
        = Left.
      + simpl.
        rewrite IHx1, IHx2.
        @ goal : (f (inr (a, cata' x1, cata' x2)) = cata' (Tree_Node A a x1 x2)).
        Right
        = (cata' (Tree_Node A a x1 x2)).
        = ((cata' ∘ treeA_eval) (inr (a, x1, x2))).
        = ((f ∘ treeA_hom cata') (inr (a, x1, x2)))  {by H}.
        = (f (inr (a, cata' x1, cata' x2))).
        = Left.
  Qed.
End Tree.





Variable A : Type.

Definition F_listA (X : Type) := 1 + (A × X).

Definition listA_hom {X Y : Type} (f : X -> Y) (x : F_listA X)
  := match x with
     | inl $¥bullet$  => inl $¥bullet$
     | inr x' => inr (outl x', f (outr x'))
     end.

Instance listA_functor : Functor F_listA (@listA_hom) :=
  {}.
Proof.
  - intros A0.
    extensionality x.
    induction x.
    + induction a.
      easy.
    + induction b.
      easy.
  - intros A0 B C f g.
    extensionality x.
    induction x.
    + induction a.
      easy.
    + easy.
Qed.

Definition listA_eval :=
  fun (x : F_listA (list A)) =>
    match x with
    | inl $¥bullet$  => []
    | inr x' => (outl x') :: (outr x')
    end.

Definition listA_cata {X : Type} (f : F_listA X -> X) :=
  fix F x :=
    (match (x : list A) with
     | []     => f (inl $¥bullet$)
     | h :: t => f (inr (h, F t))
     end).

Instance listA_initial : (F_initial_algebra F_listA (@listA_hom)
                                            (list A) listA_eval
                                            (@listA_cata)) :=
  {
  }.
Proof.
  - intros X f.
    extensionality x.
    induction x.
    + induction a.
      easy.
    + induction b.
      easy.
  - intros X f cata' H.
    extensionality x.
    induction x.
    + Right
      = (cata' nil).
      = (cata' (listA_eval (inl $¥bullet$))).
      = ((cata' $¥circ$ listA_eval) (inl $¥bullet$)).
      = ((f $¥circ$ listA_hom cata') (inl $¥bullet$))  {by H}.
      = (f (inl $¥bullet$)).
      = Left.
    + simpl.
      rewrite IHx.
      @ goal : (f (inr (a, cata' x)) = cata' (a :: x)).
      Right
      = (cata' (a :: x)).
      = ((cata' $¥circ$ listA_eval) (inr (a, x))).
      = ((f $¥circ$ listA_hom cata') (inr (a, x)))  {by H}.
      = (f (inr (a, cata' x))).
      = Left.

Qed.

Instance listA_initial :
  (F_initial_algebra F_listA (@listA_hom) (list A) listA_eval (@listA_cata)) := {}.

initial_fusion : 
  forall {F : Type -> Type}
         {Fhom : forall {A B : Type},
             (A -> B) -> F A -> F B}
         {I : Type}
         {eval : F I -> I}
         {bf : forall (X : Type)
                      (f : F X -> X),
             I -> X}
         {fi : F_initial_algebra
                 F (fun A B => @Fhom _ _)
                 I eval bf}
         {A B : Type}
         (f : F A -> A)
         (g : F B -> B)
         (h : A -> B),
    h ∘ f = g ∘ F[h]
    -> h ∘ (|f|) = (|g|).