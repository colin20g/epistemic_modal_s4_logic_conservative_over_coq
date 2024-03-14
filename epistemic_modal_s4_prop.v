(** In this text we define a new type ("Epistemic_Prop") whose intended elements are logical 
    formulas with a modal operator, in which *classical* modal S4 logical reasoning can be 
    conducted. The important feature of that system is that the usual Prop COQ type of 
    logical formulas is embedded conservatively into Epistemic_Prop 
    (although the former has only intuitionistic logic available).
    As a result it is possible to reason classically in COQ by replacing Prop by this new type 
    and yet produce legitimate theorems from the point of view of COQ.

    The proof consists in building a special case of a theorem of Funayama which states that
    every complete Heyting algebra is isomorphic as a lattice to a topology in a suitable
    complete boolean algebra. When the Heyting algebra is the COQ Prop type itself, 
    the construction of the boolean algebra and the topology (in the form of an 
    interior operation) are surprisingly short and done in the text below.

    The Funayama's theorem provides a justification of the fact that if the 
    Gödel-MacKinsey-Tarski translation of a formula is provable in classical modal S4
    logic then the aformentioned formula has an intuitionistic proof. 
    For the record the following is a sketch of a constructive proof of the Funayama's theorem.
    Let H be a complete Heyting algebra and p be any element of H. Then the subset B(p) of  
    elements x of H such that (x -> p) -> p <= x is a complete boolean algebra (having the 
    same implication and arbitrary meets as H and p as its smallest element). The product
    B of the family p -> B(p) is again a complete boolean algebra. We define for any x,p in H,
    u(x)(p):= (x -> p) -> p. We define for any f in B and p in H, 
    i(f):= u(inf{f(q) | q in H}). Then i is an interior operation in B and u is the
    required embedding from H to B (details are straightforward and left to the reader).

    The following program is the implementation of the ideas of the proof just above.
    
    Similar ideas can be found in  the following:
    [R. C. Flagg, H. Friedman, Epistemic and intuitionistic formal systems, Annals
    of Pure and Applied Logic 32 (1986) 53–60]
 *)

Definition Epistemic_Prop:Type:=
  {g: Prop -> Prop | forall p:Prop, ((g p -> p) -> p) -> g p}.

Definition EP_Theorem (a: Epistemic_Prop):Prop:= forall p: Prop, proj1_sig a p.

(** The following is the modal operator; we didn't find that the word "necessary"
 faithfully reflected its meaning in the case we wish to apply it. *)

Definition ep_confirmed (f: Epistemic_Prop): Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
        (fun p : Prop => ((forall q : Prop, proj1_sig f q) -> p) -> p)
        (fun (p : Prop) (A : ((((forall q : Prop, proj1_sig f q) -> p) -> p) -> p) -> p)
             (B : (forall q : Prop, proj1_sig f q) -> p) =>
           A (fun C : ((forall q : Prop, proj1_sig f q) -> p) -> p => C B)).

Definition ep_False: Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p) 
        (fun p : Prop => p) (fun (p : Prop) (A : (p -> p) -> p) => A (fun B : p => B)).

Definition ep_True: Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
        (fun _ : Prop => True) (fun (p : Prop) (_ : (True -> p) -> p) => I). 

Definition ep_not (a: Epistemic_Prop): Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
        (fun p : Prop => proj1_sig a p -> p)
        (fun (p : Prop) (L : ((proj1_sig a p -> p) -> p) -> p) (M : proj1_sig a p) =>
           L (fun N : proj1_sig a p -> p => N M)).
           
Definition ep_implies (a b: Epistemic_Prop): Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
        (fun p : Prop => proj1_sig a p -> proj1_sig b p)
        (fun (p : Prop) (L : ((proj1_sig a p -> proj1_sig b p) -> p) -> p)
             (M : proj1_sig a p) =>
           proj2_sig b p
                     (fun N : proj1_sig b p -> p =>
                        L (fun O : proj1_sig a p -> proj1_sig b p => N (O M)))).

Definition ep_and (a b: Epistemic_Prop): Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
        (fun p : Prop => proj1_sig a p /\ proj1_sig b p)
        (fun (p : Prop) (M : (proj1_sig a p /\ proj1_sig b p -> p) -> p) =>
           conj
             (proj2_sig a p
                        (fun Na : proj1_sig a p -> p =>
                           M (fun O : proj1_sig a p /\ proj1_sig b p => Na (proj1 O))))
             (proj2_sig b p
                        (fun Nb : proj1_sig b p -> p =>
                           M (fun O : proj1_sig a p /\ proj1_sig b p => Nb (proj2 O))))).

Definition ep_all (T: Type) (f: T -> Epistemic_Prop): Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
        (fun p : Prop => forall t : T, proj1_sig (f t) p)
        (fun (p : Prop) (A : ((forall t : T, proj1_sig (f t) p) -> p) -> p) (u : T) =>
           proj2_sig (f u) p
                     (fun B : proj1_sig (f u) p -> p =>
                        A (fun C : forall t : T, proj1_sig (f t) p => B (C u)))).

Definition ep_confirmed_equal (T: Type) (x y:T): Epistemic_Prop:=
  exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
        (fun p : Prop => (x = y -> p) -> p)
        (fun (p : Prop) (A : (((x = y -> p) -> p) -> p) -> p) (B : x = y -> p) =>
           A (fun C : (x = y -> p) -> p => C B)).

(** Other connectors that have to be defined indirectly. *)

Definition ep_or (a b:Epistemic_Prop):= ep_not (ep_and (ep_not a) (ep_not b)).

Definition ep_ex (T: Type) (f: T -> Epistemic_Prop):=
  ep_not (ep_all T (fun t: T => ep_not (f t))).

Definition ep_possible (a: Epistemic_Prop):= ep_not (ep_confirmed (ep_not a)).

Section Epistemic_proof_theory.

  (** We develop a Hilbert System for s4 modal logic. A natural deduction system
   might be added in the future. *)
  
  Notation EP:= Epistemic_Prop.

  Notation "|- F":= (EP_Theorem F) (at level 41).

  (** Before we start we establish our system is sound in the following sense:
   COQ guarantees ep_false is not an EP_Theorem (so if it is, COQ is inconsistent too).
   The conservativity result we prove later in the text is of course stronger.  
   *)

  Theorem ep_soundness: ~ |- ep_False.
  Proof.
    intro F; apply F.
  Defined.
  
  (** The first five properties we prove establishes that our system proves all classical
   first order logic theorems written with forall, implies and false. 
   Further results are provided in order to show that every other logical connector has the 
   intended meaning and to allow the reader to implement easily some other Hilbert systems 
   *)
  Section Basic_proof_theory_with_false_imply_and_forall.
    
    Theorem ep_modus_ponens (x y: EP): |- ep_implies x y -> |- x -> |- y.
    Proof.
      intros A B p; apply A; apply B.
    Defined.
    
    Theorem ep_all_intro (c: EP) (T: Type) (f: T -> EP):
      (forall w:T, |- ep_implies c (f w)) -> |- ep_implies c (ep_all T f).
    Proof.
      intros A p B t; apply (A t); apply B.
    Defined.

    Theorem ep_K (x y:EP): |- ep_implies x (ep_implies y x).
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); simpl; intros A B; apply A.
    Defined.
    
    Theorem ep_S (x y z:EP): |- ep_implies
                                  (ep_implies x (ep_implies y z))
                                  (ep_implies (ep_implies x y) (ep_implies x z)).
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); destruct z as (c, rc);
        simpl; intros A B C; apply (A C (B C)).
    Defined.  

    Theorem ep_Church_absurdity (x: EP):
    |- ep_implies (ep_implies (ep_implies x ep_False) ep_False) x.
    Proof.
      intro p; destruct x as (a, ra); simpl; intro L; apply (ra p L).
    Defined.

    Theorem ep_all_elim (T: Type) (f: T -> EP) (x: T):
    |- ep_implies (ep_all T f) (f x).
    Proof.
      intros p A; apply A.
    Defined.
    
  End Basic_proof_theory_with_false_imply_and_forall.

  Section Basic_modal_s4_results.
    
    Theorem ep_modal_necessitation_rule (x: EP):
      (|- x) -> (|- ep_confirmed x).
    Proof.
      destruct x as (a, ra); simpl; intros A p; simpl; intro B; apply B; apply A.
    Defined.

    Theorem ep_modal_reflexivity (x: EP): |- ep_implies (ep_confirmed x) x.
    Proof.
      destruct x as (a, ra); simpl; intros p A; simpl; simpl in A; apply ra; intro B;
        apply A; intro C; apply B; apply C.
    Defined.

    Theorem ep_modal_transitivity (x: EP):
    |- ep_implies (ep_confirmed x) (ep_confirmed (ep_confirmed x)).
    Proof.
      destruct x as (a, ra); simpl; intros p A; simpl; simpl in A; intro B;
        apply A; intro C; apply B; intro r; intro D; apply D; apply C.
    Defined.

    Theorem ep_modal_distribution_rule (x y:EP):
    |- ep_implies (ep_confirmed (ep_implies x y))
                  (ep_implies (ep_confirmed x) (ep_confirmed y)).
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); simpl; intros A B C. apply A;
        intro D; apply B; intro E; apply C; intro r; apply D; apply E.       
    Defined.

    Theorem ep_modal_reverse_Barcan_formula (T: Type) (f: T -> EP):
    |- ep_implies (ep_confirmed (ep_all T f))
                  (ep_all T (fun t: T => ep_confirmed (f t))).
    Proof.
      apply ep_all_intro; intros x p; simpl; intros A B; apply A; intro C; apply B; intro q;
        apply C. 
    Defined.
      
  End Basic_modal_s4_results.

  Section Results_about_equality.

    (** "ep_confirmed_equal" is the equality predicate of Epistemic_Prop. *)
    
    Theorem ep_confirmed_equal_reflexivity (T: Type) (x: T):|- ep_confirmed_equal T x x.
    Proof.
      intros p L; apply L; apply eq_refl. 
    Defined.
    
    Theorem ep_confirmed_equal_Leibniz_property (T: Type) (x y:T) (f: T -> EP):
    |- ep_implies (ep_confirmed_equal T x y) (ep_implies (f x) (f y)).
    Proof.
      intros p L M; apply (proj2_sig (f y)); intro N; apply L; intro E; apply N; rewrite <- E;
        apply M.
    Defined.   
    
  End Results_about_equality.

  Section Other_connectors.

    Theorem ep_or_left_intro (x y: EP): |- ep_implies x (ep_or x y).
    Proof.
      intros p L; simpl; simpl in L; intros (Mx, My); apply (Mx L).
    Defined.

    Theorem ep_or_right_intro (x y: EP): |- ep_implies y (ep_or x y).
    Proof.
      intros p L; simpl; simpl in L; intros (Mx, My); apply (My L).
    Defined.

    Theorem ep_or_elim (x y z:EP):
    |- ep_implies (ep_implies x z) (ep_implies (ep_implies y z) (ep_implies (ep_or x y) z)).
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); destruct z as (c, rc); simpl;
        intros L M N; apply rc; intro O; apply N; split; intro P.
      apply (O (L P)). apply (O (M P)).
    Defined.

    Theorem ep_and_intro (x y: EP): |- ep_implies x (ep_implies y (ep_and x y)).
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); simpl; intros A B; split.
      apply A. apply B.
    Defined.

    Theorem ep_and_left_elim (x y:EP): |- ep_implies (ep_and x y) x.
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); simpl; intro C; apply C.
    Defined.

    Theorem ep_and_right_elim (x y:EP): |- ep_implies (ep_and x y) y.
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); simpl; intro C; apply C.
    Defined.

    Theorem ep_definition_of_negation_in_terms_of_falsum (x: EP):
    |- (ep_implies (ep_not x) (ep_implies x ep_False)) /\
    |- (ep_implies (ep_implies x ep_False) (ep_not x)).
    Proof.
      destruct x as (a, ra); simpl; split; intro p; simpl; intro F; apply F.
    Defined.

    Theorem ep_ex_intro (T: Type) (f: T -> EP) (x: T):
    |- ep_implies (f x) (ep_ex T f).
    Proof.
      intros p A B; simpl in B; apply (B x A).
    Defined.
    
    Theorem ep_ex_elim (c: EP) (T: Type) (f: T -> EP):
      (forall w: T, |- ep_implies (f w) c) -> |- ep_implies (ep_ex T f) c.
    Proof.
      intros A p B; simpl in A; simpl in B; apply (proj2_sig c p); intro C; apply B;
        intros w D; apply C; apply (A w); apply D.
    Defined.       
    
  End Other_connectors.
  
  Section Further_miscellaneous_results.
    
    Theorem ep_Mendelson_Hilbert_system_absurdity (x y: EP):
    |- ep_implies (ep_implies (ep_not x) (ep_not y)) (ep_implies (ep_implies (ep_not x) y) x).
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); simpl; intros C D; apply ra;
        intro E. apply (C E (D E)).
    Defined.    

    Theorem ep_excluded_middle (x: EP): |- ep_or x (ep_not x).
    Proof.
      destruct x as (a, ra); intros p (L1, L2); simpl in L1; simpl in L2; apply (L2 L1). 
    Defined.

    Theorem ep_contraposition (x y:EP): |- ep_implies (ep_implies x y)
                                                      (ep_implies (ep_not y) (ep_not x)).
    Proof.
      intro p; destruct x as (a, ra); destruct y as (b, rb); simpl; intros L M N;
        apply (M (L N)).
    Defined.

    Theorem ep_reduction_ad_absurdum (x: EP): |- ep_implies (ep_not (ep_not x)) x.
    Proof.
      intro p; destruct x as (a, ra); simpl; intro L; apply (ra p L).
    Defined.
    
    Theorem ep_conj (x y: EP): |- x -> |- y -> |- ep_and x y.
    Proof.
      intros A B p; simpl; split. apply (proj2_sig x); intro C; apply C; apply A.
      apply (proj2_sig y); intro C; apply C; apply B.
    Defined.

    Theorem ep_proj1 (x y: EP): |- ep_and x y -> |- x.
    Proof.
      intros A p; apply (proj2_sig x); intro B. destruct (A p) as (Ax, Ay); apply (B Ax).
    Defined.

    Theorem ep_proj2 (x y: EP): |- ep_and x y -> |- y.
    Proof.
      intros A p; apply (proj2_sig y); intro B. destruct (A p) as (Ax, Ay); apply (B Ay).
    Defined.

    Theorem ep_or_introl (x y: EP): |- x -> |- ep_or x y.
    Proof.
      intros A p B; apply (proj1 B); apply A.
    Defined.

    Theorem ep_or_intror (x y: EP): |- y -> |- ep_or x y.
    Proof.
      intros A p B; apply (proj2 B); apply A.
    Defined.

    Theorem ep_or_induction (x y z: EP):
    |- ep_implies x z -> |- ep_implies y z -> |- ep_implies (ep_or x y) z.
    Proof.                                                            
      destruct x as (a, ra); destruct y as (b, rb); destruct z as (c, rc); unfold ep_implies;
        simpl; intros M N p Q; apply rc; intro R; apply Q; split; intro T; apply R.
      apply (M p T). apply (N p T).
    Defined.          

    Theorem ep_true_is_a_theorem: |- ep_True.
    Proof.
      intros p; simpl; apply I.
    Defined.

    Theorem ep_heyting (x y z:EP):
    |- ep_implies (ep_and x y) z <-> |- ep_implies x (ep_implies y z).
    Proof.  
      destruct x as (a, ra); destruct y as (b, rb); destruct z as (c, rc); unfold ep_implies;
        unfold ep_and; simpl; split. intros F q Ga Gb; apply F; split. apply Ga. apply Gb.
      intros F q G. apply F; apply G.
    Defined.    
    
    Theorem ep_Peirce_law (x y:EP): |- ep_implies (ep_implies (ep_implies x y) x) x.
    Proof.
      destruct x as (a, ra); destruct y as (b, rb); intro p; simpl; intros L;
        apply ra; intros M; apply M; apply L; intro N; apply rb; intro Q; apply (M N).
    Defined.
    
    Theorem ep_explosion (x: EP): |- ep_implies ep_False x.
    Proof.
      destruct x as (a, ra); unfold ep_False; intros p A; simpl; simpl in A; apply ra;
        intros; apply A.
    Defined.

  End Further_miscellaneous_results.
  
End Epistemic_proof_theory.

Section Translations_between_Prop_and_Epistemic_Prop_and_conservativity_results.

  Notation EP:= Epistemic_Prop.

  Definition prop_to_epistemic_prop (a: Prop): Epistemic_Prop:=
    exist (fun g : Prop -> Prop => forall p : Prop, ((g p -> p) -> p) -> g p)
          (fun p : Prop => (a -> p) -> p)
          (fun (p : Prop) (A : (((a -> p) -> p) -> p) -> p) (B : a -> p) =>
             A (fun C : (a -> p) -> p => C B)).

  Definition epistemic_prop_to_prop (b: EP): Prop:= forall p: Prop, proj1_sig b p.

  Theorem prop_to_ep_confirmed (a: Prop):
    EP_Theorem (ep_implies (prop_to_epistemic_prop a)
                           (ep_confirmed (prop_to_epistemic_prop a))).
  Proof.
    intros p L; simpl; simpl in L; intro M; apply L; intro N; apply M; intros q O; apply (O N).
  Defined.    
  
  Section Conservativity.

    Theorem prop_to_epistemic_prop_theorem (a: Prop):
      a -> EP_Theorem (prop_to_epistemic_prop a).
    Proof.
      intros A p B; apply (B A).
    Defined.

    Theorem epistemic_prop_to_prop_theorem (b: EP):
      EP_Theorem b -> epistemic_prop_to_prop b.
    Proof.
      intros A p; apply A.
    Defined.

    Theorem ep_translation_involution:
      forall a: Prop, a <-> epistemic_prop_to_prop (prop_to_epistemic_prop a).
    Proof.
      intros a; split. intros A q B; apply (B A). intro C; apply (C a); intro D; apply D.
    Defined.

    Theorem epistemic_classical_logic_conservativity_over_coq_intuitionistic_logic:
      forall a:Prop,
        a <-> EP_Theorem (prop_to_epistemic_prop a).
    Proof.
      intro a; split. apply prop_to_epistemic_prop_theorem.
      intro B; apply ep_translation_involution; apply epistemic_prop_to_prop_theorem; apply B.
    Defined.      
      
  End Conservativity.

  Section Intuitionistic_connectors_in_EP.

    (** The previous conservativity theorem is a priori not very informative because the 
        arguments in prop on which it is applied are very general and lack of structure.
        In the following we examine how every logical connector is translated. It turns out
        we get every step of the inductive definition of the "Gödel-MacKinsey-Tarski
        translation" of a given formula from ordinary logic to modal s4 logic. As a result,
        for every formula f (whenever it is explicitely build from atomic formulas and logical
        connectors so that the GMT translation could be applied to it), 
        "prop_to_epistemic_prop f" is provably equivalent (in the modal s4 logic defined 
        above) to its GMT translation.
     *)

    Notation "a == b":= (EP_Theorem (ep_implies a b) /\
                         EP_Theorem (ep_implies b a)) (at level 42).
    
    (** Connectors which are the same as in the COQ case*)

    Theorem prop_to_ep_true: (prop_to_epistemic_prop True) == ep_True.
    Proof.
      split; intros p A; simpl in A; simpl. apply I. intro B; apply (B A).
    Defined.

    Theorem prop_to_ep_false: (prop_to_epistemic_prop False) == ep_False.
    Proof.
      split; intros p A; simpl; simpl in A. apply A; apply False_ind. intro B; apply A.
    Defined.

    Theorem prop_to_ep_equal (T: Type) (x y:T):
      prop_to_epistemic_prop (x = y) == ep_confirmed_equal T x y.
    Proof.
      split; intros p L; apply L.
    Defined.    

    Theorem prop_to_ep_and (a b: Prop):
      (prop_to_epistemic_prop (a /\ b)) == (ep_and (prop_to_epistemic_prop a)
                                                   (prop_to_epistemic_prop b)).
    Proof.
      split. intros p L; simpl; simpl in L; split; intro M; apply L; intro N; apply M; apply N.
      intros p (La, Lb); simpl; simpl in La; simpl in Lb; intro M; apply Lb; intro Nb;
        apply La; intro Na; apply M; split. apply Na. apply Nb.
    Defined.

    Theorem prop_to_ep_or (a b:Prop):      
      (prop_to_epistemic_prop (a \/ b)) == (ep_or (prop_to_epistemic_prop a)
                                                  (prop_to_epistemic_prop b)).
    Proof.
      split. intros p L; simpl; simpl in L; intros (Ma, Mb); apply L; apply or_ind; intro N.
      apply Ma; intro O; apply (O N). apply Mb; intro O; apply (O N).
      intros p L; simpl; simpl in L; intro M; apply L; split; intro N; apply N; intro O;
        apply M. left; apply O. right; apply O.
    Defined.

    Theorem prop_to_ep_ex (T: Type) (f: T -> Prop):
      prop_to_epistemic_prop (exists t:T, f t) ==
      ep_ex T (fun t: T => prop_to_epistemic_prop (f t)).
    Proof.
      split; intros p A; simpl; simpl in A.
      intro B; apply A; apply ex_ind; intros u C; apply (B u); intro D; apply (D C).
      intro B; apply A; intros t C; apply C; intro D; apply B; exists t; apply D.
    Defined.
    
    (** Connectors which have to be changed by modal_necessity *)

    Theorem prop_to_ep_implies (a b:Prop):
      (prop_to_epistemic_prop (a -> b)) == ep_confirmed
                                             (ep_implies (prop_to_epistemic_prop a)
                                                         (prop_to_epistemic_prop b)).
    Proof.
      split; intros c L; simpl; simpl in L; intro M; apply L; intro N; apply M.
      intros d P Q; apply P; intro R; apply (Q (N R)).
      intro P; apply N; intro Q. apply (Q P). apply Q.
    Defined.

    Theorem prop_to_ep_not (a: Prop):
      (prop_to_epistemic_prop (~ a)) == ep_confirmed (ep_not (prop_to_epistemic_prop a)).
    Proof.
      split; intros p L; simpl; simpl in L; intro M.
      apply L; intro N; apply M; intros q; intro P; apply P; intro Q; apply False_ind; apply N;
        apply Q. apply L; intro N; apply M; intro P; apply N; intro Q; apply (Q P).
    Defined.
      
    Theorem prop_to_ep_all (T: Type) (f: T -> Prop):
      prop_to_epistemic_prop (forall t:T, f t) ==
      ep_confirmed (ep_all T (fun t: T => prop_to_epistemic_prop (f t))).
    Proof.
      split; intros p L; simpl in L; simpl; intros M; apply L; intro N; apply M.
      intros q t O; apply O; apply N. intro t; apply (N (f t) t); intro P; apply P.
    Defined.            
      
  End Intuitionistic_connectors_in_EP.

  Section Decidability.

    (** How our EP deals with the notion of decidability *)
    
    Definition ep_decidable (a: EP):EP:= ep_or (ep_confirmed a) (ep_confirmed (ep_not a)).

    Theorem prop_to_ep_decidable (a: Prop):
      EP_Theorem (ep_decidable (prop_to_epistemic_prop a)) <-> (a \/ ~ a).
    Proof.
      unfold EP_Theorem; split.
      intros L; simpl in L; apply L with (p:= a \/ ~a); split;
        intro E; apply E; intro F. left; apply (F a); intro G; apply G.
      right; intro G. apply (F False); intro K; apply (K G).
      simpl; intros C p (Dy, Dn). destruct C as [Cy| Cn].
      apply Dy; intro E; apply E; intros q F; apply (F (Cy)).
      apply Dn; intro E; apply E; intros q F; apply F; intro G; apply False_ind; apply (Cn G).
    Defined.
    
  End Decidability.
    
End Translations_between_Prop_and_Epistemic_Prop_and_conservativity_results.
