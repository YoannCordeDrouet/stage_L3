Require Import PeanoNat List Bool.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.
Require Import Lia.
Require Import Coq.NArith.Nnat.
Require Import Coq.Numbers.Natural.Abstract.NDiv.
Require Import Ring.


(* =========== Définition des types des objets ===============

   - Les signaux sont représentés par des entiers naturels.
   - Les règles sont représentées par des formules logiques dont les éléments
     atomiques sont de la forme (k,s) (qui code la règle de signaux k.s)
     (Dans toute la suite on appellera "formule" ces formules sur les signaux.
   - Une règle est un couple (phi,s) où phi est une formule et s un signal.
     Elle s'interprète comme "si phi est vraie alors le signal s apparait sur
     case" (on a vu que quitte à découper en plusieurs règles et à décaler les 
     indices on pouvait se ramener au cas d'un seul signal produit avec aucun 
     décalage).
   - Les règles sont stockées sous forme de liste.
   - Une configuration est une fonction qui a un entier relatif donne une liste
     de signaux.
*)
   
Definition signal := Z.
Inductive signal_form :=
  | f_true : signal_form
  | f_false : signal_form
  | f_atome : (Z * signal) -> signal_form
  | f_and : signal_form -> signal_form -> signal_form
  | f_or : signal_form -> signal_form -> signal_form
  | f_not : signal_form -> signal_form.
Definition rule : Type := signal_form * signal.
Definition rules := list rule.
Definition config := Z -> list signal.
Definition empty_config : config := fun x => [].

Fixpoint signal_sat_z (c : config) (z : Z) (phi : signal_form) : bool :=
  match phi with
  | f_true => true
  | f_false => false
  | f_atome (k,s) => existsb (fun x => x=?s) (c (z+k))
  | f_and phi1 phi2 => (signal_sat_z c z phi1) && (signal_sat_z c z phi2)
  | f_or phi1 phi2 => (signal_sat_z c z phi1) || (signal_sat_z c z phi2)
  | f_not psi => negb (signal_sat_z c z psi)
  end.

Definition delta_one_rule (r : rule) (c_pred : config) (c : config) : config := 
  fun z => 
    match r with (phi,s) =>
     if (signal_sat_z c_pred z phi) then s::(c z) else (c z)
     end.
 
Fixpoint delta (rs : rules) (c : config) : config :=
  match rs with
    | [] => empty_config
    | t::q => delta_one_rule t c (delta q c)
  end.

(* delta_n : appliquer n+1 fois delta *)
Fixpoint delta_n (rs : rules) (c : config) (n : nat) :=
  match n with
  | 0%nat => c 
  | S m => delta_n rs (delta rs c) m
  end.
  
(*================= signaux de fischer ==========================*)
Definition init_1 : signal := 0.
Definition init_2 : signal:= 1.
Definition init_3 : signal:= 2.
Definition wall : signal := 3.
Definition slow_1 : signal := 4.
Definition slow_2 : signal := 5.
Definition slow_3 : signal := 6.
Definition build_r : signal := 7.
Definition build_l : signal := 8.
Definition gen : signal := 9.
Definition bounce_r : signal := 10.
Definition bounce_l : signal := 11.
Definition composite : signal := 12.

(* =============== regles ======================= *)

(* init *)
Definition phi_init_1 : signal_form := f_atome (0,init_1).
Definition rule_init_1_to_2 : rule := (phi_init_1,init_2).
Definition rule_init_1_to_wall : rule := (phi_init_1,wall).
Definition rule_init_1_to_slow : rule := (phi_init_1,slow_1).
Definition rule_init_1_to_composite : rule := (phi_init_1,composite).

Definition phi_init_2 : signal_form := f_atome (0,init_2).
Definition rule_init_2_to_3 : rule := (phi_init_2,init_3).

Definition phi_init_3 : signal_form := f_atome (0,init_3).
Definition rule_init_3_to_build_r : rule := (phi_init_3,build_r).

(* slow *)
Definition phi_slow_1_to_2 : signal_form := f_and (f_atome (0,slow_1)) (f_not (f_atome (0,build_r))).
Definition rule_slow_1_to_2 : rule := (phi_slow_1_to_2,slow_2).

Definition phi_slow_2_to_3 : signal_form := f_atome (0,slow_2).
Definition rule_slow_2_to_3 : rule := (phi_slow_2_to_3,slow_3).

Definition phi_slow_3_to_1 : signal_form := f_atome (-1,slow_3).
Definition rule_slow_3_to_1 : rule := (phi_slow_3_to_1,slow_1).

Definition phi_slow_1_to_1 : signal_form := f_and (f_atome (-1,slow_1)) (f_atome (-1,build_r)).
Definition rule_slow_1_to_1 : rule := (phi_slow_1_to_1,slow_1).

(* wall *)
Definition phi_wall_wall : signal_form := f_atome (0,wall).
Definition rule_wall_wall : rule := (phi_wall_wall,wall).

(* composite *)
Definition phi_composite : signal_form := f_atome (1,composite).
Definition rule_composite : rule := (phi_composite, composite).

(* build *)
Definition phi_create_gen : signal_form := f_and (f_atome (-1,slow_1)) (f_atome (-1,build_r)).
Definition rule_create_gen : rule := (phi_create_gen,gen).

Definition phi_gen_0 : signal_form := f_atome (0,gen).
Definition rule_gen_to_wall : rule := (phi_gen_0,wall).

Definition phi_gen_1 : signal_form := f_atome (1,gen).
Definition rule_gen_to_build_l : rule := (phi_gen_1, build_l).
Definition rule_gen_to_bounce_l : rule := (phi_gen_1, bounce_l).

Definition phi_build_l_build_l : signal_form := f_and (f_atome (1,build_l)) (f_not (f_atome (1,wall))).
Definition rule_build_l_build_l : rule := (phi_build_l_build_l, build_l).

Definition phi_build_l_to_build_r : signal_form := f_and (f_atome (-1,build_l)) (f_atome (-1,wall)).
Definition rule_build_l_to_build_r : rule := (phi_build_l_to_build_r, build_r).

Definition phi_build_r_build_r : signal_form := f_and (f_not (f_atome (-1,slow_1))) (f_atome (-1,build_r)).
Definition rule_build_r_build_r : rule := (phi_build_r_build_r,build_r).

(* bounce *)
Definition phi_bounce_l_bounce_l : signal_form := f_and (f_atome (1,bounce_l)) (f_not (f_atome (1,wall))).
Definition rule_bounce_l_bounce_l : rule := (phi_bounce_l_bounce_l, bounce_l).

Definition phi_bounce_l_to_bounce_r : signal_form := f_and (f_atome (-1,bounce_l)) (f_atome (-1,wall)).
Definition rule_bounce_l_to_bounce_r : rule := (phi_bounce_l_to_bounce_r, bounce_r).

Definition phi_bounce_r_bounce_r : signal_form := f_and (f_atome (-1,bounce_r)) (f_not (f_atome (-1,wall))).
Definition rule_bounce_r_bounce_r : rule := (phi_bounce_r_bounce_r, bounce_r).

Definition phi_bounce_r_to_bounce_l : signal_form := f_and (f_atome (1,bounce_r)) (f_atome (1,wall)).
Definition rule_bounce_r_to_bounce_l : rule := (phi_bounce_r_to_bounce_l, bounce_l).

(*cette dernière règle est peut être à changer (TO SEE) *)
Definition phi_bounce_l_to_composite : signal_form := f_atome (1,bounce_l).
Definition rule_bounce_l_to_composite : rule := (phi_bounce_l_to_composite,composite).

(* REGLES *)

Definition regles : rules :=
  [
    rule_init_1_to_2; 
    rule_init_1_to_wall;
    rule_init_1_to_slow;
    rule_init_1_to_composite;
    rule_init_2_to_3;
    rule_init_3_to_build_r;
    rule_slow_1_to_2;
    rule_slow_2_to_3;
    rule_slow_3_to_1;
    rule_slow_1_to_1;
    rule_wall_wall;
    rule_composite;
    rule_create_gen;
    rule_gen_to_wall;
    rule_gen_to_build_l;
    rule_gen_to_bounce_l;
    rule_build_l_build_l;
    rule_build_l_to_build_r;
    rule_build_r_build_r;
    rule_bounce_l_bounce_l;
    rule_bounce_l_to_bounce_r;
    rule_bounce_r_bounce_r;
    rule_bounce_r_to_bounce_l;
    rule_bounce_l_to_composite
  ].

(* définition de la configuration initiale *) 

Definition config_0 : config := fun z => if z =? 0 then [init_1] else [].

(* Des Lemmes utiles *)

Lemma condition_appartenance (rs : rules) (c : config) (z : Z) (s : signal) :
  In s (delta rs c z) <-> exists phi, signal_sat_z c z phi = true /\ In (phi, s) rs.
Proof.
  split.
  + intro.
    induction rs.
    - simpl in H.
      contradiction.
    - destruct a as [psi s_prime].
      simpl in H.
      destruct (signal_sat_z c z psi) eqn:Hsat.
      * simpl in H.
        destruct H.
        -- exists psi.
           split.
           ** exact Hsat.
           ** simpl.
              left.
              rewrite H.
              reflexivity.
        -- apply IHrs in H.
           destruct H as [phi [H1 H2]].
           exists phi.
           split.
           ** exact H1.
           ** simpl.
              right.
              exact H2.
      * apply IHrs in H.
        destruct H as [phi [H1 H2]].
        exists phi.
        split.
        ** exact H1.
        ** simpl.
           right.
           exact H2.
  + intro.
    induction rs.
    - destruct H as [phi [H1 H2]].
      simpl in H2.
      contradiction.
    - destruct a as [psi s_prime].
      destruct H as [phi [H1 H2]].
      simpl in H2.
      destruct H2.
      * simpl.
        inversion H.
        rewrite H1.
        simpl.
        left; reflexivity.
      * simpl.
        destruct (signal_sat_z c z psi).
        1: simpl; right.
        all: apply IHrs.
        all: exists phi.
        all: split.
        1,3: exact H1.
        all: exact H.
Qed.

Lemma in_and_exists (l : list signal) (s : signal) :
  existsb (fun x => x =? s) l = true <-> In s l.
Proof.
  induction l.
  + simpl.
    split.
    - intro. discriminate H.
    - intro. contradiction.
  + simpl.
    rewrite orb_true_iff.
    split.
    all: intro; destruct H.
    2,4: apply IHl in H; right; exact H.
    - left.
      rewrite Z.eqb_eq in H.
      exact H.
    - left.
      rewrite Z.eqb_eq.
      exact H.
Qed.

Lemma not_in_and_exists (l : list signal) (s : signal) :
  negb (existsb (fun x => x =? s) l) = true <-> ~(In s l).
Proof.
  rewrite <- (not_iff_compat (in_and_exists l s)).
  rewrite not_true_iff_false.
  apply negb_true_iff.
Qed.

Lemma delta_delta_n_comm (rs : rules) (n : nat) (s : signal) (z : Z) :
  forall c, In s (delta_n rs (delta rs c) n z) <-> In s (delta rs (delta_n rs c n) z).
Proof.
  induction n.
  + reflexivity.
  + intro.
    simpl.
    specialize (IHn (delta rs c)).
    exact IHn.
Qed.

Lemma delta_m_delta_n (rs : rules) (n : nat) (m : nat) (s : signal) (z : Z) :
  forall c, In s (delta_n rs (delta_n rs c m) n z) <-> In s (delta_n rs c (n+m) z).
Proof.
  induction m.
  + rewrite Nat.add_0_r.
    reflexivity.
  + simpl.
    intro.
    specialize (IHm (delta rs c)).
    rewrite Nat.add_succ_r.
    exact IHm.
Qed.

(* ================ condition appartenance à la configuration suivante ==================== *)

(* init_1 *)
Lemma in_init_1 (c : config) (z : Z) :
  ~In init_1 ((delta regles c) z).
Proof.
  intro.
  rewrite (condition_appartenance regles c z init_1) in H.
  destruct H as [phi [H1 H2]].
  unfold regles, In in H2.
  destruct H2 as 
  [H | [H | [H | [H | [H | [H | [H | [H
  | [H | [H | [H | [H | [H | [H | [H 
  | [H | [H | [H | [H | [H | [H | [H 
  | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
  all:inversion H.
Qed.
 
Lemma in_init_n (c : config) (z : Z) (n : nat) :
  (n>0)%nat -> ~In init_1 ((delta_n regles c n) z).
Proof.
  destruct n.
  + intro.
    inversion H.
  + cbn [delta_n].
    intro.
    intro.
    apply delta_delta_n_comm in H0.
    apply (in_init_1 (delta_n regles c n) z).
    exact H0.
Qed.

(* init_2 *)
Lemma in_init_2_1 (c : config) (z : Z) :
  In init_2 ((delta regles c) z) <-> signal_sat_z c z phi_init_1 = true.
Proof.
  rewrite (condition_appartenance regles c z init_2).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    rewrite H2.
    exact H1.
  + intro.
    exists phi_init_1.
    split.
    - exact H.
    - simpl.
      left; reflexivity.
Qed.

Lemma in_init_2_2 (c : config) (z : Z) :
  signal_sat_z c z phi_init_1 = true <-> In init_1 (c z).
Proof.
  simpl.
  rewrite Z.add_0_r.
  apply in_and_exists.
Qed.

Lemma in_init_2 (c : config) (z : Z) :
  In init_2 ((delta regles c) z) <-> In init_1 (c z).
Proof.
  rewrite in_init_2_1.
  apply in_init_2_2.
Qed.

(* init_3 *)

Lemma in_init_3_1 (c : config) (z : Z) :
  In init_3 ((delta regles c) z) <-> signal_sat_z c z phi_init_2 = true.
Proof.
  rewrite (condition_appartenance regles c z init_3).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    rewrite H2.
    exact H1.
  + intro.
    exists phi_init_2.
    split.
    - exact H.
    - simpl.
      right; right; right; right; left; reflexivity.
Qed.

Lemma in_init_3_2 (c : config) (z : Z) :
  signal_sat_z c z phi_init_2 = true <-> In init_2 (c z).
Proof.
  simpl.
  rewrite Z.add_0_r.
  apply in_and_exists.
Qed.

Lemma in_init_3 (c : config) (z : Z) :
  In init_3 ((delta regles c) z) <-> In init_2 (c z).
Proof.
  rewrite in_init_3_1.
  apply in_init_3_2.
Qed.

(* wall *)

Lemma in_wall_1 (c : config) (z : Z) :
  In wall ((delta regles c) z) <-> 
  signal_sat_z c z phi_wall_wall  = true 
  \/ signal_sat_z c z phi_init_1 = true
  \/ signal_sat_z c z phi_gen_0 = true.
Proof.
  rewrite (condition_appartenance regles c z wall).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    1: right; left.
    2: left.
    3: right; right.
    all:rewrite H2.
    all:exact H1.
  + intro.
    destruct H as [H |[H | H]].
    1: exists phi_wall_wall.
    2: exists phi_init_1.
    3: exists phi_gen_0.
    all: split.
    1,3,5: exact H.
    all: simpl.
    - right; right; right; right; right; right; right; right; right; right; left; reflexivity.
    - right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_wall_2 (c : config) (z : Z) :
  signal_sat_z c z phi_wall_wall  = true 
  \/ signal_sat_z c z phi_init_1 = true
  \/ signal_sat_z c z phi_gen_0 = true <-> 
  In wall (c z) 
  \/ In init_1 (c z)
  \/ In gen (c z).
Proof.
  simpl.
  rewrite Z.add_0_r.
  split.
  + intro.
    destruct H as [H | [H | H]].
    all: apply in_and_exists in H.
    - left; exact H.
    - right; left; exact H.
    - right; right; exact H.
  + intro.
    destruct H as [H | [H | H]].
    all: apply in_and_exists in H.
    - left; exact H.
    - right; left; exact H.
    - right; right; exact H.
Qed.


Lemma in_wall (c : config) (z : Z) :
  In wall ((delta regles c) z) <->
  In wall (c z) 
  \/ In init_1 (c z)
  \/ In gen (c z).
Proof.
  rewrite in_wall_1.
  apply in_wall_2.
Qed.

(* slow_1 *)

Lemma in_slow_1_1 (c : config) (z : Z) :
  In slow_1 ((delta regles c) z) <-> 
  signal_sat_z c z phi_init_1 = true
  \/ signal_sat_z c z phi_slow_3_to_1 = true 
  \/ signal_sat_z c z phi_slow_1_to_1 = true.
Proof.
  rewrite (condition_appartenance regles c z slow_1).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    1: left.
    2: right; left.
    3: right; right.
    all:rewrite H2.
    all:exact H1.
  + intro.
    destruct H as [H | [H | H]].
    1: exists phi_init_1.
    2: exists phi_slow_3_to_1.
    3: exists phi_slow_1_to_1.
    all: split.
    1,3,5: exact H.
    all: simpl.
    - right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_slow_1_2 (c : config) (z : Z) :
  signal_sat_z c z phi_init_1 = true
  \/ signal_sat_z c z phi_slow_3_to_1 = true 
  \/ signal_sat_z c z phi_slow_1_to_1 = true <-> 
  In init_1 (c z)
  \/ In slow_3 (c (z-1)) 
  \/ (In slow_1 (c (z - 1)) /\ In build_r (c (z - 1))).
Proof.
  simpl.
  rewrite Z.add_0_r.
  change (z + -1) with (z - 1).
  rewrite andb_true_iff.
  split.
  + intro.
    destruct H as [H | [H | [H H1]]].
    all: apply in_and_exists in H.
    3: apply in_and_exists in H1.
    - left; exact H.
    - right; left; exact H.
    - right; right; split.
      -- exact H.
      -- exact H1.
  + intro.
    destruct H as [H | [H | [H H1]]].
    all: apply in_and_exists in H.
    3: apply in_and_exists in H1.
    - left; exact H.
    - right; left; exact H.
    - right; right; split.
      -- exact H.
      -- exact H1.
Qed.

Lemma in_slow_1 (c : config) (z : Z) :
  In slow_1 ((delta regles c) z) <->
  In init_1 (c z)
  \/ In slow_3 (c (z-1)) 
  \/ (In slow_1 (c (z - 1)) /\ In build_r (c (z - 1))).
Proof.
  rewrite in_slow_1_1.
  apply in_slow_1_2.
Qed.

(* slow_2 *)

Lemma in_slow_2_1 (c : config) (z : Z) :
  In slow_2 ((delta regles c) z) <-> 
  signal_sat_z c z phi_slow_1_to_2 = true.
Proof.
  rewrite (condition_appartenance regles c z slow_2).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    rewrite H2.
    exact H1.
  + intro.
    exists phi_slow_1_to_2.
    split.
    - exact H.
    - simpl.
      right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_slow_2_2 (c : config) (z : Z) :
  signal_sat_z c z phi_slow_1_to_2 = true <-> 
  (In slow_1 (c z) /\ ~(In build_r (c z))).
Proof.
  simpl.
  rewrite Z.add_0_r.
  change (z + -1) with (z - 1).
  rewrite andb_true_iff.
  split.
  + intro.
    destruct H as [H1 H2].
    apply in_and_exists in H1.
    apply not_in_and_exists in H2.
    split.
    - exact H1.
    - exact H2.
  + intro.
    destruct H as [H1 H2].
    apply in_and_exists in H1.
    apply not_in_and_exists in H2.
    split.
    - exact H1.
    - exact H2.
Qed.

Lemma in_slow_2 (c : config) (z : Z) :
  In slow_2 ((delta regles c) z) <->
  In slow_1 (c z) /\ ~(In build_r (c z)).
Proof.
  rewrite in_slow_2_1.
  apply in_slow_2_2.
Qed.

(* slow_3 *)

Lemma in_slow_3_1 (c : config) (z : Z) :
  In slow_3 ((delta regles c) z) <-> signal_sat_z c z phi_slow_2_to_3  = true.
Proof.
  rewrite (condition_appartenance regles c z slow_3).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    rewrite H2.
    exact H1.
  + intro.
    exists phi_slow_2_to_3.
    split.
    - exact H.
    - simpl.
      right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_slow_3_2 (c : config) (z : Z) :
  signal_sat_z c z phi_slow_2_to_3  = true <-> In slow_2 (c z).
Proof.
  simpl.
  rewrite Z.add_0_r.
  apply in_and_exists.
Qed.

Lemma in_slow_3 (c : config) (z : Z) :
  In slow_3 ((delta regles c) z) <-> In slow_2 (c z).
Proof.
  rewrite in_slow_3_1.
  apply in_slow_3_2.
Qed.

(* build_r *)

Lemma in_build_r_1 (c : config) (z : Z) :
  In build_r ((delta regles c) z) <-> 
  signal_sat_z c z phi_init_3 = true
  \/ signal_sat_z c z phi_build_l_to_build_r = true
  \/ signal_sat_z c z phi_build_r_build_r = true.
Proof.
  rewrite (condition_appartenance regles c z build_r).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    1: left.
    2: right; left.
    3: right; right.
    all:rewrite H2.
    all:exact H1.
  + intro.
    destruct H as [H | [H | H]].
    1: exists phi_init_3.
    2: exists phi_build_l_to_build_r.
    3: exists phi_build_r_build_r.
    all: split.
    1,3,5: exact H.
    all: simpl.
    - right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right;right; right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; right;right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_build_r_2 (c : config) (z : Z) :
  signal_sat_z c z phi_init_3 = true
  \/ signal_sat_z c z phi_build_l_to_build_r = true
  \/ signal_sat_z c z phi_build_r_build_r = true <->
  In init_3 (c z)
  \/ (In build_l (c (z - 1)) /\ In wall (c (z - 1)))
  \/ (~(In slow_1 (c (z - 1))) /\ In build_r (c (z - 1))).
Proof.
  simpl.
  rewrite Z.add_0_r.
  change (z + -1) with (z - 1).
  repeat rewrite andb_true_iff.
  split.
  + intro.
    destruct H as [H1 | [[H2 H3] | [H4 H5]]].
    - apply in_and_exists in H1.
      left; exact H1.
    - apply in_and_exists in H2, H3.
      right; left; split.
      -- exact H2.
      -- exact H3.
    - apply not_in_and_exists in H4.
      apply in_and_exists in H5.
      right; right; split.
      -- exact H4.
      -- exact H5.
  + intro.
    destruct H as [H1 | [[H2 H3] | [H4 H5]]].
    - apply in_and_exists in H1.
      left; exact H1.
    - apply in_and_exists in H2, H3.
      right; left; split.
      -- exact H2.
      -- exact H3.
    - apply not_in_and_exists in H4.
      apply in_and_exists in H5.
      right; right; split.
      -- exact H4.
      -- exact H5.
Qed.

Lemma in_build_r (c : config) (z : Z) :
  In build_r ((delta regles c) z) <->
  In init_3 (c z)
  \/ (In build_l (c (z - 1)) /\ In wall (c (z - 1)))
  \/ (~(In slow_1 (c (z - 1))) /\ In build_r (c (z - 1))).
Proof.
  rewrite in_build_r_1.
  apply in_build_r_2.
Qed.

(* build_l *)

Lemma in_build_l_1 (c : config) (z : Z) :
  In build_l ((delta regles c) z) <-> 
  signal_sat_z c z phi_gen_1 = true
  \/ signal_sat_z c z phi_build_l_build_l = true.
Proof.
  rewrite (condition_appartenance regles c z build_l).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    1: left.
    2: right.
    all:rewrite H2.
    all:exact H1.
  + intro.
    destruct H.
    1: exists phi_gen_1.
    2: exists phi_build_l_build_l.
    all: split.
    1,3: exact H.
    all: simpl.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_build_l_2 (c : config) (z : Z) :
  signal_sat_z c z phi_gen_1 = true
  \/ signal_sat_z c z phi_build_l_build_l = true <->
  In gen (c (z + 1))
  \/ (In build_l (c (z + 1)) /\ ~(In wall (c (z + 1)))).
Proof.
  simpl.
  rewrite andb_true_iff.
  split.
  + intro.
    destruct H as [H1 | [H2 H3]].
    - apply in_and_exists in H1.
      left; exact H1.
    - apply in_and_exists in H2.
      apply not_in_and_exists in H3.
      right; split.
      -- exact H2.
      -- exact H3.
  + intro.
    destruct H as [H1 | [H2 H3]].
    - apply in_and_exists in H1.
      left; exact H1.
    - apply in_and_exists in H2.
      apply not_in_and_exists in H3.
      right; split.
      -- exact H2.
      -- exact H3.
Qed.

Lemma in_build_l (c : config) (z : Z) :
  In build_l ((delta regles c) z) <->
  In gen (c (z + 1))
  \/ (In build_l (c (z + 1)) /\ ~(In wall (c (z + 1)))).
Proof.
  rewrite in_build_l_1.
  apply in_build_l_2.
Qed.

(* gen *)

Lemma in_gen_1 (c : config) (z : Z) :
  In gen ((delta regles c) z) <-> 
  signal_sat_z c z phi_create_gen = true.
Proof.
  rewrite (condition_appartenance regles c z gen).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    rewrite H2.
    exact H1.
  + intro.
    exists phi_create_gen.
    split.
    - exact H.
    - simpl.
      right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_gen_2 (c : config) (z : Z) :
  signal_sat_z c z phi_create_gen = true <->
  In slow_1 (c (z - 1)) /\ In build_r (c (z - 1)).
Proof.
  simpl.
  rewrite andb_true_iff.
  change (z + -1) with (z - 1).
  split.
  + intro.
    destruct H.
    apply in_and_exists in H.
    apply in_and_exists in H0.
    split.
    - exact H.
    - exact H0.
  + intro.
    destruct H.
    apply in_and_exists in H.
    apply in_and_exists in H0.
    split.
    - exact H.
    - exact H0.
Qed.

Lemma in_gen (c : config) (z : Z) :
  In gen ((delta regles c) z) <->
  In slow_1 (c (z - 1)) /\ In build_r (c (z - 1)).
Proof.
  rewrite in_gen_1.
  apply in_gen_2.
Qed.

(* bounce_r *)

Lemma in_bounce_r_1 (c : config) (z : Z) :
  In bounce_r ((delta regles c) z) <-> 
  signal_sat_z c z phi_bounce_l_to_bounce_r = true
  \/ signal_sat_z c z phi_bounce_r_bounce_r = true.
Proof.
  rewrite (condition_appartenance regles c z bounce_r).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    1: left.
    2: right.
    all:rewrite H2.
    all:exact H1.
  + intro.
    destruct H.
    1: exists phi_bounce_l_to_bounce_r.
    2: exists phi_bounce_r_bounce_r.
    all: split.
    1,3: exact H.
    all: simpl.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_bounce_r_2 (c : config) (z : Z) :
  signal_sat_z c z phi_bounce_l_to_bounce_r = true
  \/ signal_sat_z c z phi_bounce_r_bounce_r = true <->
  (In bounce_l (c (z - 1)) /\ In wall (c (z - 1)))
  \/ (In bounce_r (c (z - 1)) /\ ~(In wall (c (z - 1)))).
Proof.
  simpl.
  change (z + -1) with (z - 1).
  repeat rewrite andb_true_iff.
  split.
  + intro.
    destruct H as [[H1 H2] | [H3 H4]].
    - apply in_and_exists in H1, H2.
      left; split.
      -- exact H1.
      -- exact H2.
    - apply in_and_exists in H3.
      apply not_in_and_exists in H4.
      right; split.
      -- exact H3.
      -- exact H4.
  + intro.
    destruct H as [[H1 H2] | [H3 H4]].
    - apply in_and_exists in H1, H2.
      left; split.
      -- exact H1.
      -- exact H2.
    - apply in_and_exists in H3.
      apply not_in_and_exists in H4.
      right; split.
      -- exact H3.
      -- exact H4.
Qed.

Lemma in_bounce_r (c : config) (z : Z) :
  In bounce_r ((delta regles c) z) <->
  (In bounce_l (c (z - 1)) /\ In wall (c (z - 1)))
  \/ (In bounce_r (c (z - 1)) /\ ~(In wall (c (z - 1)))).
Proof.
  rewrite in_bounce_r_1.
  apply in_bounce_r_2.
Qed.

(* bounce_l *)

Lemma in_bounce_l_1 (c : config) (z : Z) :
  In bounce_l ((delta regles c) z) <-> 
  signal_sat_z c z phi_gen_1 = true 
  \/ signal_sat_z c z phi_bounce_l_bounce_l = true
  \/ signal_sat_z c z phi_bounce_r_to_bounce_l = true.
Proof.
  rewrite (condition_appartenance regles c z bounce_l).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    1: left.
    2: right; left.
    3: right; right.
    all:rewrite H2.
    all:exact H1.
  + intro.
    destruct H as [H |[H | H]].
    1: exists phi_gen_1.
    2: exists phi_bounce_l_bounce_l.
    3: exists phi_bounce_r_to_bounce_l.
    all: split.
    1,3,5: exact H.
    all: simpl.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_bounce_l_2 (c : config) (z : Z) :
  signal_sat_z c z phi_gen_1 = true 
  \/ signal_sat_z c z phi_bounce_l_bounce_l = true
  \/ signal_sat_z c z phi_bounce_r_to_bounce_l = true <->
  In gen (c (z + 1))
  \/ (In bounce_l (c (z + 1)) /\ ~(In wall (c (z + 1))))
  \/ (In bounce_r (c (z + 1)) /\ In wall (c (z + 1))).
Proof.
  simpl.
  repeat rewrite andb_true_iff.
  split.
  + intro.
    destruct H as [H0 |[[H1 H2] | [H3 H4]]].
    - apply in_and_exists in H0.
      left; exact H0.
    - apply in_and_exists in H1.
      apply not_in_and_exists in H2.
      right; left; split.
      -- exact H1.
      -- exact H2.
    - apply in_and_exists in H3, H4.
      right; right; split.
      -- exact H3.
      -- exact H4.
  + intro.
    destruct H as [H0 |[[H1 H2] | [H3 H4]]].
    - apply in_and_exists in H0.
      left; exact H0.
    - apply in_and_exists in H1.
      apply not_in_and_exists in H2.
      right; left; split.
      -- exact H1.
      -- exact H2.
    - apply in_and_exists in H3, H4.
      right; right; split.
      -- exact H3.
      -- exact H4.
Qed.

Lemma in_bounce_l (c : config) (z : Z) :
  In bounce_l ((delta regles c) z) <->
  In gen (c (z + 1))
  \/ (In bounce_l (c (z + 1)) /\ ~(In wall (c (z + 1))))
  \/ (In bounce_r (c (z + 1)) /\ In wall (c (z + 1))).
Proof.
  rewrite in_bounce_l_1.
  apply in_bounce_l_2.
Qed.

(* composite *)

Lemma in_composite_1 (c : config) (z : Z) :
  In composite ((delta regles c) z) <-> 
  signal_sat_z c z phi_init_1 = true 
  \/ signal_sat_z c z phi_composite = true 
  \/ signal_sat_z c z phi_bounce_l_to_composite = true.
Proof.
  rewrite (condition_appartenance regles c z composite).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    unfold regles, In in H2.
    destruct H2 as 
    [H | [H | [H | [H | [H | [H | [H | [H
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | [H | [H | [H | [H | [H 
    | [H | [H | H]]]]]]]]]]]]]]]]]]]]]]]].
    all:inversion H.
    1: left.
    2: right; left.
    3: right; right.
    all:rewrite H2.
    all:exact H1.
  + intro.
    destruct H as [H |[H | H]].
    1: exists phi_init_1.
    2: exists phi_composite.
    3: exists phi_bounce_l_to_composite.
    all: split.
    1,3,5: exact H.
    all: simpl.
    - right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
    - right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; reflexivity.
Qed.

Lemma in_composite_2 (c : config) (z : Z) :
  signal_sat_z c z phi_init_1 = true 
  \/ signal_sat_z c z phi_composite = true 
  \/ signal_sat_z c z phi_bounce_l_to_composite = true <->
  In init_1 (c z)
  \/ In composite (c (z + 1))
  \/ In bounce_l (c (z + 1)).
Proof.
  simpl.
  rewrite Z.add_0_r.
  split.
  + intro.
    destruct H as [H |[H | H]].
    all: apply in_and_exists in H.
    1: left.
    2: right; left.
    3: right; right.
    all : exact H.
  + intro.
    destruct H as [H |[H | H]].
    all: apply in_and_exists in H.
    1: left.
    2: right; left.
    3: right; right.
    all : exact H.
Qed.

Lemma in_composite (c : config) (z : Z) :
  In composite ((delta regles c) z) <->
  In init_1 (c z)
  \/ In composite (c (z + 1))
  \/ In bounce_l (c (z + 1)).
Proof.
  rewrite in_composite_1.
  apply in_composite_2.
Qed.

(* =============== Des propriétés simples ================= *)

Lemma not_init_propagation (c : config) (n : nat) (m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall z, ~(In init_1 (delta_n regles c (n+m) z)) /\ ~(In init_2 (delta_n regles c (n+m) z)) /\ ~(In init_3 (delta_n regles c (n+m) z))).
Proof.
  induction m.
  + rewrite Nat.add_0_r.
    intro; exact H.
  + intros.
    specialize (IHm H z).
    destruct IHm as [H1 [H2 H3]].
    replace (Nat.add n (S m)) with (S (n + m)) by lia.
    repeat split.
    2,3: cbn [delta_n].
    2,3: intro.
    2,3: apply delta_delta_n_comm in H0.
    2: apply in_init_2 in H0.
    3: apply in_init_3 in H0.
    2,3: contradiction.
    - apply in_init_n.
      lia.
Qed.

Lemma in_wall_m (z : Z) (c : config) (n m: nat) :
   (In wall (delta_n regles c n z)) \/ (In init_1 (delta_n regles c n z)) \/ (In gen (delta_n regles c n z)) 
   -> In wall (delta_n regles c (S(n+m)) z).
Proof.
  induction m.
  + intro.
    rewrite Nat.add_0_r.
    cbn [delta_n].
    apply delta_delta_n_comm.
    apply in_wall.
    exact H.
  + intros.
    replace (S (n + S m)) with (S (S (n+m))) by lia.
    cbn [delta_n] in *.
    apply delta_delta_n_comm.
    apply in_wall.
    left.
    exact (IHm H).
Qed.

(* =============== comportement de slow ================ *)

Lemma propagation_slow_1 (z1 : Z) (c : config) (n : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  ~(In build_r (delta_n regles c n z1)) /\
  In slow_1 (delta_n regles c n z1) /\ 
  ~(In slow_2 (delta_n regles c n z1)) /\ 
  ~(In slow_3 (delta_n regles c n z1)) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  ->
  ~(In slow_1 (delta_n regles c (n+1) z1)) /\ 
  In slow_2 (delta_n regles c (n+1) z1) /\ 
  ~(In slow_3 (delta_n regles c (n+1) z1)) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c (n+1) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+1) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+1) z2))).
Proof.
  intros.
  destruct H0 as [H0 [H1 [H2 [H3 H4]]]].
  replace (Nat.add n 1) with (S n) by lia.
  cbn [delta_n].  
  repeat split.
  1,3,4,5,6: intro.
  + apply delta_delta_n_comm in H5.
    apply in_slow_1 in H5.
    destruct H5 as [H5 | [H5 | H5]].
    - specialize (H z1).
      destruct H.
      contradiction.
    - assert (z1 <> z1 - 1) by lia.
      apply (H4 (z1 - 1)) in H6.
      destruct H6 as [H6 [H7 H8]].
      contradiction.
    - destruct H5.
      assert (z1 <> z1 - 1) by lia.
      apply (H4 (z1 - 1)) in H7.
      destruct H7 as [H7 [H8 H9]].
      contradiction.
  + apply delta_delta_n_comm in H5.
    apply in_slow_3 in H5.
    contradiction.
  + apply delta_delta_n_comm in H6.
    apply in_slow_1 in H6.
    destruct (z1 =? z2 - 1) eqn : Heq.
    1: rewrite Z.eqb_eq in Heq.
    2: rewrite Z.eqb_neq in Heq.
    all: destruct H6 as [H6 | [H6 | [H7 H6]]].
    1,4: specialize (H z2); destruct H; contradiction.
    1,2: rewrite <- Heq in H6; contradiction.
    1,2: apply (H4 (z2 - 1)) in Heq; destruct Heq as [H8 [H9 H10]]; contradiction.
  + apply delta_delta_n_comm in H6.
    apply in_slow_2 in H6.
    destruct H6.
    apply (H4 z2) in H5.
    destruct H5 as [H5 [H8 H9]].
    contradiction. 
  + apply delta_delta_n_comm in H6.
    apply in_slow_3 in H6.
    apply (H4 z2) in H5.
    destruct H5 as [H5 [H7 H8]].
    contradiction.
  + apply delta_delta_n_comm.
    apply in_slow_2.
    exact (conj H1 H0). 
Qed.

Lemma propagation_slow_2 (z1 : Z) (c : config) (n : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  ~(In slow_1 (delta_n regles c n z1)) /\ 
  In slow_2 (delta_n regles c n z1) /\ 
  ~(In slow_3 (delta_n regles c n z1)) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  ->
  ~(In slow_1 (delta_n regles c (n+1) z1)) /\ 
  ~(In slow_2 (delta_n regles c (n+1) z1)) /\ 
  In slow_3 (delta_n regles c (n+1) z1) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c (n+1) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+1) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+1) z2))).
Proof.
  intros.
  destruct H0 as [H0 [H1 [H2 H3]]].
  replace (Nat.add n 1) with (S n) by lia.
  cbn [delta_n].  
  repeat split.
  1,2,4,5,6: intro.
  + apply delta_delta_n_comm in H4.
    apply in_slow_1 in H4.
    destruct H4 as [H4 | [H4 | H4]].
    - specialize (H z1).
      destruct H.
      contradiction.
    - assert (z1 <> z1 - 1) by lia.
      apply (H3 (z1 - 1)) in H5.
      destruct H5 as [H5 [H6 H7]].
      contradiction.
    - destruct H4.
      assert (z1 <> z1 - 1) by lia.
      apply (H3 (z1 - 1)) in H6.
      destruct H6 as [H6 [H7 H8]].
      contradiction.
  + apply delta_delta_n_comm in H4.
    apply in_slow_2 in H4.
    destruct H4.
    contradiction.
  + apply delta_delta_n_comm in H5.
    apply in_slow_1 in H5.
    destruct (z1 =? z2 - 1) eqn : Heq.
    1: rewrite Z.eqb_eq in Heq.
    2: rewrite Z.eqb_neq in Heq.
    all: destruct H5 as [H5 | [H5 | [H5 H6]]].
    1,4: specialize (H z2); destruct H; contradiction.
    1,2: rewrite <- Heq in H5; contradiction.
    1,2: apply (H3 (z2 - 1)) in Heq; destruct Heq as [H7 [H8 H9]]; contradiction.
  + apply delta_delta_n_comm in H5.
    apply in_slow_2 in H5.
    destruct H5.
    apply (H3 z2) in H4.
    destruct H4 as [H4 [H7 H8]].
    contradiction. 
  + apply delta_delta_n_comm in H5.
    apply in_slow_3 in H5.
    apply (H3 z2) in H4.
    destruct H4 as [H4 [H6 H7]].
    contradiction.
  + apply delta_delta_n_comm.
    apply in_slow_3.
    exact H1. 
Qed.

Lemma propagation_slow_3 (z1 : Z) (c : config) (n : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  ~(In slow_1 (delta_n regles c n z1)) /\ 
  ~(In slow_2 (delta_n regles c n z1)) /\ 
  In slow_3 (delta_n regles c n z1) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  ->
  In slow_1 (delta_n regles c (n+1) (z1+1)) /\ 
  ~(In slow_2 (delta_n regles c (n+1) (z1+1))) /\ 
  ~(In slow_3 (delta_n regles c (n+1) (z1+1))) /\
  (forall z2, (z1+1) <> z2 -> 
    ~(In slow_1 (delta_n regles c (n+1) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+1) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+1) z2))).
Proof.
  intros.
  destruct H0 as [H0 [H1 [H2 H3]]].
  replace (Nat.add n 1) with (S n) by lia.
  cbn [delta_n].  
  repeat split.
  2,3,4,5,6: intro.
  + apply delta_delta_n_comm.
    apply in_slow_1.
    replace (z1 + 1 - 1) with z1 by lia.
    right; left; exact H2. 
  + apply delta_delta_n_comm in H4.
    apply in_slow_2 in H4.
    destruct H4.
    assert (z1 <> z1 + 1) by lia.
    apply H3 in H6.
    destruct H6.
    contradiction.
  + apply delta_delta_n_comm in H4.
    apply in_slow_3 in H4.
    assert (z1 <> z1 + 1) by lia.
    apply H3 in H5.
    destruct H5 as [H5 [H6 H7]].
    contradiction.
  + apply delta_delta_n_comm in H5.
    apply in_slow_1 in H5.
    assert (z1 <> z2 - 1) by lia.
    apply H3 in H6.
    destruct H6 as [H6 [H7 H8]].
    destruct H5 as [H5 | [H5 | [H5 H9]]].
    - specialize (H z2). 
      destruct H.
      contradiction.
    - contradiction.
    - contradiction.
  + apply delta_delta_n_comm in H5.
    apply in_slow_2 in H5.
    destruct H5.
    destruct (z1 =? z2) eqn:Heq.
    - rewrite Z.eqb_eq in Heq.
      rewrite <- Heq in H5.
      contradiction.
    - rewrite Z.eqb_neq in Heq.
      apply (H3 z2) in Heq.
      destruct Heq.
      contradiction. 
  + apply delta_delta_n_comm in H5.
    apply in_slow_3 in H5.
    destruct (z1 =? z2) eqn:Heq.
    - rewrite Z.eqb_eq in Heq.
      rewrite <- Heq in H5.
      contradiction.
    - rewrite Z.eqb_neq in Heq.
      apply (H3 z2) in Heq.
      destruct Heq as [Heq1 [Heq2 Heq3]].
      contradiction. 
Qed.

Lemma propagation_slow_m_1 (z1 : Z) (c : config) (n : nat) (m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall n0, (n0 < m)%nat -> ~(In build_r (delta_n regles c (n+3*n0) (z1 + Z.of_nat n0)))) /\
  In slow_1 (delta_n regles c n z1) /\ 
  ~(In slow_2 (delta_n regles c n z1)) /\ 
  ~(In slow_3 (delta_n regles c n z1)) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  ->
  (forall n0, (n0 < m)%nat -> 
  In slow_1 (delta_n regles c (n+3*n0+3) (z1 + Z.of_nat n0 + 1)) /\ 
  ~(In slow_2 (delta_n regles c (n+3*n0+3) (z1 + Z.of_nat n0 + 1))) /\ 
  ~(In slow_3 (delta_n regles c (n+3*n0+3) (z1 + Z.of_nat n0 + 1))) /\
  (forall z2, z1 + Z.of_nat n0 + 1 <> z2 ->  
    ~(In slow_1 (delta_n regles c (n+3*n0+3) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*n0+3) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*n0+3) z2)))).
Proof.
  induction m.
  + intros.
    inversion H1.
  + destruct m.
    - intros.
      destruct n0 eqn:Heq0.
      * destruct H0.
        apply (H0 0%nat) in H1. 
        specialize (not_init_propagation c n 1 H) as H3.
        specialize (not_init_propagation c n 2 H) as H4.
        replace (Nat.add (Nat.add n (Nat.mul 3 0)) 3) with (Nat.add (Nat.add n 2) 1) by lia.
        replace (z1 + Z.of_nat 0 + 1) with (z1 + 1) by lia.
        apply propagation_slow_3.
        ++ exact H4.
        ++ replace (Nat.add n 2) with (Nat.add (Nat.add n 1) 1) by lia.
           apply propagation_slow_2.
           -- exact H3.
           -- apply propagation_slow_1.
              ** exact H.
              ** split.
                 +++ rewrite Nat.add_0_r in H1.
                     replace (z1 + Z.of_nat 0) with z1 in H1 by lia.
                     exact H1.
                 +++ exact H2.
      * inversion H1.
        inversion H3.
    - intros.
      destruct (Nat.eqb n0 (S m)) eqn:Heq.
      * rewrite Nat.eqb_eq in Heq.
        destruct H0.
        apply (H0 n0) in H1. 
        specialize (not_init_propagation c n (3*n0+1) H) as H3.
        specialize (not_init_propagation c n (3*n0+2) H) as H4.
        rewrite Nat.add_assoc in H3.
        rewrite Nat.add_assoc in H4.
        replace (Nat.add (Nat.add n (Nat.mul 3 n0)) 3) with (Nat.add (Nat.add (Nat.add n (Nat.mul 3 n0)) 2) 1) by lia.
        apply propagation_slow_3.
        ++ exact H4.
        ++ replace (Nat.add (Nat.add n (Nat.mul 3 n0)) 2) with (Nat.add (Nat.add (Nat.add n (Nat.mul 3 n0)) 1) 1) by lia.
           apply propagation_slow_2.
           -- exact H3.
           -- apply propagation_slow_1.
              ** apply (not_init_propagation c n (3*n0) H).
              ** rewrite Heq.
                 assert (m < S m)%nat by lia.
                 assert (forall n0, (n0 < S m)%nat -> ~ In build_r (delta_n regles c (n + 3 * n0) (z1 + Z.of_nat n0))).
                 +++ intros.
                     assert (n1 < S (S m))%nat by lia.
                     apply (H0 n1 H7).
                 +++ specialize (IHm H (conj H6 H2) m H5).
                     split.
                     --- assert (S m < S (S m))%nat by lia.
                         apply (H0 (S m) H7).
                     --- replace (Nat.add n (Nat.mul 3 (S m))) with (Nat.add (Nat.add n (Nat.mul 3 m)) 3) by lia.
                         replace (z1 + Z.of_nat (S m)) with (z1 + Z.of_nat m + 1) by lia.
                         exact IHm.
      * rewrite Nat.eqb_neq in Heq.
        assert (n0 < S m)%nat by lia.
        destruct H0.
        assert (forall n0, (n0 < S m)%nat -> ~ In build_r (delta_n regles c (n + 3 * n0) (z1 + Z.of_nat n0))).
        ++ intros.
           assert (n1 < S (S m))%nat by lia.
           apply (H0 n1 H5).
        ++ apply (IHm H (conj H4 H3) n0 H2).
Qed.

Lemma propagation_slow_m_2 (z1 : Z) (c : config) (n : nat) (m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall n0, (n0 < m)%nat -> ~(In build_r (delta_n regles c (n+3*n0) (z1 + Z.of_nat n0)))) /\
  In slow_1 (delta_n regles c n z1) /\ 
  ~(In slow_2 (delta_n regles c n z1)) /\ 
  ~(In slow_3 (delta_n regles c n z1)) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  ->
  (forall n0, (n0 < m)%nat -> 
  ~(In slow_1 (delta_n regles c (n+3*n0+1) (z1 + Z.of_nat n0))) /\ 
  In slow_2 (delta_n regles c (n+3*n0+1) (z1 + Z.of_nat n0)) /\ 
  ~(In slow_3 (delta_n regles c (n+3*n0+1) (z1 + Z.of_nat n0))) /\
  (forall z2, z1 + Z.of_nat n0 <> z2 ->  
    ~(In slow_1 (delta_n regles c (n+3*n0+1) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*n0+1) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*n0+1) z2)))).
Proof.
  destruct m.
  + intros.
    inversion H1.
  + destruct n0.
    - intros.
      destruct H0.
      apply (H0 0%nat) in H1. 
      replace (z1 + Z.of_nat 0) with z1 in * by lia.
      replace (Nat.add n (Nat.mul 3 0)) with n in * by lia.
      apply propagation_slow_1.
      * exact H.
      * exact (conj H1 H2).
    - intros.
      destruct H0.
      apply propagation_slow_1.
      * apply not_init_propagation.
        exact H.
      * split.
        ++ apply (H0 (S n0) H1).
        ++ replace (Nat.add n (Nat.mul 3 (S n0))) with (Nat.add (Nat.add n (Nat.mul 3  n0)) 3) by lia.
           replace (z1 + Z.of_nat (S n0)) with (z1 + Z.of_nat n0 + 1) by lia. 
           assert (forall n0, (n0 < m)%nat -> ~ In build_r (delta_n regles c (n + 3 * n0) (z1 + Z.of_nat n0))).
           ** intros.
              assert (n1 < S m)%nat by lia.
              apply (H0 n1 H4).
           ** assert (n0<m)%nat by lia.
              apply (propagation_slow_m_1 z1 c n m H (conj H3 H2) n0 H4).
Qed.

Lemma propagation_slow_m_3 (z1 : Z) (c : config) (n : nat) (m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall n0, (n0 < m)%nat -> ~(In build_r (delta_n regles c (n+3*n0) (z1 + Z.of_nat n0)))) /\
  In slow_1 (delta_n regles c n z1) /\ 
  ~(In slow_2 (delta_n regles c n z1)) /\ 
  ~(In slow_3 (delta_n regles c n z1)) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  ->
  (forall n0, (n0 < m)%nat -> 
  ~(In slow_1 (delta_n regles c (n+3*n0+2) (z1 + Z.of_nat n0))) /\ 
  ~(In slow_2 (delta_n regles c (n+3*n0+2) (z1 + Z.of_nat n0))) /\ 
  In slow_3 (delta_n regles c (n+3*n0+2) (z1 + Z.of_nat n0)) /\
  (forall z2, z1 + Z.of_nat n0 <> z2 ->  
    ~(In slow_1 (delta_n regles c (n+3*n0+2) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*n0+2) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*n0+2) z2)))).
Proof.
  intros.
  replace (Nat.add (Nat.add n (Nat.mul 3 n0)) 2) with (Nat.add (Nat.add (Nat.add n (Nat.mul 3 n0)) 1) 1) by lia.
  apply propagation_slow_2.
  + repeat apply not_init_propagation.
    exact H.
  + apply (propagation_slow_m_2 z1 c n m H H0 n0 H1).
Qed.

Lemma slow_goes_to_the_right (z1 : Z) (c : config) (n : nat) (m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall z2, z2 < z1 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  -> 
  (forall z2, z2 < z1 -> 
    ~(In slow_1 (delta_n regles c (n+m) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+m) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+m) z2))).
Proof.
  induction m.
  + intros.
    rewrite Nat.add_0_r.
    exact (H0 z2 H1).
  + intros.
    specialize (IHm H H0 z2 H1) as IHm2.
    destruct IHm2 as [H2 [H3 H4]].
    assert (z2 - 1 < z1) by lia.
    specialize (IHm H H0 (z2-1) H5).
    destruct IHm as [H6 [H7 H8]].
    replace (Nat.add n (S m)) with (S (n+m)) by lia.
    cbn [delta_n].
    repeat split.
    all: intro.
    all: apply delta_delta_n_comm in H9.
    - apply in_slow_1 in H9.
      destruct H9 as [H9 | [H9 | [H9 H10]]].
      2,3: contradiction.
      specialize (not_init_propagation c n m H z2) as [H10 [H11 H12]].
      contradiction.
    - apply in_slow_2 in H9.
      destruct H9.
      contradiction.
    - apply in_slow_3 in H9.
      contradiction. 
Qed.

Lemma slow_isnt_that_slow (z1 : Z) (c : config) (n : nat) (m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  In slow_1 (delta_n regles c n z1) /\ 
  ~(In slow_2 (delta_n regles c n z1)) /\ 
  ~(In slow_3 (delta_n regles c n z1)) /\
  (forall z2, z1 <> z2 -> 
    ~(In slow_1 (delta_n regles c n z2)) /\ 
    ~(In slow_2 (delta_n regles c n z2)) /\ 
    ~(In slow_3 (delta_n regles c n z2)))
  -> 
  (forall z2, z2 < z1 + Z.of_nat m ->  
    ~(In slow_1 (delta_n regles c (n+3*m) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*m) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*m) z2)) /\
    ~(In slow_1 (delta_n regles c (n+3*m+1) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*m+1) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*m+1) z2)) /\
    ~(In slow_1 (delta_n regles c (n+3*m+2) z2)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*m+2) z2)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*m+2) z2))).
Proof.
  induction m.
  + intros.
    replace (z1 + Z.of_nat 0) with z1 in H1 by lia.
    replace (Nat.add n (Nat.mul 3 0)) with n by lia.
    destruct H0 as [H0 [H2 [H3 H4]]].
    assert (z1 <> z2) by lia.
    destruct (H4 z2 H5) as [H6 [H7 H8]].
    assert (forall z2, z2 < z1 ->
    ~ In slow_1 (delta_n regles c n z2) /\
    ~ In slow_2 (delta_n regles c n z2) /\ ~ In slow_3 (delta_n regles c n z2)).
    - intros.
      assert (z1 <> z0) by lia.
      exact (H4 z0 H10).
    - destruct (slow_goes_to_the_right z1 c n 1 H H9 z2 H1) as [H10 [H11 H12]].
      destruct (slow_goes_to_the_right z1 c n 2 H H9 z2 H1) as [H13 [H14 H15]].
      repeat split.
      * exact H6.
      * exact H7.
      * exact H8.
      * exact H10.
      * exact H11.
      * exact H12.
      * exact H13.
      * exact H14.
      * exact H15.
  + intros.
    specialize (IHm H H0).
    - assert (forall z2,
      z2 < z1 + Z.of_nat (S m) ->
      ~ In slow_1 (delta_n regles c (n + 3 * S m) z2) /\
      ~ In slow_2 (delta_n regles c (n + 3 * S m) z2) /\
      ~ In slow_3 (delta_n regles c (n + 3 * S m) z2)).
      * intros.
        assert (z0 - 1 < z1 + Z.of_nat m) by lia.
        destruct (IHm (z0 - 1) H3) as [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]].
        replace (Nat.add n (Nat.mul 3 (S m))) with (S (n + 3*m + 2)) by lia.
        cbn [delta_n].
        repeat split.
        all: intro; apply delta_delta_n_comm in H13.
        ++ apply in_slow_1 in H13.
           specialize (not_init_propagation c n (3 * m + 2) H z0) as [H14 [H15 H16]].
           rewrite Nat.add_assoc in H14.
           destruct H13 as [H13 | [H13 | [H13 H17]]].
           all: contradiction.
        ++ apply in_slow_2 in H13.
           destruct H13.
           replace (Nat.add (Nat.add n (Nat.mul 3 m)) 2) with (S (n + 3*m + 1)) in H13 by lia.
           cbn [delta_n] in H13.
           apply delta_delta_n_comm in H13.
           apply in_slow_1 in H13.
           specialize (not_init_propagation c n (3 * m + 1) H z0) as [H15 [H16 H17]].
           rewrite Nat.add_assoc in H15.
           destruct H13 as [H13 | [H13 | [H13 H18]]].
           all: contradiction.
        ++ apply in_slow_3 in H13.
           replace (Nat.add (Nat.add n (Nat.mul 3 m)) 2) with (S (n + 3*m + 1)) in H13 by lia.
           cbn [delta_n] in H13.
           apply delta_delta_n_comm in H13.
           apply in_slow_2 in H13.
           destruct H13.
           replace (Nat.add (Nat.add n (Nat.mul 3 m)) 1) with (S (n + 3*m)) in H13 by lia.
           cbn [delta_n] in H13.
           apply delta_delta_n_comm in H13.
           apply in_slow_1 in H13.
           specialize (not_init_propagation c n (3 * m) H z0) as [H15 [H16 H17]].
           destruct H13 as [H13 | [H13 | [H13 H18]]].
           all: contradiction.
      * assert(forall z2,
        z2 < z1 + Z.of_nat (S m) ->
        ~ In slow_1 (delta_n regles c (n + 3 * S m + 1) z2) /\
        ~ In slow_2 (delta_n regles c (n + 3 * S m + 1) z2) /\
        ~ In slow_3 (delta_n regles c (n + 3 * S m + 1) z2)).
        ++ intros.
           destruct (H2 z0 H3) as [H4 [H5 H6]].
           assert (z0 - 1 < z1 + Z.of_nat (S m)) by lia.
           destruct (H2 (z0-1) H7) as [H8 [H9 H10]].
           replace (Nat.add (Nat.add n (Nat.mul 3 (S m))) 1) with (S (n + 3*(S m))) by lia.
           cbn [delta_n].
           repeat split.
           all: intro; apply delta_delta_n_comm in H11.
           -- apply in_slow_1 in H11.
              specialize (not_init_propagation c n (3 * (S m)) H z0) as [H12 [H13 H14]].
              destruct H11 as [H11 | [H11 | [H11 H15]]].
              all: contradiction.
           -- apply in_slow_2 in H11.
              destruct H11.
              contradiction.
           -- apply in_slow_3 in H11.
              contradiction.
        ++ destruct (H2 z2 H1) as [H4 [H5 H6]].
           destruct (H3 z2 H1) as [H7 [H8 H9]].
           assert (z2 - 1 < z1 + Z.of_nat (S m)) by lia.
           destruct (H3 (z2-1) H10) as [H11 [H12 H13]].
           repeat split.
           7-9: replace (Nat.add (Nat.add n (Nat.mul 3 (S m))) 2) with (S (n + 3*(S m) + 1)) by lia.
           7-9: cbn [delta_n]; intro; apply delta_delta_n_comm in H14.
           -- exact H4.
           -- exact H5.
           -- exact H6.
           -- exact H7.
           -- exact H8.
           -- exact H9.
           -- apply in_slow_1 in H14.
              specialize (not_init_propagation c n (3 * (S m) + 1) H z2) as [H15 [H16 H17]].
              rewrite Nat.add_assoc in H15.
              destruct H14 as [H14 | [H14 | [H14 H18]]].
              all: contradiction.
           -- apply in_slow_2 in H14.
              destruct H14.
              contradiction.
           -- apply in_slow_3 in H14.
              contradiction.
Qed.

(* =========== pas de nouveaux murs qui apparaissent =========== *)

Lemma no_new_wall (z1 z2 : Z) (c : config) (n : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall z, (z1 < z) /\ (z < z2) ->
    ~(In wall (delta_n regles c n z)) /\ 
    ~(In gen (delta_n regles c n z))) /\ 
  (forall z, (z < z2) ->
    ~(In slow_1 (delta_n regles c n z)) /\ 
    ~(In slow_2 (delta_n regles c n z)) /\ 
    ~(In slow_3 (delta_n regles c n z)))
  -> 
  (forall z, (z1 < z) /\ (z < z2) ->
    ~(In wall (delta_n regles c (S n) z)) /\ 
    ~(In gen (delta_n regles c (S n) z))).
Proof.
  intros.
  destruct H0.
  cbn [delta_n].
  split.
  all: intro.
  all: apply delta_delta_n_comm in H3.
  + apply in_wall in H3.
    destruct H3 as [H3 | [H3 | H3]].
    - destruct (H0 z H1).
      contradiction.
    - destruct (H z).
      contradiction.
    - destruct (H0 z H1).
      contradiction.
  + apply in_gen in H3.
    destruct H3.
    assert (z - 1 < z2) by lia.
    destruct (H2 (z-1) H5).
    contradiction.
Qed.

Lemma no_new_wall_m (z1 z2 : Z) (c : config) (n m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall z, (z1 < z) /\ (z < z2) ->
    ~(In wall (delta_n regles c n z)) /\ 
    ~(In gen (delta_n regles c n z))) /\ 
  (forall z, (z < z2) ->
    ~(In slow_1 (delta_n regles c n z)) /\ 
    ~(In slow_2 (delta_n regles c n z)) /\ 
    ~(In slow_3 (delta_n regles c n z)))
  -> 
  (forall z, (z1 < z) /\ (z < z2) ->
    ~(In wall (delta_n regles c (n+m) z)) /\ 
    ~(In gen (delta_n regles c  (n+m) z))).
Proof.
  induction m.
  + rewrite Nat.add_0_r.
    intros.
    destruct H0.
    exact (H0 z H1).
  + intros.
    replace (Nat.add n (S m)) with (S (n+m)) by lia.
    apply (no_new_wall z1 z2 c (n+m)) in H1.
    - exact H1.
    - apply not_init_propagation.
      exact H.
    - specialize (IHm H H0).
      split.
      * exact IHm.
      * destruct H0.
        apply slow_goes_to_the_right.
        ++ exact H.
        ++ exact H2.
Qed.

Lemma propagation_build_l_m (z : Z) (n m : nat) :
  forall c,
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  In build_l (delta_n regles c n (z + Z.of_nat m)) /\
  (forall z_prime, (z < z_prime) /\ (z_prime < z + Z.of_nat m + 1) ->
    ~(In wall (delta_n regles c n z_prime)) /\ 
    ~(In gen (delta_n regles c n z_prime))) /\ 
  (forall z_prime, (z_prime < z + Z.of_nat m + 1) ->
    ~(In slow_1 (delta_n regles c n z_prime)) /\ 
    ~(In slow_2 (delta_n regles c n z_prime)) /\ 
    ~(In slow_3 (delta_n regles c n z_prime)))
  -> 
  In build_l (delta_n regles c (n+m) z).
Proof.
  induction m.
  + intros.
    destruct H0.
    rewrite Nat.add_0_r.
    replace (z + Z.of_nat 0) with z in H0 by lia.
    exact H0.
  + intros.
    replace (Nat.add n (S m)) with (S (n+m)) by lia.
    cbn [delta_n].
    apply (IHm (delta regles c)).
    - intro.
      specialize (not_init_propagation c n 1 H z0) as H1.
      replace (Nat.add n 1) with (S n) in H1 by lia.
      cbn [delta_n] in H1.
      destruct H1 as [H1 [H2 H3]].
      repeat split.
      * exact H1.
      * exact H2.
      * exact H3.
    - destruct H0 as [H0 [H1 H2]].
      replace (z + Z.of_nat (S m)) with (z + Z.of_nat m + 1) in * by lia.
      split.
      * apply delta_delta_n_comm.
        apply in_build_l.
        right; split.
        ++ exact H0.
        ++ assert (z < z + Z.of_nat m + 1 < z + Z.of_nat m + 1 + 1) by lia.
           destruct (H1 (z + Z.of_nat m + 1) H3).
           exact H4.
      * split.
        ++ intros.
           assert (z < z_prime < z + Z.of_nat m + 1 + 1) by lia.
           apply (H1 z_prime) in H4.
           destruct H4.
           assert (z_prime - 1 < z + Z.of_nat m + 1 + 1) by lia.
           apply (H2 (z_prime - 1)) in H6.
           destruct H6 as [H7 [H8 H9]].
           split.
           all: intro.
           all: apply delta_delta_n_comm in H6.
           -- apply in_wall in H6.
              destruct H6 as [H6 | [H6 | H6]].
              ** contradiction.
              ** destruct (H z_prime).
                 contradiction.
              ** contradiction. 
           -- apply in_gen in H6.
              destruct H6.
              contradiction.
        ++ specialize (slow_goes_to_the_right (z + Z.of_nat m + 1 + 1) c n 1 H H2) as H3.
           replace (Nat.add n 1) with (S n) in H3 by lia.
           cbn [delta_n] in H3.
           intros.
           apply (H3 z_prime).
           lia.
Qed.


Lemma propagation_build_r_m (c : config) (z : Z) (n m : nat) :
  In build_r (delta_n regles c n z) /\
  (forall p, (p < m)%nat -> ~(In slow_1 (delta_n regles c (n+p) (z + Z.of_nat p))))
  -> 
  In build_r (delta_n regles c (n+m) (z + Z.of_nat m)).
Proof.
  induction m.
  + intros.
    destruct H.
    rewrite Nat.add_0_r.
    replace (z + Z.of_nat 0) with z by lia.
    exact H.
  + intros.
    replace (Nat.add n (S m)) with (S (n+m)) by lia.
    cbn [delta_n].
    apply delta_delta_n_comm.
    apply in_build_r.
    replace (z + Z.of_nat (S m) - 1) with (z + Z.of_nat m) by lia.
    right; right.
    destruct H.
    split.
    - assert (m < S m)%nat by lia.
      apply (H0 m H1).
    - apply IHm.
      split.
      * exact H.
      * intros.
        assert (p < S m)%nat by lia.
        apply (H0 p H2).
Qed.

Lemma gen_or_build_r_or_build_l (c : config) (n : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) -> 
  (exists z, 
    ((In gen (delta_n regles c n z) /\ ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ In build_l (delta_n regles c n z) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ ~(In build_l (delta_n regles c n z)) /\ In build_r (delta_n regles c n z))) /\
    forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c n z_prime)) /\ ~(In build_l (delta_n regles c n z_prime)) /\ ~(In build_r (delta_n regles c n z_prime)))
  -> 
  (exists z, 
    ((In gen (delta_n regles c (n+1) z) /\ ~(In build_l (delta_n regles c (n+1) z)) /\ ~(In build_r (delta_n regles c (n+1) z))) \/
    (~(In gen (delta_n regles c (n+1) z)) /\ In build_l (delta_n regles c (n+1) z) /\ ~(In build_r (delta_n regles c (n+1) z))) \/
    (~(In gen (delta_n regles c (n+1) z)) /\ ~(In build_l (delta_n regles c (n+1) z)) /\ In build_r (delta_n regles c (n+1) z))) /\
    forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c (n+1) z_prime)) /\ ~(In build_l (delta_n regles c (n+1) z_prime)) /\ ~(In build_r (delta_n regles c (n+1) z_prime))).
Proof.
  intros.
  destruct H0 as [z [[H0 | [H0 | H0]]  H1]].
  + exists (z - 1).
    destruct H0 as [H0 [H2 H3]].
    split.
    - right; left.
      assert (z <> z - 2) by lia.
      specialize (H1 (z - 2) H4).
      destruct H1 as [H1 [H5 H6]].
      replace (Nat.add n 1) with (S n) by lia.
      cbn [delta_n].
      repeat split.
      * intro.
        apply delta_delta_n_comm in H7.
        apply in_gen in H7.
        replace (z - 1 - 1) with (z - 2) in H7 by lia.
        destruct H7; contradiction.
      * apply delta_delta_n_comm.
        apply in_build_l.
        replace (z - 1 + 1) with z by lia.
        left; exact H0.
      * intro.
        apply delta_delta_n_comm in H7.
        apply in_build_r in H7.
        replace (z - 1 - 1) with (z - 2) in H7 by lia.
        destruct H7 as [H7 | [[H7 H8] | [H7 H8]]].
        2,3: contradiction.
        destruct (H (z-1)) as [H8 [H9 H10]].
        contradiction.
    - intros.
      replace (Nat.add n 1) with (S n) by lia.
      cbn [delta_n].
      repeat split.
      all: intro; apply delta_delta_n_comm in H5.
      * apply in_gen in H5.
        destruct H5.
        destruct (z =? z_prime - 1) eqn:Heq.
        ++ rewrite Z.eqb_eq in Heq.
           rewrite <- Heq in H6.
           contradiction.
        ++ rewrite Z.eqb_neq in Heq.
           destruct (H1 (z_prime - 1) Heq) as [H7 [H8 H9]].
           contradiction.
      * apply in_build_l in H5.
        assert (z <> z_prime + 1) by lia.
        destruct (H1 (z_prime + 1) H6) as [H7 [H8 H9]].
        destruct H5 as [H5 | [H5 H10]].
        all: contradiction.
      * apply in_build_r in H5.
        destruct H5.
        ++ destruct (H z_prime) as [H6 [H7 H8]].
           contradiction.
        ++ destruct (z =? z_prime - 1) eqn:Heq.
          -- rewrite Z.eqb_eq in Heq.
             rewrite <- Heq in H5.
             destruct H5 as [[H5 H6] | [H5 H6]].
             all: contradiction.
          -- rewrite Z.eqb_neq in Heq.
             destruct (H1 (z_prime - 1) Heq) as [H7 [H8 H9]].
             destruct H5 as [[H5 H6] | [H5 H6]].
             all: contradiction.
  + replace (Nat.add n 1) with (S n) by lia.
    cbn [delta_n].
    destruct (existsb (fun x => x =? wall) (delta_n regles c n z)) eqn: Hex.
    - apply in_and_exists in  Hex.
      exists (z + 1).
      destruct H0 as [H0 [H2 H3]].
      split.
      * right; right.
        repeat split.
        ++ intro.
           apply delta_delta_n_comm in H4.
           apply in_gen in H4.
           destruct H4.
           replace (z + 1 - 1) with z in H5 by lia.
           contradiction.
        ++ intro.
           apply delta_delta_n_comm in H4.
           apply in_build_l in H4.
           assert (z <> z + 1 + 1) by lia.
           destruct (H1 (z + 1 + 1) H5) as [H6 [H7 H8]].
           destruct H4 as [H4 | [H4 H9]].
           all: contradiction.
        ++ apply delta_delta_n_comm.
           apply in_build_r.
           right; left.
           replace (z + 1 - 1) with z by lia.
           exact (conj H2 Hex).
      * intros.
        repeat split.
        all: intro; apply delta_delta_n_comm in H5.
        ++ apply in_gen in H5.
           destruct H5.
           assert (z <> z_prime - 1) by lia.
           destruct (H1 (z_prime - 1) H7) as [H8 [H9 H10]].
           contradiction.
        ++ apply in_build_l in H5.
           destruct (z =? z_prime + 1) eqn:Heq.
           -- rewrite Z.eqb_eq in Heq.
              rewrite <- Heq in H5.
              destruct H5 as [H5 | [H5 H6]].
              all: contradiction.
           -- rewrite Z.eqb_neq in Heq.
              destruct (H1 (z_prime + 1) Heq) as [H7 [H8 H9]].
              destruct H5 as [H5 | [H5 H6]].
              all: contradiction.
        ++ apply in_build_r in H5.
           destruct H5.
           -- destruct (H z_prime) as [H6 [H7 H8]].
              contradiction.
           -- assert (z <> z_prime - 1) by lia.
              destruct (H1 (z_prime - 1) H6) as [H7 [H8 H9]].
              destruct H5 as [[H5 H10] | [H5 H10]].
              all: contradiction.
    - apply negb_true_iff in Hex.
      apply not_in_and_exists in Hex.
      exists (z - 1).
      destruct H0 as [H0 [H2 H3]].
      split.
      * right; left.
        assert (z <> z - 2) by lia.
        specialize (H1 (z - 2) H4).
        destruct H1 as [H1 [H5 H6]].
        replace (Nat.add n 1) with (S n) by lia.
        cbn [delta_n].
        repeat split.
        ++ intro.
           apply delta_delta_n_comm in H7.
           apply in_gen in H7. 
           replace (z - 1 - 1) with (z - 2) in H7 by lia.
           destruct H7; contradiction.
        ++ apply delta_delta_n_comm.
          apply in_build_l.
          replace (z - 1 + 1) with z by lia.
          right; exact (conj H2 Hex).
        ++ intro.
          apply delta_delta_n_comm in H7.
          apply in_build_r in H7.
          replace (z - 1 - 1) with (z - 2) in H7 by lia.
          destruct H7 as [H7 | [[H7 H8] | [H7 H8]]].
          2,3: contradiction.
          destruct (H (z-1)) as [H8 [H9 H10]].
          contradiction.
      * intros.
        replace (Nat.add n 1) with (S n) by lia.
        cbn [delta_n].
        repeat split.
        all: intro; apply delta_delta_n_comm in H5.
      ++ apply in_gen in H5.
         destruct H5.
         destruct (z =? z_prime - 1) eqn:Heq.
         -- rewrite Z.eqb_eq in Heq.
            rewrite <- Heq in H6.
            contradiction.
         -- rewrite Z.eqb_neq in Heq.
            destruct (H1 (z_prime - 1) Heq) as [H7 [H8 H9]].
            contradiction.
      ++ apply in_build_l in H5.
         assert (z <> z_prime + 1) by lia.
         destruct (H1 (z_prime + 1) H6) as [H7 [H8 H9]].
         destruct H5 as [H5 | [H5 H10]].
         all: contradiction.
      ++ apply in_build_r in H5.
         destruct H5.
         -- destruct (H z_prime) as [H6 [H7 H8]].
            contradiction.
         -- destruct (z =? z_prime - 1) eqn:Heq.
            ** rewrite Z.eqb_eq in Heq.
               rewrite <- Heq in H5.
               destruct H5 as [[H5 H6] | [H5 H6]].
               all: contradiction.
            ** rewrite Z.eqb_neq in Heq.
               destruct (H1 (z_prime - 1) Heq) as [H7 [H8 H9]].
               destruct H5 as [[H5 H6] | [H5 H6]].
               all: contradiction.
  + replace (Nat.add n 1) with (S n) by lia.
    cbn [delta_n].
    destruct (existsb (fun x => x =? slow_1) (delta_n regles c n z)) eqn: Hex.
    - apply in_and_exists in  Hex.
      exists (z + 1).
      destruct H0 as [H0 [H2 H3]].
      split.
      * left.
        repeat split.
        ++ apply delta_delta_n_comm.
           apply in_gen.
           replace (z + 1 - 1) with z by lia.
           exact (conj Hex H3).
        ++ intro.
           apply delta_delta_n_comm in H4.
           apply in_build_l in H4.
           assert (z <> z + 1 + 1) by lia.
           destruct (H1 (z + 1 + 1) H5) as [H6 [H7 H8]].
           destruct H4 as [H4 | [H4 H9]].
           all: contradiction.
        ++ intro.
           apply delta_delta_n_comm in H4.
           apply in_build_r in H4.
           destruct H4.
           -- destruct (H (z + 1)) as [H5 [H6 H7]].
              contradiction.
           -- replace (z + 1 - 1) with z in H4 by lia.
              destruct H4 as [[H4 H5] | [H4 H5]].
              all: contradiction.
      * intros.
        repeat split.
        all: intro; apply delta_delta_n_comm in H5.
        ++ apply in_gen in H5.
           destruct H5.
           assert (z <> z_prime - 1) by lia.
           destruct (H1 (z_prime - 1) H7) as [H8 [H9 H10]].
           contradiction.
        ++ apply in_build_l in H5.
           destruct (z =? z_prime + 1) eqn:Heq.
           -- rewrite Z.eqb_eq in Heq.
              rewrite <- Heq in H5.
              destruct H5 as [H5 | [H5 H6]].
              all: contradiction.
           -- rewrite Z.eqb_neq in Heq.
              destruct (H1 (z_prime + 1) Heq) as [H7 [H8 H9]].
              destruct H5 as [H5 | [H5 H6]].
              all: contradiction.
        ++ apply in_build_r in H5.
           destruct H5.
           -- destruct (H z_prime) as [H6 [H7 H8]].
              contradiction.
           -- assert (z <> z_prime - 1) by lia.
              destruct (H1 (z_prime - 1) H6) as [H7 [H8 H9]].
              destruct H5 as [[H5 H10] | [H5 H10]].
              all: contradiction.
    - apply negb_true_iff in Hex.
      apply not_in_and_exists in Hex.
      exists (z + 1).
      destruct H0 as [H0 [H2 H3]].
      split.
      * right; right.
        repeat split.
        ++ intro.
           apply delta_delta_n_comm in H4.
           apply in_gen in H4.
           replace (z + 1 - 1) with z in H4 by lia.
           destruct H4.
           contradiction.
        ++ intro.
           apply delta_delta_n_comm in H4.
           apply in_build_l in H4.
           assert (z <> z + 1 + 1) by lia.
           destruct (H1 (z + 1 + 1) H5) as [H76 [H7 H8]].
           destruct H4 as [H4 | [H4 H9]].
           all: contradiction.
        ++ apply delta_delta_n_comm.
           apply in_build_r.
           replace (z + 1 - 1) with z by lia.
           right; right; exact (conj Hex H3).
      * intros.
        replace (Nat.add n 1) with (S n) by lia.
        cbn [delta_n].
        repeat split.
        all: intro; apply delta_delta_n_comm in H5.
      ++ apply in_gen in H5.
         assert (z <> z_prime - 1) by lia.
         destruct (H1 (z_prime - 1) H6) as [H7 [H8 H9]].
         destruct H5.
         contradiction.
      ++ apply in_build_l in H5.
         destruct (z =? z_prime + 1) eqn:Heq.
         -- apply Z.eqb_eq in Heq.
            rewrite <- Heq in H5.
            destruct H5 as [H5 | [H5 H6]].
            all: contradiction.
         -- apply Z.eqb_neq in Heq.
            destruct (H1 (z_prime + 1) Heq) as [H6 [H7 H8]].
            destruct H5 as [H5 | [H5 H9]].
            all: contradiction.
      ++ apply in_build_r in H5.
         destruct H5.
         -- destruct (H z_prime) as [H6 [H7 H8]].
            contradiction.
         -- assert (z <> z_prime - 1) by lia.
            destruct (H1 (z_prime - 1) H6) as [H7 [H8 H9]].
            destruct H5 as [[H5 H10] | [H5 H10]].
            all: contradiction.
Qed.

Lemma gen_or_build_r_or_build_l_m (c : config) (n m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) -> 
  (exists z, 
    ((In gen (delta_n regles c n z) /\ ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ In build_l (delta_n regles c n z) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ ~(In build_l (delta_n regles c n z)) /\ In build_r (delta_n regles c n z))) /\
    forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c n z_prime)) /\ ~(In build_l (delta_n regles c n z_prime)) /\ ~(In build_r (delta_n regles c n z_prime)))
  -> 
  (exists z, 
    ((In gen (delta_n regles c (n+m) z) /\ ~(In build_l (delta_n regles c (n+m) z)) /\ ~(In build_r (delta_n regles c (n+m) z))) \/
    (~(In gen (delta_n regles c (n+m) z)) /\ In build_l (delta_n regles c (n+m) z) /\ ~(In build_r (delta_n regles c (n+m) z))) \/
    (~(In gen (delta_n regles c (n+m) z)) /\ ~(In build_l (delta_n regles c (n+m) z)) /\ In build_r (delta_n regles c (n+m) z))) /\
    forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c (n+m) z_prime)) /\ ~(In build_l (delta_n regles c (n+m) z_prime)) /\ ~(In build_r (delta_n regles c (n+m) z_prime))).
Proof.
  induction m.
  + intros H0 H.
    rewrite Nat.add_0_r.
    exact H.
  + intros H0 H.
    replace (Nat.add n (S m)) with (Nat.add (Nat.add n m) 1) by lia.
    apply gen_or_build_r_or_build_l.
    - apply not_init_propagation.
      exact H0.
    - apply (IHm H0 H).
Qed.

Lemma gen_or_build_r_or_build_l_m_cor_1 (c : config) (z : Z) (n m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) -> 
  (exists z, 
    ((In gen (delta_n regles c n z) /\ ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ In build_l (delta_n regles c n z) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ ~(In build_l (delta_n regles c n z)) /\ In build_r (delta_n regles c n z))) /\
    forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c n z_prime)) /\ ~(In build_l (delta_n regles c n z_prime)) /\ ~(In build_r (delta_n regles c n z_prime)))
  -> 
  In gen (delta_n regles c (n+m) z) ->
  ~(In build_l (delta_n regles c (n+m) z)) /\ ~(In build_r (delta_n regles c (n+m) z)) /\
  forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c (n+m) z_prime)) /\ ~(In build_l (delta_n regles c (n+m) z_prime)) /\ ~(In build_r (delta_n regles c (n+m) z_prime)).
Proof.
  intros.
  apply (gen_or_build_r_or_build_l_m c n m H) in H0.
  destruct H0 as [z2 [H0 H2]].
  destruct (z2 =? z) eqn:Heq.
  + apply Z.eqb_eq in Heq.
    rewrite <- Heq in *.
    destruct H0 as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    2,3: contradiction.
    exact (conj H4 (conj H5 H2)).
  + apply Z.eqb_neq in Heq.
    destruct (H2 z Heq) as [H5 [H6 H7]].
    contradiction.
Qed.

Lemma gen_or_build_r_or_build_l_m_cor_2 (c : config) (z : Z) (n m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) -> 
  (exists z, 
    ((In gen (delta_n regles c n z) /\ ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ In build_l (delta_n regles c n z) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ ~(In build_l (delta_n regles c n z)) /\ In build_r (delta_n regles c n z))) /\
    forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c n z_prime)) /\ ~(In build_l (delta_n regles c n z_prime)) /\ ~(In build_r (delta_n regles c n z_prime)))
  -> 
  In build_l (delta_n regles c (n+m) z) ->
  ~(In gen (delta_n regles c (n+m) z)) /\ ~(In build_r (delta_n regles c (n+m) z)) /\
  forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c (n+m) z_prime)) /\ ~(In build_l (delta_n regles c (n+m) z_prime)) /\ ~(In build_r (delta_n regles c (n+m) z_prime)).
Proof.
  intros.
  apply (gen_or_build_r_or_build_l_m c n m H) in H0.
  destruct H0 as [z2 [H0 H2]].
  destruct (z2 =? z) eqn:Heq.
  + apply Z.eqb_eq in Heq.
    rewrite <- Heq in *.
    destruct H0 as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    1,3: contradiction.
    exact (conj H3 (conj H5 H2)).
  + apply Z.eqb_neq in Heq.
    destruct (H2 z Heq) as [H5 [H6 H7]].
    contradiction.
Qed.

Lemma gen_or_build_r_or_build_l_m_cor_3 (c : config) (z : Z) (n m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) -> 
  (exists z, 
    ((In gen (delta_n regles c n z) /\ ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ In build_l (delta_n regles c n z) /\ ~(In build_r (delta_n regles c n z))) \/
    (~(In gen (delta_n regles c n z)) /\ ~(In build_l (delta_n regles c n z)) /\ In build_r (delta_n regles c n z))) /\
    forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c n z_prime)) /\ ~(In build_l (delta_n regles c n z_prime)) /\ ~(In build_r (delta_n regles c n z_prime)))
  -> 
  In build_r (delta_n regles c (n+m) z) ->
  ~(In gen (delta_n regles c (n+m) z)) /\ ~(In build_l (delta_n regles c (n+m) z)) /\
  forall z_prime, z <> z_prime -> ~(In gen (delta_n regles c (n+m) z_prime)) /\ ~(In build_l (delta_n regles c (n+m) z_prime)) /\ ~(In build_r (delta_n regles c (n+m) z_prime)).
Proof.
  intros.
  apply (gen_or_build_r_or_build_l_m c n m H) in H0.
  destruct H0 as [z2 [H0 H2]].
  destruct (z2 =? z) eqn:Heq.
  + apply Z.eqb_eq in Heq.
    rewrite <- Heq in *.
    destruct H0 as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    1,2: contradiction.
    exact (conj H3 (conj H4 H2)).
  + apply Z.eqb_neq in Heq.
    destruct (H2 z Heq) as [H5 [H6 H7]].
    contradiction.
Qed.


Lemma build_r_cannot_tp (c : config) (z : Z) (n : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) ->
  (forall z, ~(In build_l (delta_n regles c n z)) /\  ~(In gen (delta_n regles c n z))) /\
  (forall z_prime, z < z_prime -> ~(In build_r (delta_n regles c n z_prime)))
  ->
  (forall m z_prime, z + Z.of_nat m < z_prime -> 
  ~(In build_r (delta_n regles c (n+m) z_prime)) /\
  ~(In build_l (delta_n regles c (n+m) z_prime)) /\
  ~(In gen (delta_n regles c (n+m) z_prime))).
Proof.
  induction m.
  + replace (z + Z.of_nat 0) with z by lia.
    rewrite Nat.add_0_r.
    intros.
    destruct H0.
    exact (conj (H2 z_prime H1) (H0 z_prime)).
  + intros.
    replace (Nat.add n (S m)) with (S (n+m)) by lia.
    cbn [delta_n].
    assert (z + Z.of_nat m < z_prime - 1) by lia.
    destruct (IHm (z_prime - 1) H2) as [IHm1 [IHm2 IHm3]].
    repeat split.
    all: intro.
    all: apply delta_delta_n_comm in H3.
    - apply in_build_r in H3.
      destruct H3 as [H3 | [[H3 H4] | [H3 H4]]].
      * destruct (not_init_propagation c n m H z_prime) as [H4 [H5 H6]].
        contradiction.
      * contradiction.
      * contradiction.
    - apply in_build_l in H3.
      assert (z + Z.of_nat m < z_prime + 1) by lia.
      destruct (IHm (z_prime + 1) H4) as [IHm4 [IHm5 IHm6]].
      destruct H3 as [H3 | [H3 H5]].
      all: contradiction.
    - apply in_gen in H3.
      destruct H3.
      contradiction.
Qed.


Lemma from_a_gen_to_another_aux_1 (c : config) (z : Z) (n m : nat) :
  (m > 1)%nat ->
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) /\
  (forall z, ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) /\
  In slow_1 (delta_n regles c n (z + Z.of_nat m)) /\
  ~(In slow_2 (delta_n regles c n (z + Z.of_nat m))) /\
  ~(In slow_3 (delta_n regles c n (z + Z.of_nat m))) /\
  In gen (delta_n regles c n (z + Z.of_nat m)) /\
  (forall z_prime, (z + Z.of_nat m <> z_prime) ->
    ~(In gen (delta_n regles c n z_prime)) /\
    ~(In slow_1 (delta_n regles c n z_prime)) /\ 
    ~(In slow_2 (delta_n regles c n z_prime)) /\ 
    ~(In slow_3 (delta_n regles c n z_prime))) /\
  In wall (delta_n regles c n z) /\
  (forall z_prime, (z < z_prime) ->
    ~(In wall (delta_n regles c n z_prime)))
  -> 
  In slow_1 (delta_n regles c (n+3*m) (z + 2*Z.of_nat m)) /\
  ~(In slow_2 (delta_n regles c (n+3*m) (z + 2*Z.of_nat m))) /\
  ~(In slow_3 (delta_n regles c (n+3*m) (z + 2*Z.of_nat m))) /\
  (forall z_prime, (z + 2*Z.of_nat m <> z_prime) ->
    ~(In slow_1 (delta_n regles c (n+3*m) z_prime)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*m) z_prime)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*m) z_prime))).
Proof.
  intros.
  destruct H0 as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
  assert (forall n0, (n0 < m)%nat -> ~(In build_r (delta_n regles c (n+3*n0) (z + Z.of_nat m + Z.of_nat n0)))).
  + intros.
    destruct (Nat.leb (Nat.mul 3 n0) m) eqn:Hcase.
    --- destruct n0.
        - replace (Nat.add n (Nat.mul 3 0)) with n by lia.
          replace (z + Z.of_nat m + Z.of_nat 0) with (z + Z.of_nat m) by lia.
          destruct (H2 (z + Z.of_nat m)).
          exact H11.
        - assert (
          ~ In gen (delta_n regles c (n + 3 * S n0) (z + Z.of_nat m + Z.of_nat (S n0))) /\
          ~ In build_l (delta_n regles c (n + 3 * S n0) (z + Z.of_nat m + Z.of_nat (S n0))) /\
          ~ In build_r (delta_n regles c (n + 3 * S n0) (z + Z.of_nat m + Z.of_nat (S n0)))
          ).
          * apply (gen_or_build_r_or_build_l_m_cor_2 c (z + Z.of_nat m - 3*Z.of_nat (S n0)) n (3*(S n0))).
            ++ exact H1.
            ++ exists (z + Z.of_nat m).
               split.
               -- left.
                  exact (conj H6 (H2 (z + Z.of_nat m))).
               -- intros.
                  destruct (H7 z_prime H10) as [H11 [H12 [H13 H14]]].
                  exact (conj H11 (H2 z_prime)).
            ++ assert (In build_l (delta_n regles c (S n) (z + Z.of_nat m - 1))).
               -- cbn [delta_n].
                  apply delta_delta_n_comm.
                  apply in_build_l.
                  replace (z + Z.of_nat m - 1 + 1) with (z + Z.of_nat m) by lia.
                  left; exact H6.
               -- replace (Nat.add n (Nat.mul 3 (S n0))) with (Nat.add (S n) (Nat.sub (Nat.mul 3 (S n0)) 1)) by lia.
                  apply (propagation_build_l_m (z + Z.of_nat m - 3 * Z.of_nat (S n0)) (S n) (3 * S n0 - 1) c).
                  ** replace (S n) with (Nat.add n 1) by lia.
                     apply not_init_propagation.
                     exact H1.
                  ** replace  (z + Z.of_nat m - 3 * Z.of_nat (S n0) + Z.of_nat (3 * S n0 - 1) + 1) with (z + Z.of_nat m) by lia.
                     replace  (z + Z.of_nat m - 3 * Z.of_nat (S n0) + Z.of_nat (3 * S n0 - 1)) with (z + Z.of_nat m - 1) by lia.
                     repeat split.
                     1: exact H10.
                     all: cbn [delta_n]; intro; apply delta_delta_n_comm in H12.
                     +++ apply in_wall in H12.
                         destruct H11.
                         assert (z + Z.of_nat m <> z_prime) by lia.
                         destruct (H7 z_prime H14).
                         apply Nat.leb_le in Hcase.
                         assert (z < z_prime) by lia.
                         specialize (H9 z_prime H17).
                         destruct (H1 z_prime).
                         destruct H12 as [H12 | [H12 | H12]].
                         all : contradiction.
                     +++ apply in_gen in H12.
                         destruct (H2 (z_prime - 1)).
                         destruct H12.
                         contradiction.
                     +++ apply in_slow_1 in H12.
                         destruct (H1 z_prime).
                         assert (z + Z.of_nat m <> z_prime - 1) by lia.
                         destruct (H7 (z_prime - 1) H15) as [H16 [H17 [H18 H19]]].
                         destruct H12 as [H12 | [H12 | [H12 H20]]].
                         all: contradiction.
                     +++ apply in_slow_2 in H12.
                         destruct H12.
                         assert (z + Z.of_nat m <> z_prime) by lia.
                         destruct (H7 z_prime H14) as [H16 [H17 [H18 H19]]].
                         contradiction.
                     +++ apply in_slow_3 in H12.
                         assert (z + Z.of_nat m <> z_prime) by lia.
                         destruct (H7 z_prime H13) as [H16 [H17 [H18 H19]]].
                         contradiction.
              ++ lia.
            * destruct H10 as [H10 [H11 H12]].
              exact H12.
      --- assert (
          ~ In gen (delta_n regles c (n + 3 * n0) (z + Z.of_nat m + Z.of_nat n0)) /\
          ~ In build_l (delta_n regles c (n + 3 * n0) (z + Z.of_nat m + Z.of_nat n0)) /\
          ~ In build_r (delta_n regles c (n + 3 * n0) (z + Z.of_nat m + Z.of_nat n0))
          ).
          - apply (gen_or_build_r_or_build_l_m_cor_3 c (z + 3*Z.of_nat n0 - Z.of_nat m) n (3* n0)).
            * exact H1.
            * exists (z + Z.of_nat m).
              split.
              -- left.
                 exact (conj H6 (H2 (z + Z.of_nat m))).
              -- intros.
                 destruct (H7 z_prime H10) as [H11 [H12 [H13 H14]]].
                 exact (conj H11 (H2 z_prime)).
            * apply Nat.leb_gt in Hcase.
              replace (Nat.add n (Nat.mul 3 n0)) with (Nat.add (S (n+m)) (Nat.sub (Nat.sub (Nat.mul 3 n0) m) 1)) by lia.
              replace (z + 3 * Z.of_nat n0 - Z.of_nat m) with (z + 1 + Z.of_nat (3 * n0 - m - 1)) by lia.
              apply propagation_build_r_m.
              split.
              ++ cbn [delta_n].
                 apply delta_delta_n_comm.
                 apply in_build_r.
                 right; left.
                 replace (z + 1 - 1) with z by lia.
                 split.
                 -- replace (Nat.add n m) with (Nat.add (S n) (Nat.sub m 1)) by lia.
                    apply propagation_build_l_m.
                    ** replace (S n) with (Nat.add n 1) by lia.
                       apply not_init_propagation.
                       exact H1.
                    ** cbn [delta_n].
                       repeat split.
                       2-6: intro; apply delta_delta_n_comm in H11.
                       +++ apply delta_delta_n_comm .
                           apply in_build_l.
                           replace (z + Z.of_nat (m - 1) + 1) with (z + Z.of_nat m) by lia.
                           left; exact H6.
                       +++ apply in_wall in H11.
                           destruct H10.
                           specialize (H9 z_prime H10).
                           destruct (H1 z_prime).
                           assert (z + Z.of_nat m <> z_prime) by lia.
                           destruct (H7 z_prime H15).
                           destruct H11 as [H11 | [H11 | H11]].
                           all: contradiction.
                       +++ apply in_gen in H11.
                           destruct (H2 (z_prime - 1)).
                           destruct H11.
                           contradiction.
                       +++ apply in_slow_1 in H11.
                           destruct (H1 z_prime).
                           assert (z + Z.of_nat m <> z_prime - 1) by lia.
                           destruct (H7 (z_prime - 1) H14) as [H16 [H17 [H18 H19]]].
                           destruct H11 as [H11 | [H11 | [H11 H20]]].
                           all: contradiction.
                       +++ apply in_slow_2 in H11.
                           destruct H11.
                           assert (z + Z.of_nat m <> z_prime) by lia.
                           destruct (H7 z_prime H13) as [H16 [H17 [H18 H19]]].
                           contradiction.
                       +++ apply in_slow_3 in H11.
                           assert (z + Z.of_nat m <> z_prime) by lia.
                           destruct (H7 z_prime H12) as [H16 [H17 [H18 H19]]].
                           contradiction.
                 -- replace (Nat.add n m) with (S (n + (m - 1))) by lia.
                    apply in_wall_m.
                    left; exact H8.
              ++ intros. 
                 assert( forall z_prime,
                 z + Z.of_nat m <> z_prime ->
                 ~ In slow_1 (delta_n regles c n z_prime) /\
                 ~ In slow_2 (delta_n regles c n z_prime) /\
                 ~ In slow_3 (delta_n regles c n z_prime)).
                 -- intros.
                    destruct (H7 z_prime H11).
                    exact H13. 
                 -- pose (q := Nat.div (Nat.add (Nat.add m p) 1) 3).
                    pose (r := Nat.modulo (Nat.add (Nat.add m p) 1) 3).
                    assert (Nat.add (Nat.add m p) 1 = 3 * q + r)%nat by (subst q r; apply Nat.div_mod; lia).
                    assert (r < 3)%nat by (subst r; apply Nat.mod_upper_bound; lia).  
                    pose proof (slow_isnt_that_slow (z + Z.of_nat m) c n q H1 (conj H3 (conj H4 (conj H5 H11)))).
                    assert (z + 1 + Z.of_nat p < z + Z.of_nat m + Z.of_nat q) by lia.
                    destruct (H14 (z + 1 + Z.of_nat p) H15) as [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 H24]]]]]]]].
                    replace (Nat.add (S (n + m)) p) with (Nat.add n (Nat.add (Nat.add m p) 1)) by lia.
                    destruct r.
                    +++ replace (Nat.add (Nat.add m p) 1) with (Nat.mul 3 q) by lia.
                        exact H16.
                    +++ destruct r.
                        *** replace (Nat.add n (Nat.add (Nat.add m p) 1)) with (Nat.add (Nat.add n (Nat.mul 3 q)) 1) by lia.
                            exact H19.
                        *** replace (Nat.add n (Nat.add (Nat.add m p) 1)) with (Nat.add (Nat.add n (Nat.mul 3 q)) 2) by lia.
                            exact H22.
            * lia.
          - destruct H10 as [H10 [H11 H12]].
            exact H12.
  + assert(forall z_prime,
    z + Z.of_nat m <> z_prime ->
    ~ In slow_1 (delta_n regles c n z_prime) /\
    ~ In slow_2 (delta_n regles c n z_prime) /\
    ~ In slow_3 (delta_n regles c n z_prime)).
    - intros.
      destruct (H7 z_prime H10).
      exact H12. 
    - destruct m.
      * replace (z + Z.of_nat 0) with z in * by lia.
        replace (z + 2*Z.of_nat 0) with z by lia.
        replace (Nat.add n (Nat.mul 3 0)) with n by lia.
        exact (conj H3 (conj H4 (conj H5 H10))).
      * pose proof (propagation_slow_m_1 (z + Z.of_nat (S m)) c n (S m) H1 (conj H0 (conj H3 (conj H4 (conj H5 H10))))).
        assert (m < S m)%nat by lia.
        apply H11 in H12.
        replace (Nat.add (Nat.add n (Nat.mul 3 m)) 3) with (Nat.add n (Nat.mul 3 (S m))) in H12 by lia.
        replace (z + Z.of_nat (S m) + Z.of_nat m + 1) with (z + 2 * Z.of_nat (S m)) in H12 by lia.
        exact H12.
Qed.


Lemma from_a_gen_to_another_aux_2 (c : config) (z : Z) (n m : nat) :
  (m > 1)%nat ->
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) /\
  (forall z, ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) /\
  In slow_1 (delta_n regles c n (z + Z.of_nat m)) /\
  ~(In slow_2 (delta_n regles c n (z + Z.of_nat m))) /\
  ~(In slow_3 (delta_n regles c n (z + Z.of_nat m))) /\
  In gen (delta_n regles c n (z + Z.of_nat m)) /\
  (forall z_prime, (z + Z.of_nat m <> z_prime) ->
    ~(In gen (delta_n regles c n z_prime)) /\
    ~(In slow_1 (delta_n regles c n z_prime)) /\ 
    ~(In slow_2 (delta_n regles c n z_prime)) /\ 
    ~(In slow_3 (delta_n regles c n z_prime))) /\
  In wall (delta_n regles c n z) /\
  (forall z_prime, (z < z_prime) ->
    ~(In wall (delta_n regles c n z_prime)))
  -> 
  In build_r (delta_n regles c (n+3*m) (z + 2*Z.of_nat m)) /\
  (forall p, (1<= p <= 3*m)%nat -> 
    forall z_prime, ~(In gen (delta_n regles c (n+p) z_prime))).
Proof.
  intros.
  destruct H0 as [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]].
  assert (forall p, (1 <= p <= m)%nat ->
          In build_l (delta_n regles c (n + p) (z + Z.of_nat m - Z.of_nat p))).
  + intros.
    replace (Nat.add n p) with (Nat.add (Nat.add n 1) (Nat.sub p 1)) by lia.
    apply (propagation_build_l_m (z + Z.of_nat m - Z.of_nat p) (n+1) (p-1) c).
    - apply not_init_propagation.
      exact H1.
    - assert (In build_l (delta_n regles c (n + 1) (z + Z.of_nat m - Z.of_nat p + Z.of_nat (p - 1)))).
      * replace (Nat.add n 1) with (S n) by lia.
        cbn [delta_n].
        apply delta_delta_n_comm.
        apply in_build_l.
        replace (z + Z.of_nat m - Z.of_nat p + Z.of_nat (p - 1) + 1) with (z + Z.of_nat m) by lia.
        left; exact H6.
      * split.
        ++ exact H10.
        ++ split.
           -- intros.
              replace (Nat.add n 1) with (S n) by lia.
              cbn [delta_n].
              split.
              all: intro; apply delta_delta_n_comm in H12.
              ** apply in_wall in H12.
                 assert (z + Z.of_nat m <> z_prime) by lia.
                 destruct (H7 z_prime H13) as [H14 [H15 [H16 H17]]].
                 assert (z < z_prime) by lia.
                 specialize (H9 z_prime H18).
                 destruct (H1 z_prime) as [H19 [H20 H21]].
                 destruct H12 as [H12 | [H12 | H12]].
                 all: contradiction.
              ** apply in_gen in H12.
                 destruct H12.
                 destruct (H2 (z_prime-1)).
                 contradiction.
           -- replace (z + Z.of_nat m - Z.of_nat p + Z.of_nat (p - 1) + 1) with (z + Z.of_nat m) by lia.
              apply slow_goes_to_the_right.
              ** exact H1.
              ** intros.
                 assert (z + Z.of_nat m <> z2) by lia.
                 destruct (H7 z2 H12).
                 exact H14.
  + assert (forall p,
    (m+1 <= p < 3*m)%nat ->
    In build_r (delta_n regles c (n + p) (z + Z.of_nat p - Z.of_nat m))).
    - intros.
      replace (Nat.add n p) with (Nat.add (Nat.add (Nat.add n m) 1) (Nat.sub (Nat.sub p m) 1)) by lia.
      replace (z + Z.of_nat p - Z.of_nat m) with (z + 1 + Z.of_nat (p - m - 1)) by lia.
      apply propagation_build_r_m.
      split.
      * replace (Nat.add (Nat.add n m) 1) with (S (n+m)) by lia.
        cbn [delta_n].
        apply delta_delta_n_comm.
        apply in_build_r.
        replace (z + 1 - 1) with z by lia.
        right; left; split.
        ++ assert (1 <= m <= m)%nat by lia.
           apply (H0 m) in H11.
           replace (z + Z.of_nat m - Z.of_nat m) with z in H11 by lia.
           exact H11.
        ++ replace (Nat.add n m) with (S (n + (m - 1))) by lia.
           apply in_wall_m.
           left; exact H8.
      * intros. 
        assert( forall z_prime,
        z + Z.of_nat m <> z_prime ->
        ~ In slow_1 (delta_n regles c n z_prime) /\
        ~ In slow_2 (delta_n regles c n z_prime) /\
        ~ In slow_3 (delta_n regles c n z_prime)).
        -- intros.
           destruct (H7 z_prime H12).
           exact H14. 
        -- pose (q := Nat.div (Nat.add (Nat.add m 1) p0) 3).
           pose (r := Nat.modulo (Nat.add (Nat.add m 1) p0) 3).
           assert (Nat.add (Nat.add m 1) p0 = 3 * q + r)%nat by (subst q r; apply Nat.div_mod; lia).
           assert (r < 3)%nat by (subst r; apply Nat.mod_upper_bound; lia).  
           pose proof (slow_isnt_that_slow (z + Z.of_nat m) c n q H1 (conj H3 (conj H4 (conj H5 H12)))).
           assert (z + 1 + Z.of_nat p0 < z + Z.of_nat m + Z.of_nat q) by lia.
           destruct (H15 (z + 1 + Z.of_nat p0) H16) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]].
           replace (Nat.add (Nat.add (Nat.add n m) 1) p0) with (Nat.add n (Nat.add (Nat.add m 1) p0)) by lia.
           destruct r.
           ** replace (Nat.add (Nat.add m 1) p0) with (Nat.mul 3 q) by lia.
              exact H17.
           ** destruct r.
              +++ replace (Nat.add n (Nat.add (Nat.add m 1) p0)) with (Nat.add (Nat.add n (Nat.mul 3 q)) 1) by lia.
                  exact H20.
              +++ replace (Nat.add n (Nat.add (Nat.add m 1) p0)) with (Nat.add (Nat.add n (Nat.mul 3 q)) 2) by lia.
                  exact H23.
    - assert (In build_r (delta_n regles c (n + 3 * m) (z + 2 * Z.of_nat m))).
      * replace (Nat.add n (Nat.mul 3 m)) with (S (n + 3*(m - 1) + 2)) by lia.
        cbn [delta_n].
        apply delta_delta_n_comm.
        apply in_build_r.
        right; right.
        split.
        ++ assert (forall n0, (n0 < m)%nat -> ~(In build_r (delta_n regles c (n+3*n0) (z + Z.of_nat m + Z.of_nat n0)))).
           ** intros.
              destruct (Nat.leb (Nat.mul 3 n0) m) eqn:Hcase.
              +++ destruct n0.
                  --- replace (Nat.add n (Nat.mul 3 0)) with n by lia.
                      replace (z + Z.of_nat m + Z.of_nat 0) with (z + Z.of_nat m) by lia.
                      destruct (H2 (z + Z.of_nat m)).
                      exact H13.
                  --- assert (
                      ~ In gen (delta_n regles c (n + 3 * S n0) (z + Z.of_nat m + Z.of_nat (S n0))) /\
                      ~ In build_l (delta_n regles c (n + 3 * S n0) (z + Z.of_nat m + Z.of_nat (S n0))) /\
                      ~ In build_r (delta_n regles c (n + 3 * S n0) (z + Z.of_nat m + Z.of_nat (S n0)))
                      ).
                      *** apply (gen_or_build_r_or_build_l_m_cor_2 c (z + Z.of_nat m - 3*Z.of_nat (S n0)) n (3*(S n0))).
                          ++++ exact H1.
                          ++++ exists (z + Z.of_nat m).
                               split.
                               ---- left.
                                    exact (conj H6 (H2 (z + Z.of_nat m))).
                               ---- intros.
                                    destruct (H7 z_prime H12) as [H13 [H14 [H15 H16]]].
                                    exact (conj H13 (H2 z_prime)).
                          ++++ apply Nat.leb_le in Hcase.
                               assert (1 <= 3 * S n0 <= m)%nat by lia.
                               replace (z + Z.of_nat m - 3 * Z.of_nat (S n0)) with (z + Z.of_nat m - Z.of_nat (3* (S n0))) by lia.
                               exact (H0 (Nat.mul 3 (S n0)) H12).
                          ++++ lia.
                     *** destruct H12 as [H13 [H14 H15]].
                         exact H15.
              +++ assert (
                  ~ In gen (delta_n regles c (n + 3 * n0) (z + Z.of_nat m + Z.of_nat n0)) /\
                  ~ In build_l (delta_n regles c (n + 3 * n0) (z + Z.of_nat m + Z.of_nat n0)) /\
                  ~ In build_r (delta_n regles c (n + 3 * n0) (z + Z.of_nat m + Z.of_nat n0))
                  ).
                  --- apply (gen_or_build_r_or_build_l_m_cor_3 c (z + 3*Z.of_nat n0 - Z.of_nat m) n (3* n0)).
                      *** exact H1.
                      *** exists (z + Z.of_nat m).
                          split.
                          ++++ left.
                               exact (conj H6 (H2 (z + Z.of_nat m))).
                          ++++ intros.
                               destruct (H7 z_prime H12) as [H13 [H14 [H15 H16]]].
                               exact (conj H13 (H2 z_prime)).
                      *** apply Nat.leb_gt in Hcase.
                          assert (m + 1 <= 3*n0 < 3 * m)%nat by lia.
                          replace (z + 3 * Z.of_nat n0 - Z.of_nat m) with (z + Z.of_nat (3 * n0) - Z.of_nat m) by lia.
                          exact (H10 (Nat.mul 3 n0) H12).
                      *** lia.
                  --- destruct H12 as [H13 [H14 H15]].
                      exact H15.
           ** assert (m - 1 < m)%nat by lia.
              assert( forall z_prime,
              z + Z.of_nat m <> z_prime ->
              ~ In slow_1 (delta_n regles c n z_prime) /\
              ~ In slow_2 (delta_n regles c n z_prime) /\
              ~ In slow_3 (delta_n regles c n z_prime)).
              +++ intros.
                  destruct (H7 z_prime H13).
                  exact H15. 
              +++ destruct (propagation_slow_m_3 (z + Z.of_nat m) c n m H1 (conj H11 (conj H3 (conj H4 (conj H5 H13)))) (m-1) H12) as [H14 [H15 [H16 H17]]].
                  replace (z + 2 * Z.of_nat m - 1) with (z + Z.of_nat m + Z.of_nat (m - 1)) by lia.
                  exact H14.
          ++ assert (m + 1 <= 3*(m - 1)+2 < 3 * m)%nat by lia.
             replace (z + 2 * Z.of_nat m - 1) with (z + Z.of_nat (3 * (m - 1) + 2) - Z.of_nat m) by lia.
             rewrite <- Nat.add_assoc.
             exact (H10 (Nat.add (Nat.mul 3 (Nat.sub m 1)) 2) H11).
        * split.
          ++ exact H11.
          ++ intros. 
             destruct (Nat.leb p m) eqn:Hcase.
             -- rewrite Nat.leb_le in Hcase.
                assert (1 <= p <= m)%nat by lia.
                apply (H0 p) in H13.
                assert (~(In gen (delta_n regles c (n+p) (z + Z.of_nat m - Z.of_nat p))) /\ ~(In build_r (delta_n regles c (n+p) (z + Z.of_nat m - Z.of_nat p))) /\
                forall z_prime, (z + Z.of_nat m - Z.of_nat p) <> z_prime -> ~(In gen (delta_n regles c (n+p) z_prime)) /\ ~(In build_l (delta_n regles c (n+p) z_prime)) /\ ~(In build_r (delta_n regles c (n+p) z_prime))).
                ** apply gen_or_build_r_or_build_l_m_cor_2.
                   +++ exact H1.
                   +++ exists (z + Z.of_nat m).
                       split.
                       --- left.
                           specialize (H2 (z + Z.of_nat m)).
                           exact (conj H6 H2).
                       --- intros.
                           destruct (H7 z_prime0 H14).
                           specialize (H2 (z_prime0)).
                           exact (conj H15 H2).
                   +++ exact H13.
                ** destruct H14 as [H14 [H15 H16]].
                   destruct (z + Z.of_nat m - Z.of_nat p =? z_prime) eqn:Heq.
                   +++ apply Z.eqb_eq in Heq.
                       rewrite Heq in H14.
                       exact H14.
                   +++ apply Z.eqb_neq in Heq.
                       apply H16 in Heq.
                       destruct Heq.
                       exact H17.
             -- rewrite Nat.leb_gt in Hcase.
                assert (~(In gen (delta_n regles c (n+p) (z + Z.of_nat p - Z.of_nat m))) /\ ~(In build_l (delta_n regles c (n+p) (z + Z.of_nat p - Z.of_nat m))) /\
                forall z_prime, (z + Z.of_nat p - Z.of_nat m) <> z_prime -> ~(In gen (delta_n regles c (n+p) z_prime)) /\ ~(In build_l (delta_n regles c (n+p) z_prime)) /\ ~(In build_r (delta_n regles c (n+p) z_prime))).
                ** apply gen_or_build_r_or_build_l_m_cor_3.
                   +++ exact H1.
                   +++ exists (z + Z.of_nat m).
                       split.
                       --- left.
                           specialize (H2 (z + Z.of_nat m)).
                           exact (conj H6 H2).
                       --- intros.
                           destruct (H7 z_prime0 H13).
                           specialize (H2 (z_prime0)).
                           exact (conj H14 H2).
                   +++ destruct (Nat.eqb p (Nat.mul 3 m)) eqn:Heq.
                       --- apply Nat.eqb_eq in Heq.
                           rewrite Heq.
                           replace  (z + Z.of_nat (3 * m) - Z.of_nat m) with (z + 2 * Z.of_nat m) by lia.
                           exact H11.
                       --- apply Nat.eqb_neq in Heq.
                           assert (m + 1 <= p < 3 * m)%nat by lia.
                           exact (H10 p H13).
                ** destruct H13 as [H13 [H14 H15]].
                   destruct (z + Z.of_nat p - Z.of_nat m =? z_prime) eqn:Heq.
                   +++ apply Z.eqb_eq in Heq.
                       rewrite Heq in H13.
                       exact H13.
                   +++ apply Z.eqb_neq in Heq.
                       apply H15 in Heq.
                       destruct Heq.
                       exact H16.
Qed.


Lemma from_a_gen_to_another_aux_3 (c : config) (z : Z) (n m : nat) :
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) /\
  (forall z_prime, (z < z_prime) ->
    ~(In wall (delta_n regles c n z_prime))) /\
  (forall z_prime, (z + Z.of_nat m <> z_prime) ->
    ~(In gen (delta_n regles c n z_prime))) /\
  (forall p, (1<= p <= 3*m)%nat -> 
    forall z_prime, ~(In gen (delta_n regles c (n+p) z_prime))) 
  ->
  (forall p, (1 <= p <= 3*m + 1)%nat ->
    (forall z_prime, (z + Z.of_nat m < z_prime) ->
      ~(In wall (delta_n regles c (n+p) z_prime)))).
Proof.
  intros.
  destruct H as [H2 [H3 [H4 H5]]].
  destruct p.
  + inversion H0.
    inversion H.
  + induction p.
    1: replace (Nat.add n 1) with (S n) by lia.
    2: replace (Nat.add n (S (S p))) with (S (n + (S p))) by lia.
    all: cbn [delta_n]; intro; apply delta_delta_n_comm in H; apply in_wall in H.
    all: destruct H as [H | [H | H]].
    - assert (z < z_prime) by lia.
      specialize (H3 z_prime H6).
      contradiction.
    - destruct (H2 z_prime).
      contradiction.
    - assert (z + Z.of_nat m <> z_prime) by lia.
      specialize (H4 z_prime H6).
      contradiction.
    - assert (1 <= S p <= 3 * m + 1)%nat by lia.
      apply IHp in H6.
      contradiction.
    - destruct (not_init_propagation c n (S p) H2 z_prime).
      contradiction.
    - assert (1 <= S p <= 3 * m)%nat by lia.
      specialize (H5 (S p) H6 z_prime).
      contradiction.
Qed.

Lemma from_a_gen_to_another (c : config) (z : Z) (n m : nat) :
  (m > 1)%nat ->
  (forall z, ~(In init_1 (delta_n regles c n z)) /\ ~(In init_2 (delta_n regles c n z)) /\ ~(In init_3 (delta_n regles c n z))) /\
  (forall z, ~(In build_l (delta_n regles c n z)) /\ ~(In build_r (delta_n regles c n z))) /\
  In slow_1 (delta_n regles c n (z + Z.of_nat m)) /\
  ~(In slow_2 (delta_n regles c n (z + Z.of_nat m))) /\
  ~(In slow_3 (delta_n regles c n (z + Z.of_nat m))) /\
  In gen (delta_n regles c n (z + Z.of_nat m)) /\
  (forall z_prime, (z + Z.of_nat m <> z_prime) ->
    ~(In gen (delta_n regles c n z_prime)) /\
    ~(In slow_1 (delta_n regles c n z_prime)) /\ 
    ~(In slow_2 (delta_n regles c n z_prime)) /\ 
    ~(In slow_3 (delta_n regles c n z_prime))) /\
  In wall (delta_n regles c n z) /\
  (forall z_prime, (z < z_prime) ->
    ~(In wall (delta_n regles c n z_prime)))
  -> 
  (forall z, ~(In build_l (delta_n regles c (n+3*m + 1) z)) /\ ~(In build_r (delta_n regles c (n+3*m + 1) z))) /\
  In slow_1 (delta_n regles c (n+3*m + 1) (z + 2*Z.of_nat m + 1)) /\
  ~(In slow_2 (delta_n regles c (n+3*m + 1) (z + 2*Z.of_nat m + 1))) /\
  ~(In slow_3 (delta_n regles c (n+3*m + 1) (z + 2*Z.of_nat m + 1))) /\
  In gen (delta_n regles c (n+3*m + 1) (z + 2*Z.of_nat m + 1)) /\
  (forall z_prime, (z + 2*Z.of_nat m + 1 <> z_prime) ->
    ~(In gen (delta_n regles c (n+3*m + 1) z_prime)) /\
    ~(In slow_1 (delta_n regles c (n+3*m + 1) z_prime)) /\ 
    ~(In slow_2 (delta_n regles c (n+3*m + 1) z_prime)) /\ 
    ~(In slow_3 (delta_n regles c (n+3*m + 1) z_prime))) /\
  In wall (delta_n regles c (n+3*m + 1) (z + Z.of_nat m)) /\
  (forall z_prime, (z + Z.of_nat m < z_prime) ->
    ~(In wall (delta_n regles c (n+3*m + 1) z_prime))).
Proof.
  intros.
  pose proof (from_a_gen_to_another_aux_1 c z n m H H0).
  pose proof (from_a_gen_to_another_aux_2 c z n m H H0).
  destruct H0 as [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 H11]]]]]]]].
  destruct H1 as [H12 [H13 [H14 H15]]].
  destruct H2 as [H16 H17].
  assert (In gen (delta_n regles c (n + 3 * m + 1) (z + 2 * Z.of_nat m + 1))).
  + replace (Nat.add (Nat.add n (Nat.mul 3 m)) 1) with (S (n + 3 * m)) by lia.
    cbn [delta_n].
    apply delta_delta_n_comm.
    apply in_gen.
    replace (z + 2 * Z.of_nat m + 1 - 1) with (z + 2 * Z.of_nat m) by lia.
    exact (conj H12 H16).
  + assert (
    ~(In build_l (delta_n regles c (n + (3 * m + 1)) (z + 2 * Z.of_nat m + 1))) /\ ~(In build_r (delta_n regles c (n + (3 * m + 1)) (z + 2 * Z.of_nat m + 1))) /\
    forall z_prime, (z + 2 * Z.of_nat m + 1) <> z_prime -> ~(In gen (delta_n regles c (n + (3 * m + 1)) z_prime)) /\ ~(In build_l (delta_n regles c (n + (3 * m + 1)) z_prime)) /\ ~(In build_r (delta_n regles c (n + (3 * m + 1)) z_prime))).
    - apply gen_or_build_r_or_build_l_m_cor_1.
      * exact H3.
      * exists (z + Z.of_nat m).
        split.
        ++ left.
           exact (conj H8 (H4 (z+Z.of_nat m))).
        ++ intros.
           split.
           -- destruct (H9 z_prime H1).
              exact H2.
           -- exact (H4 z_prime).
      * rewrite Nat.add_assoc.
        exact H0.
    - destruct H1 as [H18 [H19 H20]].
      split.
      * intro.
        rewrite <- Nat.add_assoc.
        destruct (z + 2 * Z.of_nat m + 1 =? z0) eqn:Heq.
        ++ apply Z.eqb_eq in Heq.
           rewrite <- Heq.
           exact (conj H18 H19).
        ++ apply Z.eqb_neq in Heq.
           destruct (H20 z0 Heq).
           exact H2.
      * repeat split.
        1,2,3,6,7,8: replace (Nat.add (Nat.add n (Nat.mul 3 m)) 1) with (S (n+ 3 * m)) by lia;
                cbn [delta_n].
        2,3: assert (z + 2 * Z.of_nat m <> z + 2 * Z.of_nat m + 1) by lia;
             destruct (H15 (z + 2 * Z.of_nat m + 1) H1) as [H22 [H23 H24]];
             intro;
             apply delta_delta_n_comm in H2.
        ++ apply delta_delta_n_comm.
           apply in_slow_1.
           right; right.
           replace (z + 2 * Z.of_nat m + 1 - 1) with (z + 2 * Z.of_nat m) by lia.
           exact (conj H12 H16).
        ++ apply in_slow_2 in H2.
           destruct H2.
           contradiction.
        ++ apply in_slow_3 in H2.
           contradiction.
        ++ intro.
           apply delta_delta_n_comm in H2.
           apply in_slow_1 in H2.
           assert (z + 2 * Z.of_nat m <> z_prime - 1) by lia.
           destruct (H15 (z_prime - 1) H21) as [H22 [H23 H24]].
           destruct H2 as [H2 | [H2 | [H2 H25]]].
           2,3: contradiction.
           destruct (not_init_propagation c n (3*m) H3 z_prime).
           contradiction.
        ++ intro.
           apply delta_delta_n_comm in H2.
           apply in_slow_2 in H2.
           destruct H2.
           destruct (z + 2 * Z.of_nat m =? z_prime) eqn:Heq.
           -- apply Z.eqb_eq in Heq.
              rewrite <- Heq in H21.
              contradiction.
           -- apply Z.eqb_neq in Heq.
              destruct (H15 z_prime Heq).
              contradiction.
        ++ intro.
           apply delta_delta_n_comm in H2.
           apply in_slow_3 in H2.
           destruct (z + 2 * Z.of_nat m =? z_prime) eqn:Heq.
           -- apply Z.eqb_eq in Heq.
              rewrite <- Heq in H2.
              contradiction.
           -- apply Z.eqb_neq in Heq.
              destruct (H15 z_prime Heq) as [H21 [H22 H23]].
              contradiction.
        ++ exact H0.
        ++ destruct (H20 z_prime H1).
           rewrite <- Nat.add_assoc.
           exact H2.
        ++ replace (Nat.add (Nat.add n (Nat.mul 3 m)) 1) with (S(n + 3 * m )) by lia.
           apply in_wall_m.
           right; right; exact H8.
        ++ assert (forall z_prime, (z + Z.of_nat m <> z_prime) ->
           ~(In gen (delta_n regles c n z_prime))).
           -- intros.
              destruct (H9 (z_prime) H1).
              exact H2.
           -- intros.
              assert (1 <= 3 * m + 1 <= 3 * m + 1)%nat by lia.
              rewrite <- Nat.add_assoc.
              exact (from_a_gen_to_another_aux_3 c z n m (conj H3 (conj H11 (conj H1 H17))) (3 * m + 1) H21 z_prime H2).
Qed.

(* 6 premières configurations *) 

Lemma description_config_0 :
  In init_1 (config_0 0) /\ 
  (forall z, z <> 0 -> ~(In init_1 (config_0 z))) /\
  (forall z, 
    ~(In init_2 (config_0 z)) /\
    ~(In init_3 (config_0 z)) /\
    ~(In wall (config_0 z)) /\
    ~(In slow_1 (config_0 z)) /\
    ~(In slow_2 (config_0 z)) /\
    ~(In slow_3 (config_0 z)) /\
    ~(In build_r (config_0 z)) /\
    ~(In build_l (config_0 z)) /\
    ~(In gen (config_0 z)) /\
    ~(In bounce_r (config_0 z)) /\
    ~(In bounce_l (config_0 z)) /\
    ~(In composite (config_0 z))
  ).
Proof.
  repeat split.
  1: simpl; left; reflexivity.
  1: intros.
  all: unfold config_0; destruct (z =? 0) eqn:Heq.
  1: apply Z.eqb_eq in Heq; contradiction.
  all: simpl; intro.
  1,3,5,7,9,11,13,15,17,19,21,23,25: contradiction.
  all: destruct H.
  1,3,5,7,9,11,13,15,17,19,21,23: inversion H.
  all: contradiction.
Qed.

Lemma description_config_1 :
  In init_2 (delta_n regles config_0 1 0) /\ 
  In slow_1 (delta_n regles config_0 1 0) /\ 
  In wall (delta_n regles config_0 1 0) /\ 
  In composite (delta_n regles config_0 1 0) /\ 
  (forall z, z <> 0 -> 
    ~(In init_2 (delta_n regles config_0 1 z)) /\ 
    ~(In slow_1 (delta_n regles config_0 1 z)) /\ 
    ~(In wall (delta_n regles config_0 1 z)) /\ 
    ~(In composite (delta_n regles config_0 1 z))
  ) /\
  (forall z, 
    ~(In init_1 (delta_n regles config_0 1 z)) /\
    ~(In init_3 (delta_n regles config_0 1 z)) /\
    ~(In slow_2 (delta_n regles config_0 1 z)) /\
    ~(In slow_3 (delta_n regles config_0 1 z)) /\
    ~(In build_r (delta_n regles config_0 1 z)) /\
    ~(In build_l (delta_n regles config_0 1 z)) /\
    ~(In gen (delta_n regles config_0 1 z)) /\
    ~(In bounce_r (delta_n regles config_0 1 z)) /\
    ~(In bounce_l (delta_n regles config_0 1 z))
   ).
Proof.
  pose proof description_config_0.
  destruct H as [H1 [H2 H3]].
  repeat split.
  all: cbn [delta_n].
  5-17: intro; 
        destruct (H3 (z-1)) as [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]]]];
        destruct (H3 z) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 [H26 [H27 H28]]]]]]]]]]];
        destruct (H3 (z+1)) as [H29 [H30 [H31 [H32 [H33 [H34 [H35 [H36 [H37 [H38 [H39 H40]]]]]]]]]]].
  + apply in_init_2.
    exact H1.
  + apply in_slow_1.
    left; exact H1.
  + apply in_wall.
    right; left; exact H1.
  + apply in_composite.
    left; exact H1.
  + apply in_init_2 in H0.
    apply (H2 z H).
    exact H0.
  + apply in_slow_1 in H0.
    destruct H0 as [H0 | [H0 | [H0 H4]]].
    2,3: contradiction.
    - apply (H2 z H).
      exact H0.
  + apply in_wall in H0.
    destruct H0 as [H0 | [H0 | H0]].
    1,3: contradiction.
    - apply (H2 z H).
      exact H0.
  + apply in_composite in H0.
    destruct H0 as [H0 | [H0 | H0]].
    2,3: contradiction.
    - apply (H2 z H).
      exact H0.
  + apply in_init_1 in H.
    inversion H.
  + apply in_init_3 in H.
    contradiction.
  + apply in_slow_2 in H.
    destruct H; contradiction.
  + apply in_slow_3 in H.
    contradiction.
  + apply in_build_r in H.
    destruct H as [H | [[H H0] | [H H0]]].
    all: contradiction.
  + apply in_build_l in H.
    destruct H as [H | [H H0]].
    all: contradiction.
  + apply in_gen in H.
    destruct H.
    contradiction.
  + apply in_bounce_r in H.
    destruct H as [[H H0] | [H H0]].
    all: contradiction.
  + apply in_bounce_l in H.
    destruct H as [H | [[H H0] | [H H0]]].
    all: contradiction.
Qed. 

Lemma description_config_2 :
  In init_3 (delta_n regles config_0 2 0) /\ 
  In slow_2 (delta_n regles config_0 2 0) /\ 
  In wall (delta_n regles config_0 2 0) /\  
  (forall z, z <> 0 -> 
    ~(In init_3 (delta_n regles config_0 2 z)) /\ 
    ~(In slow_2 (delta_n regles config_0 2 z)) /\ 
    ~(In wall (delta_n regles config_0 2 z))
  ) /\
  In composite (delta_n regles config_0 2 (-1)) /\  
  (forall z, z <> - 1 -> 
    ~(In composite (delta_n regles config_0 2 z))
  ) /\
  (forall z, 
    ~(In init_1 (delta_n regles config_0 2 z)) /\
    ~(In init_2 (delta_n regles config_0 2 z)) /\
    ~(In slow_1 (delta_n regles config_0 2 z)) /\
    ~(In slow_3 (delta_n regles config_0 2 z)) /\
    ~(In build_r (delta_n regles config_0 2 z)) /\
    ~(In build_l (delta_n regles config_0 2 z)) /\
    ~(In gen (delta_n regles config_0 2 z)) /\
    ~(In bounce_r (delta_n regles config_0 2 z)) /\
    ~(In bounce_l (delta_n regles config_0 2 z))
   ).
Proof.
  pose proof description_config_1.
  destruct H as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  replace (delta_n regles config_0 2) with (delta_n regles (delta regles config_0) 1) by reflexivity.
  repeat split.
  8: intros.
  4-6,8-17: intro; 
        destruct (H6 (z-1)) as [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]];
        destruct (H6 z) as [H16 [H17 [H18 [H19 [H20 [H21 [H22 [H23 H24]]]]]]]];
        destruct (H6 (z+1)) as [H25 [H26 [H27 [H28 [H29 [H30 [H31 [H32 H33]]]]]]]].
  + apply delta_delta_n_comm.
    apply in_init_3.
    exact H1.
  + apply delta_delta_n_comm.
    apply in_slow_2.
    destruct (H6 0) as [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]]].
    split.
    - exact H2.
    - intro; contradiction. 
  + apply delta_delta_n_comm.
    apply in_wall.
    left; exact H3.
  + apply delta_delta_n_comm in H0.
    apply in_init_3 in H0.
    destruct (H5 z H).
    apply H34; exact H0.
  + apply delta_delta_n_comm in H0.
    apply in_slow_2 in H0.
    destruct H0.
    destruct (H5 z H) as [H35 [H36 H37]].
    apply H36; exact H0.
  + apply delta_delta_n_comm in H0.
    apply in_wall in H0.
    destruct H0 as [H0 | [H0 | H0]].
    - destruct (H5 z H) as [H34 [H35 [H36 H37]]].
      apply H36; exact H0.
    - apply H16; exact H0.
    - apply H22; exact H0.
  + apply delta_delta_n_comm in H0.
    apply in_composite in H0.
    destruct H0 as [H0 | [H0 | H0]].
    - apply H16; exact H0.
    - assert (z+1 <> 0) by lia.
      destruct (H5 (z+1) H34) as [H35 [H36 [H37 H38]]].
      apply H38; exact H0.
    - apply H33; exact H0.
  + apply delta_delta_n_comm in H.
    apply in_init_1 in H.
    inversion H.
  + apply delta_delta_n_comm in H.
    apply in_init_2 in H.
    apply H16; exact H.
  + apply delta_delta_n_comm in H.
    apply in_slow_1 in H.
    destruct H as [H | [H | [H H0]]].
    - apply H16; exact H.
    - apply H10; exact H.
    - apply H11; exact H0.
  + apply delta_delta_n_comm in H.
    apply in_slow_3 in H.
    apply H18; exact H.
  + apply delta_delta_n_comm in H.
    apply in_build_r in H.
    destruct H as [H | [[H H0] | [H H0]]].
    - apply H17; exact H.
    - apply H12; exact H.
    - apply H11; exact H0.
  + apply delta_delta_n_comm in H.
    apply in_build_l in H.
    destruct H as [H | [H H0]].
    - apply H31; exact H.
    - apply H30; exact H.
  + apply delta_delta_n_comm in H.
    apply in_gen in H.
    destruct H.
    apply H11; exact H0.
  + apply delta_delta_n_comm in H.
    apply in_bounce_r in H.
    destruct H as [[H H0] | [H H0]].
    - apply H15; exact H.
    - apply H14; exact H.
  + apply delta_delta_n_comm in H.
    apply in_bounce_l in H.
    destruct H as [H | [[H H0] | [H H0]]].
    - apply H31; exact H.
    - apply H33; exact H.
    - apply H32; exact H.
  + apply delta_delta_n_comm.
    apply in_composite.
    right; left.
    replace (-1 +1) with 0 by lia.
    exact H4.
Qed.

Lemma description_config_3 :
  In slow_3 (delta_n regles config_0 3 0) /\ 
  In wall (delta_n regles config_0 3 0) /\  
  In build_r (delta_n regles config_0 3 0) /\  
  (forall z, z <> 0 -> 
    ~(In slow_3 (delta_n regles config_0 3 z)) /\ 
    ~(In wall (delta_n regles config_0 3 z)) /\
    ~(In build_r (delta_n regles config_0 3 z))
  ) /\
  In composite (delta_n regles config_0 3 (-2)) /\  
  (forall z, z <> - 2 -> 
    ~(In composite (delta_n regles config_0 3 z))
  ) /\
  (forall z, 
    ~(In init_1 (delta_n regles config_0 3 z)) /\
    ~(In init_2 (delta_n regles config_0 3 z)) /\
    ~(In init_3 (delta_n regles config_0 3 z)) /\
    ~(In slow_1 (delta_n regles config_0 3 z)) /\
    ~(In slow_2 (delta_n regles config_0 3 z)) /\
    ~(In build_l (delta_n regles config_0 3 z)) /\
    ~(In gen (delta_n regles config_0 3 z)) /\
    ~(In bounce_r (delta_n regles config_0 3 z)) /\
    ~(In bounce_l (delta_n regles config_0 3 z))
   ).
Proof.
  pose proof description_config_2.
  destruct H as [H [H0 [H1 [H2 [H3 [H4 H5]]]]]].
  replace (delta_n regles config_0 3) with (delta_n regles (delta regles config_0) 2) by reflexivity.
  repeat split.
  4-6,8-17: intro; 
        destruct (H5 (z-1)) as [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]];
        destruct (H5 z) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]];
        destruct (H5 (z+1)) as [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 H34]]]]]]]].
  1-3: apply delta_delta_n_comm.
  + apply in_slow_3.
    exact H0.
  + apply in_wall.
    left; exact H1.
  + apply in_build_r.
    left; exact H.
  + apply delta_delta_n_comm in H7.
    apply in_slow_3 in H7.
    destruct (H2 z H6) as [H35 [H36 H37]].
    apply H36; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_wall in H7.
    destruct H7 as [H7 | [H7 | H7]].
    - destruct (H2 z H6) as [H35 [H36 H37]].
      apply H37; exact H7.
    - apply H17; exact H7.
    - apply H23; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_build_r in H7.
    destruct H7 as [H7 | [[H7 H35] | [H7 H35]]].
    - destruct (H2 z H6).
      apply H35; exact H7.
    - apply H13; exact H7.
    - apply H12; exact H35.
  + intros H6 H7.
    apply delta_delta_n_comm in H7.
    apply in_composite in H7.
    destruct H7 as [H7 | [H7 | H7]].
    - apply H17; exact H7.
    - assert (z + 1 <> -1) by lia.
      apply (H4 (z+1) H35).
      exact H7.
    - apply H34; exact H7.
  + apply delta_delta_n_comm in H6.
    apply in_init_1 in H6.
    inversion H6.
  + apply delta_delta_n_comm in H6.
    apply in_init_2 in H6.
    apply H17; exact H6.
  + apply delta_delta_n_comm in H6.
    apply in_init_3 in H6.
    apply H18; exact H6.
  + apply delta_delta_n_comm in H6.
    apply in_slow_1 in H6.
    destruct H6 as [H6 | [H6 | [H6 H7]]].
    - apply H17; exact H6.
    - apply H11; exact H6.
    - apply H10; exact H6.
  + apply delta_delta_n_comm in H6.
    apply in_slow_2 in H6.
    destruct H6.
    apply H19; exact H6.
  + apply delta_delta_n_comm in H6.
    apply in_build_l in H6.
    destruct H6 as [H6 | [H6 H7]].
    - apply H32; exact H6.
    - apply H31; exact H6.
  + apply delta_delta_n_comm in H6.
    apply in_gen in H6.
    destruct H6.
    apply H10; exact H6.
  + apply delta_delta_n_comm in H6.
    apply in_bounce_r in H6.
    destruct H6 as [[H6 H7] | [H6 H7]].
    - apply H16; exact H6.
    - apply H15; exact H6.
  + apply delta_delta_n_comm in H6.
    apply in_bounce_l in H6.
    destruct H6 as [H6 | [[H6 H7] | [H6 H7]]].
    - apply H32; exact H6.
    - apply H34; exact H6.
    - apply H33; exact H6.
  + apply delta_delta_n_comm.
    apply in_composite.
    replace (-2+1) with (-1) by lia.
    right; left; exact H3.
Qed.

Lemma description_config_4 :
  In wall (delta_n regles config_0 4 0) /\  
  (forall z, z <> 0 -> 
    ~(In wall (delta_n regles config_0 4 z))
  ) /\
  In slow_1 (delta_n regles config_0 4 1) /\ 
  In build_r (delta_n regles config_0 4 1) /\ 
  (forall z, z <> 1 -> 
    ~(In slow_1 (delta_n regles config_0 4 z)) /\
    ~(In build_r (delta_n regles config_0 4 z))
  ) /\
  In composite (delta_n regles config_0 4 (-3)) /\  
  (forall z, z <> - 3 -> 
    ~(In composite (delta_n regles config_0 4 z))
  ) /\
  (forall z, 
    ~(In init_1 (delta_n regles config_0 4 z)) /\
    ~(In init_2 (delta_n regles config_0 4 z)) /\
    ~(In init_3 (delta_n regles config_0 4 z)) /\
    ~(In slow_2 (delta_n regles config_0 4 z)) /\
    ~(In slow_3 (delta_n regles config_0 4 z)) /\
    ~(In build_l (delta_n regles config_0 4 z)) /\
    ~(In gen (delta_n regles config_0 4 z)) /\
    ~(In bounce_r (delta_n regles config_0 4 z)) /\
    ~(In bounce_l (delta_n regles config_0 4 z))
   ).
Proof.
  pose proof description_config_3.
  destruct H as [H [H0 [H1 [H2 [H3 [H4 H5]]]]]].
  replace (delta_n regles config_0 4) with (delta_n regles (delta regles config_0) 3) by reflexivity.
  split.
  + apply delta_delta_n_comm.
    apply in_wall.
    left; exact H0.
  + split.
    - intros z H6 H7.
      apply delta_delta_n_comm in H7.
      apply in_wall in H7.
      destruct (H5 z) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]].
      destruct (H2 z H6) as [H8 [H9 H10]].
      destruct H7 as [H7 | [H7 | H7]].
      * apply H9; exact H7.
      * apply H17; exact H7.
      * apply H23; exact H7.
    - split.
      * apply delta_delta_n_comm.
        apply in_slow_1.
        right; left; replace (1-1) with 0 by lia; exact H.
      * split.
        ++ apply delta_delta_n_comm.
           apply in_build_r.
           destruct (H5 0) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]].
           right; right; replace (1-1) with 0 by lia; exact (conj H20 H1).
        ++ split.
           -- intros.
              repeat split.
              all: intro; apply delta_delta_n_comm in H7.
              ** apply in_slow_1 in H7.
                 destruct H7 as [H7 | [H7 | H7]].
                 +++ destruct (H5 z) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]].
                     apply H17; exact H7.
                 +++ assert (z - 1 <> 0) by lia.
                     destruct (H2 (z-1) H8).
                     apply H9; exact H7.
                 +++ destruct (H5 (z-1)) as [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]].
                     destruct H7.
                     apply H11; exact H7.
              ** apply in_build_r in H7.
                 destruct H7 as [H7 | [[H7 H8] | [H7 H8]]].
                 +++ destruct (H5 z) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]].
                     apply H19; exact H7.
                 +++ destruct (H5 (z-1)) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]].
                     apply H22; exact H7.
                 +++ assert (z - 1 <> 0) by lia.
                     destruct (H2 (z-1) H9) as [H10 [H11 H12]].
                     apply H12; exact H8.
           -- split.
              ** apply delta_delta_n_comm.
                 apply in_composite.
                 replace (-3+1) with (-2) by lia.
                 right; left; exact H3.
              ** repeat split.
                 1: intros.
                 all: intro; 
                      destruct (H5 (z-1)) as [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]];
                      destruct (H5 z) as [H17 [H18 [H19 [H20 [H21 [H22 [H23 [H24 H25]]]]]]]];
                      destruct (H5 (z+1)) as [H26 [H27 [H28 [H29 [H30 [H31 [H32 [H33 H34]]]]]]]].
                 2-10: apply delta_delta_n_comm in H6.
                 +++ apply delta_delta_n_comm in H7.
                     apply in_composite in H7.
                     destruct H7 as [H7 | [H7 | H7]].
                     --- apply H17; exact H7.
                     --- assert (z + 1 <> -2) by lia.
                         apply (H4 (z+1) H35).
                         exact H7.
                     --- apply H34; exact H7.
                 +++ apply in_init_1 in H6.
                     inversion H6.
                 +++ apply in_init_2 in H6.
                     apply H17; exact H6.
                 +++ apply in_init_3 in H6.
                     apply H18; exact H6.
                 +++ apply in_slow_2 in H6.
                     destruct H6.
                     apply H20; exact H6.
                 +++ apply in_slow_3 in H6.
                     apply H21; exact H6.
                 +++ apply in_build_l in H6.
                     destruct H6 as [H6 | [H6 H7]].
                     --- apply H32; exact H6.
                     --- apply H31; exact H6.
                 +++ apply in_gen in H6.
                     destruct H6.
                     apply H11; exact H6.
                 +++ apply in_bounce_r in H6.
                     destruct H6 as [[H6 H7] | [H6 H7]].
                     --- apply H16; exact H6.
                     --- apply H15; exact H6.
                 +++ apply in_bounce_l in H6.
                     destruct H6 as [H6 | [[H6 H7] | [H6 H7]]].
                     --- apply H32; exact H6.
                     --- apply H34; exact H6.
                     --- apply H33; exact H6.
Qed.

Lemma description_config_5_aux (c : config) :
  In wall (delta_n regles c 4 0) /\  
  (forall z, z <> 0 -> 
    ~(In wall (delta_n regles c 4 z))
  ) /\
  In slow_1 (delta_n regles c 4 1) /\ 
  In build_r (delta_n regles c 4 1) /\ 
  (forall z, z <> 1 -> 
    ~(In slow_1 (delta_n regles c 4 z)) /\
    ~(In build_r (delta_n regles c 4 z))
  ) /\
  In composite (delta_n regles c 4 (-3)) /\  
  (forall z, z <> - 3 -> 
    ~(In composite (delta_n regles c 4 z))
  ) /\
  (forall z, 
    ~(In init_1 (delta_n regles c 4 z)) /\
    ~(In init_2 (delta_n regles c 4 z)) /\
    ~(In init_3 (delta_n regles c 4 z)) /\
    ~(In slow_2 (delta_n regles c 4 z)) /\
    ~(In slow_3 (delta_n regles c 4 z)) /\
    ~(In build_l (delta_n regles c 4 z)) /\
    ~(In gen (delta_n regles c 4 z)) /\
    ~(In bounce_r (delta_n regles c 4 z)) /\
    ~(In bounce_l (delta_n regles c 4 z))
   )
  ->
  In wall (delta_n regles c 5 0) /\  
  (forall z, z <> 0 -> 
    ~(In wall (delta_n regles c 5 z))
  ) /\
  In slow_1 (delta_n regles c 5 2) /\ 
  In gen (delta_n regles c 5 2) /\ 
  (forall z, z <> 2 -> 
    ~(In slow_1 (delta_n regles c 5 z)) /\
    ~(In gen (delta_n regles c 5 z))
  ) /\
  In composite (delta_n regles c 5 (-4)) /\  
  (forall z, z <> - 4 -> 
    ~(In composite (delta_n regles c 5 z))
  ) /\
  (forall z, 
    ~(In init_1 (delta_n regles c 5 z)) /\
    ~(In init_2 (delta_n regles c 5 z)) /\
    ~(In init_3 (delta_n regles c 5 z)) /\
    ~(In slow_2 (delta_n regles c 5 z)) /\
    ~(In slow_3 (delta_n regles c 5 z)) /\
    ~(In build_r (delta_n regles c 5 z)) /\
    ~(In build_l (delta_n regles c 5 z)) /\
    ~(In bounce_r (delta_n regles c 5 z)) /\
    ~(In bounce_l (delta_n regles c 5 z))
   ).
Proof.
  intro.
  destruct H as [H [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]]].
  replace (delta_n regles c 5) with (delta_n regles (delta regles c) 4).
  repeat split.
  2,8: intros.
  2,3,6,7,9-17: intro; 
        destruct (H6 (z-1)) as [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 H17]]]]]]]];
        destruct (H6 z) as [H18 [H19 [H20 [H21 [H22 [H23 [H24 [H25 H26]]]]]]]];
        destruct (H6 (z+1)) as [H27 [H28 [H29 [H30 [H31 [H32 [H33 [H34 H35]]]]]]]].
  + apply delta_delta_n_comm.
    apply in_wall.
    left; exact H.
  + apply delta_delta_n_comm in H8.
    apply in_wall in H8.
    destruct H8 as [H8 | [H8 | H8]].
    - apply (H0 z H7); exact H8.
    - apply H18; exact H8.
    - apply H24; exact H8.
  + apply delta_delta_n_comm in H8.
    apply in_composite in H8.
    destruct H8 as [H8 | [H8 | H8]].
    - apply H18; exact H8.
    - assert (z+1 <> -3) by lia.
      apply (H5 (z+1) H36).
      exact H8.
    - apply H35; exact H8.
  + apply delta_delta_n_comm in H8.
    apply in_slow_1 in H8.
    destruct H8 as [H8 | [H8 | [H8 H36]]].
    - apply H18; exact H8.
    - apply H13; exact H8.
    - assert (z - 1 <> 1) by lia.
      apply (H3 (z-1) H37).
      exact H36.
  + apply delta_delta_n_comm in H8.
    apply in_gen in H8.
    destruct H8.
    assert (z - 1 <> 1) by lia.
    apply (H3 (z-1) H37).
    exact H36.
  + apply delta_delta_n_comm in H7.
    apply in_init_1 in H7.
    inversion H7.
  + apply delta_delta_n_comm in H7.
    apply in_init_2 in H7.
    apply H18; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_init_3 in H7.
    apply H19; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_slow_2 in H7.
    destruct H7.
    destruct (z =? 1) eqn:Heq.
    - apply Z.eqb_eq in Heq.
      rewrite Heq in H8.
      apply H8.
      exact H2.
    - apply Z.eqb_neq in Heq.
      destruct (H3 z Heq).
      apply H36; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_slow_3 in H7.
    apply H21; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_build_r in H7.
    destruct H7 as [H7 | [[H7 H8] | [H7 H8]]].
    - apply H20; exact H7.
    - apply H14; exact H7.
    - destruct (z =? 2) eqn:Heq.
      * apply Z.eqb_eq in Heq.
        rewrite Heq in H7.
        apply H7.
        replace (2-1) with 1 by lia.
        exact H1.
      * apply Z.eqb_neq in Heq.
        assert (z-1 <> 1) by lia.
        destruct (H3 (z-1) H36).
        apply H38; exact H8.
  + apply delta_delta_n_comm in H7.
    apply in_build_l in H7.
    destruct H7 as [H7 | [H7 H8]].
    - apply H33; exact H7.
    - apply H32; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_bounce_r in H7.
    destruct H7 as [[H7 H8] | [H7 H8]].
    - apply H17; exact H7.
    - apply H16; exact H7.
  + apply delta_delta_n_comm in H7.
    apply in_bounce_l in H7.
    destruct H7 as [H7 | [[H7 H8] | [H7 H8]]].
    - apply H33; exact H7.
    - apply H35; exact H7.
    - apply H34; exact H7.
  + apply delta_delta_n_comm.
    apply in_slow_1.
    replace (2-1) with 1 by lia.
    right; right; exact (conj H1 H2).
  + apply delta_delta_n_comm.
    apply in_gen.
    replace (2-1) with 1 by lia.
    exact (conj H1 H2).
  + apply delta_delta_n_comm.
    apply in_composite.
    replace (-4+1) with (-3) by lia.
    right; left; exact H4.
  + cbn [delta_n].
    reflexivity.
Qed.

Lemma description_config_5 :
  In wall (delta_n regles config_0 5 0) /\  
  (forall z, z <> 0 -> 
    ~(In wall (delta_n regles config_0 5 z))
  ) /\
  In slow_1 (delta_n regles config_0 5 2) /\ 
  In gen (delta_n regles config_0 5 2) /\ 
  (forall z, z <> 2 -> 
    ~(In slow_1 (delta_n regles config_0 5 z)) /\
    ~(In gen (delta_n regles config_0 5 z))
  ) /\
  In composite (delta_n regles config_0 5 (-4)) /\  
  (forall z, z <> - 4 -> 
    ~(In composite (delta_n regles config_0 5 z))
  ) /\
  (forall z, 
    ~(In init_1 (delta_n regles config_0 5 z)) /\
    ~(In init_2 (delta_n regles config_0 5 z)) /\
    ~(In init_3 (delta_n regles config_0 5 z)) /\
    ~(In slow_2 (delta_n regles config_0 5 z)) /\
    ~(In slow_3 (delta_n regles config_0 5 z)) /\
    ~(In build_r (delta_n regles config_0 5 z)) /\
    ~(In build_l (delta_n regles config_0 5 z)) /\
    ~(In bounce_r (delta_n regles config_0 5 z)) /\
    ~(In bounce_l (delta_n regles config_0 5 z))
   ).
Proof.
  apply (description_config_5_aux config_0 description_config_4).
Qed.

Lemma init_goes_well_for_gens :
  (forall z, ~(In init_1 (delta_n regles config_0 5 z)) /\ ~(In init_2 (delta_n regles config_0 5 z)) /\ ~(In init_3 (delta_n regles config_0 5 z))) /\
  (forall z, ~(In build_l (delta_n regles config_0 5 z)) /\ ~(In build_r (delta_n regles config_0 5 z))) /\
  In slow_1 (delta_n regles config_0 5 (0 + Z.of_nat 2)) /\
  ~(In slow_2 (delta_n regles config_0 5 (0 + Z.of_nat 2))) /\
  ~(In slow_3 (delta_n regles config_0 5 (0 + Z.of_nat 2))) /\
  In gen (delta_n regles config_0 5 (0 + Z.of_nat 2)) /\
  (forall z_prime, (0 + Z.of_nat 2 <> z_prime) ->
    ~(In gen (delta_n regles config_0 5 z_prime)) /\
    ~(In slow_1 (delta_n regles config_0 5 z_prime)) /\ 
    ~(In slow_2 (delta_n regles config_0 5 z_prime)) /\ 
    ~(In slow_3 (delta_n regles config_0 5 z_prime))) /\
  In wall (delta_n regles config_0 5 0) /\
  (forall z_prime, (0 < z_prime) ->
    ~(In wall (delta_n regles config_0 5 z_prime))).
Proof.
  pose proof description_config_5.
  destruct H as [H [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]]].
  split.
  + intro.
    destruct (H6 z) as [H7 [H8 [H9 H10]]].
    exact (conj H7 (conj H8 H9)).
  + split.
    - intro.
      destruct (H6 z) as [H7 [H8 [H9 [H11 [H12 [H13 [H14 H15]]]]]]].
      exact (conj H14 H13).
    - replace (0 + Z.of_nat 2) with 2 by lia.
      split.
      * exact H1.
      * split.
        ++ destruct (H6 2) as [H7 [H8 [H9 [H10 H11]]]].
           exact H10.
        ++ split.
           -- destruct (H6 2) as [H7 [H8 [H9 [H10 [H11 H12]]]]].
              exact H11.
           -- split.
              ** exact H2.
              ** split.
                 +++ repeat split.
                     --- assert (z_prime <> 2) by lia.
                         destruct (H3 z_prime H8).
                         exact H10.
                     --- assert (z_prime <> 2) by lia.
                         destruct (H3 z_prime H8).
                         exact H9.
                     --- destruct (H6 z_prime) as [H8 [H9 [H10 [H11 H12]]]].
                         exact H11.
                     --- destruct (H6 z_prime) as [H8 [H9 [H10 [H11 [H12 H13]]]]].
                         exact H12.
                 +++ split.
                     --- exact H.
                     --- intros.
                         assert (z_prime <> 0) by lia.
                         apply (H0 z_prime H8).
Qed.

Fixpoint sum_nat (m : nat) : nat :=
  match m with 
  |0%nat => 0
  |S p => sum_nat p + m
  end.

Lemma sum_nat_inf_square (m : nat) :
  (sum_nat m <= m*m)%nat.
Proof.
  induction m.
  + reflexivity.
  + simpl. lia.
Qed.


Lemma position_gen_aux_1 :
  forall n z, (n < 5)%nat -> ~(In gen (delta_n regles config_0 n z)).
Proof.
  intros.
  destruct n.
  + destruct description_config_0 as [H1 [H2 H3]].
    destruct (H3 z) as [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]].
    cbn [delta_n].
    exact H12.
  + destruct n.
    - destruct description_config_1 as [H1 [H2 [H3 [H4 [H5 H6]]]]].
      destruct (H6 z) as [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]].
      exact H13.
    - destruct n.
      * destruct description_config_2 as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
        destruct (H7 z) as [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]].
        exact H14.
      * destruct n.
        ++ destruct description_config_3 as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
           destruct (H7 z) as [H8 [H9 [H10 [H11 [H12 [H13 [H14 H15]]]]]]].
           exact H14.
        ++ destruct n.
           -- destruct description_config_4 as [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]].
              destruct (H8 z) as [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]].
              exact H15.
           -- do 5 (apply Nat.succ_lt_mono in H).
              inversion H.
Qed.

Lemma position_gen_aux_2 (m : nat) :
  (2*(S m)*(S m) - sum_nat (S m) = 2*m*m - sum_nat m + 3*m + 1)%nat.
Proof.
  cbn [sum_nat].
  replace (Nat.mul (2*(S m)) (S m)) with (Nat.add (2*m*m+3*m+1) (S m)) by lia.
  replace (Nat.sub (2 * m * m + 3 * m + 1 + S m) (sum_nat m + S m)) with (Nat.sub ((3 * m + 1) + (2 * m * m)) (sum_nat m)) by lia.
  rewrite <- (Nat.add_sub_assoc (3 * m + 1) (2 * m * m) (sum_nat m)).
  + lia.
  + pose proof (sum_nat_inf_square m).
    lia.
Qed.


Lemma position_gen_aux :
  forall m,
  (m > 1)%nat -> 
  (forall n z, (2*(m-1)*(m-1)-(sum_nat (m-1)) < n < 2*m*m-(sum_nat m))%nat -> ~(In gen (delta_n regles config_0 n z))) /\
  (forall z, 
    ~(In init_1 (delta_n regles config_0 (2*m*m-(sum_nat m)) z)) /\ 
    ~(In init_2 (delta_n regles config_0 (2*m*m-(sum_nat m)) z)) /\ 
    ~(In init_3 (delta_n regles config_0 (2*m*m-(sum_nat m)) z))
  ) /\
  (forall z, 
    ~(In build_l (delta_n regles config_0 (2*m*m-(sum_nat m)) z)) /\ 
    ~(In build_r (delta_n regles config_0 (2*m*m-(sum_nat m)) z))
  ) /\
  In slow_1 (delta_n regles config_0 (2*m*m-(sum_nat m)) ((Z.of_nat (sum_nat (m-1)) - 1) + Z.of_nat m)) /\
  ~(In slow_2 (delta_n regles config_0 (2*m*m-(sum_nat m)) ((Z.of_nat (sum_nat (m-1)) - 1) + Z.of_nat m))) /\
  ~(In slow_3 (delta_n regles config_0 (2*m*m-(sum_nat m)) ((Z.of_nat (sum_nat (m-1)) - 1) + Z.of_nat m))) /\
  In gen (delta_n regles config_0 (2*m*m-(sum_nat m)) ((Z.of_nat (sum_nat (m-1)) - 1) + Z.of_nat m)) /\
  (forall z_prime, ((Z.of_nat (sum_nat (m-1)) - 1) + Z.of_nat m <> z_prime) ->
    ~(In gen (delta_n regles config_0 (2*m*m-(sum_nat m)) z_prime)) /\
    ~(In slow_1 (delta_n regles config_0 (2*m*m-(sum_nat m)) z_prime)) /\ 
    ~(In slow_2 (delta_n regles config_0 (2*m*m-(sum_nat m)) z_prime)) /\ 
    ~(In slow_3 (delta_n regles config_0 (2*m*m-(sum_nat m)) z_prime))) /\
  In wall (delta_n regles config_0 (2*m*m-(sum_nat m)) (Z.of_nat (sum_nat (m-1)) - 1)) /\
  (forall z_prime, ((Z.of_nat (sum_nat (m-1)) - 1) < z_prime) ->
    ~(In wall (delta_n regles config_0 (2*m*m-(sum_nat m)) z_prime))).
Proof.
  destruct m.
  + intro; inversion H.
  + destruct m.
    - intro; inversion H; inversion H1.
    - induction m.
      * intro.
        replace (Nat.sub (Nat.mul (Nat.mul 2 2) 2) (sum_nat 2)) with 5%nat by reflexivity.
        split.
        ++ intros.
           apply position_gen_aux_1.
           lia.
        ++ replace (Z.of_nat (sum_nat (2 - 1)) - 1) with 0 by reflexivity.
           exact init_goes_well_for_gens.
      * intro.
        assert (S (S m) > 1)%nat by lia.
        apply IHm in H0 as H1.
        destruct H1 as [H2 H3].
        split.
        ++ intros.
           apply (from_a_gen_to_another_aux_2 config_0 (Z.of_nat (sum_nat (S (S m) - 1)) - 1) (2 * S (S m) * S (S m) - sum_nat (S (S m))) (S (S m)) H0) in H3.
           destruct H3.
           assert (1 <= n - (2 * (S (S (S m)) - 1) * (S (S (S m)) - 1) - sum_nat (S (S (S m)) - 1)) <= 3 * S (S m))%nat as H5.
           -- destruct H1.
              split.
              ** lia.
              ** replace (Nat.sub (S (S (S m))) 1) with (S (S m)) by lia.
                 rewrite position_gen_aux_2 in H5.
                 lia.
           -- specialize (H4 (Nat.sub n ((2 * (S (S (S m)) - 1) * (S (S (S m)) - 1) - sum_nat (S (S (S m)) - 1)))) H5 z) as H6. 
              replace (Nat.sub (S (S (S m))) 1) with (S (S m)) in H6, H1 by lia.
              replace (Nat.add (2 * S (S m) * S (S m) - sum_nat (S (S m))) ((n - (2 * S (S m) * S (S m) - sum_nat (S (S m)))))) with n in H6 by lia.
              exact H6.
        ++ apply from_a_gen_to_another in H3 as H4.
           destruct H3.
           specialize (not_init_propagation config_0 (2 * S (S m) * S (S m) - sum_nat (S (S m))) (3 * S (S m) + 1) H1) as H5.
           replace (Nat.add (2 * S (S m) * S (S m) - sum_nat (S (S m))) (3 * S (S m) + 1)) with (Nat.sub (2 * S (S (S m)) * S (S (S m))) (sum_nat (S (S (S m))))) in H5.
           replace (Nat.add (2 * S (S m) * S (S m) - sum_nat (S (S m)) + 3 * S (S m)) 1) with (Nat.sub (2 * S (S (S m)) * S (S (S m))) (sum_nat (S (S (S m))))) in H4.
           replace (Z.of_nat (sum_nat (S (S m) - 1)) - 1 + 2 * Z.of_nat (S (S m)) + 1) with (Z.of_nat (sum_nat (S (S (S m)) - 1)) - 1 + Z.of_nat (S (S (S m)))) in H4.
           replace (Z.of_nat (sum_nat (S (S m) - 1)) - 1 + Z.of_nat (S (S m))) with (Z.of_nat (sum_nat (S (S (S m)) - 1)) - 1) in H4.
           exact (conj H5 H4).
           1,2: replace (Nat.sub (S (S (S m))) 1) with (S (S m)) by lia;
              replace (Nat.sub (S (S m)) 1) with (S m) by lia;
              replace (sum_nat (S (S m))) with (Nat.add (sum_nat (S m)) (S (S m))) by reflexivity.
           1,2,5: lia.
           2: rewrite Nat.add_assoc.
           all: apply position_gen_aux_2.
Qed.


Lemma position_gen :
  forall m, (m > 1)%nat ->
    In gen (delta_n regles config_0 (2*m*m-(sum_nat m)) (Z.of_nat (sum_nat m) - 1)) /\
    (forall z, (Z.of_nat (sum_nat m) - 1) <> z -> ~(In gen (delta_n regles config_0 (2*m*m-(sum_nat m)) z))) /\
    (forall n z, (2*(m-1)*(m-1)-(sum_nat (m-1)) < n < 2*m*m-(sum_nat m))%nat -> ~(In gen (delta_n regles config_0 n z))).
Proof.
  intros.
  specialize (position_gen_aux m H) as H0.
  destruct H0 as [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]].
  replace (Z.of_nat (sum_nat (m - 1)) - 1 + Z.of_nat m) with (Z.of_nat (sum_nat m) - 1) in *.
  + repeat split.
    - exact H6.
    - intros.
      destruct (H7 z H10).
      exact H11.
    - exact H0.
  + destruct m.
    * inversion H.
    * replace (Nat.sub (S m) 1) with m by lia.
      simpl.
      lia.
Qed.

Lemma usefull_bounding (n : nat) :
  (n > 1)%nat ->
  exists m, (m > 1)%nat /\ (2*(m-1)*(m-1)-(sum_nat (m-1)) < n <= 2*m*m-(sum_nat m))%nat.
Proof.
  destruct n.
  + intro; inversion H.
  + destruct n.
    - intro; inversion H; inversion H1.
    - induction n.
      * exists 2%nat.
        split.
        2: simpl.
        all: lia.
      * intro.
        destruct IHn as [m [IHn]].
        ++ lia.
        ++ destruct (Nat.eqb (S (S n)) (2 * m * m - sum_nat m)) eqn:Heq.
           -- apply Nat.eqb_eq in Heq.
              exists (S m).
              replace (Nat.sub (S m) 1) with m by lia.
              rewrite position_gen_aux_2.
              lia.
           -- apply Nat.eqb_neq in Heq.
              exists m.
              lia.
Qed.

Lemma condition_gen (z : Z) (n : nat) :
  In gen (delta_n regles config_0 n z) <-> 
  exists m, (m > 1)%nat /\ (n = 2*m*m-(sum_nat m))%nat /\ (Z.of_nat (sum_nat m) - 1 = z).
Proof.
  destruct n.
  + split.
    all: intro.
    - destruct description_config_0 as [H1 [H2 H3]].
      destruct (H3 z) as [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]].
      simpl in H.
      contradiction.
    - destruct H as [m [H1 [H2 H3]]].
      destruct m.
      * inversion H1.
      * rewrite position_gen_aux_2 in H2.
        assert (0 <> 2 * m * m - sum_nat m + 3 * m + 1)%nat by lia.
        contradiction.
  + destruct n.
    - split.
      all: intro.
      * destruct description_config_1 as [H1 [H2 [H3 [H4 [H5 H6]]]]].
        destruct (H6 z) as [H7 [H8 [H9 [H10 [H11 [H12 [H13 H14]]]]]]].
        contradiction.
      * destruct H as [m [H1 [H2 H3]]].
        destruct m.
        ++ inversion H1.
        ++ destruct m.
           -- inversion H1; inversion H0.
           -- repeat rewrite position_gen_aux_2 in H2.
              assert (1%nat <> 2 * m * m - sum_nat m + 3 * m + 1 + 3 * S m + 1)%nat by lia.
              contradiction.
    - assert (S (S n) > 1)%nat by lia.
      apply usefull_bounding in H.
      destruct H as [m [H1 H2]].
      split.
      * intro.
        destruct (Nat.eqb (S (S n)) (2 * m * m - sum_nat m))%nat eqn:Heq.
        ++ exists m.
           apply Nat.eqb_eq in Heq.
           repeat split.
           -- exact H1.
           -- exact Heq.
           -- destruct (Z.of_nat (sum_nat m) - 1 =? z) eqn:Heqz.
              ** apply Z.eqb_eq in Heqz; exact Heqz.
              ** apply Z.eqb_neq in Heqz.
                 destruct (position_gen m H1) as [H3 [H4 H5]].
                 apply (H4 z) in Heqz as H6.
                 rewrite Heq in H.
                 contradiction.
        ++ destruct (position_gen m H1) as [H3 [H4 H5]].
           apply Nat.eqb_neq in Heq.
           assert (2 * (m - 1) * (m - 1) - sum_nat (m - 1) < S (S n) < 2 * m * m - sum_nat m)%nat by lia.
           apply (H5 (S (S n)) z) in H0.
           contradiction.
      * intro.
        destruct H as [m_prime [H3 [H4 H5]]].
        destruct (position_gen m_prime H3) as [H6 [H7 H8]].
        rewrite H4.
        rewrite <- H5.
        exact H6.
Qed.

Lemma condition_wall_aux (z : Z) (n : nat) :
  In wall (delta_n regles config_0 n z) <-> 
  (exists m, (n > m)%nat /\ (In gen (delta_n regles config_0 m z)))
  \/ ((n > 0)%nat /\ (z = 0)).
Proof.
  destruct n.
  + split.
    all: intro.
    - destruct description_config_0 as [H1 [H2 H3]].
      destruct (H3 z) as [H4 [H5 [H6 H7]]].
      simpl in H.
      contradiction.
    - destruct H as [[m [H1 H2]] | [H1 H2]].
      all: inversion H1.
  + induction n.
    - split.
      all: intro.
      * destruct description_config_1 as [H1 [H2 [H3 [H4 [H5 H6]]]]].
        destruct (z =? 0) eqn:Heq.
        ++ apply Z.eqb_eq in Heq.
           right; split.
           -- lia.
           -- exact Heq.
        ++ apply Z.eqb_neq in Heq.
           destruct (H5 z Heq) as [H7 [H8 [H9 H10]]].
           contradiction.
      * destruct H as [[m [H1 H2]] | [H1 H2]].
        ++ assert (m = 0)%nat by lia.
           cbn [delta_n].
           apply in_wall.
           rewrite H in H2.
           simpl in H2.
           right; right; exact H2.
        ++ destruct description_config_1 as [H3 [H4 [H5 H6]]].
           rewrite H2; exact H5.
    - split.
      all: intro.
      * cbn [delta_n] in *.
        apply delta_delta_n_comm in H.
        apply in_wall in H.
        destruct H as [H | [H | H]].
        ++ apply IHn in H.
           destruct H as [[m [H1 H2]] | H].
           -- left; exists m.
              split.
              ** lia.
              ** exact H2.
           -- right; split; lia.
        ++ apply delta_delta_n_comm in H.
           apply in_init_1 in H.
           contradiction. 
        ++ left; exists (S n); split.
           -- lia.
           -- cbn [delta_n].
              exact H. 
      * destruct H as [[m [H1 H2]] | [H1 H2]].
        ++ destruct (m =? S n)%nat eqn:Heq.
           -- apply Nat.eqb_eq in Heq.
              rewrite Heq in H2.
              cbn [delta_n] in *.
              apply delta_delta_n_comm.
              apply in_wall.
              right; right; exact H2.
           -- apply Nat.eqb_neq in Heq.
              assert (S n > m)%nat by lia.
              cbn [delta_n].
              apply delta_delta_n_comm.
              apply in_wall.
              left; apply IHn.
              left; exists m; exact (conj H H2).
        ++ cbn [delta_n].
           apply delta_delta_n_comm.
           apply in_wall.
           left; apply IHn.
           assert (S n > 0)%nat by lia.
           right; exact (conj H H2).
Qed.

Lemma condition_wall (z : Z) (n : nat) :
  In wall (delta_n regles config_0 n z) <-> 
  (exists m, (m > 1)%nat /\ (n > 2*m*m-(sum_nat m))%nat /\ (Z.of_nat (sum_nat m) - 1 = z))
  \/ ((n > 0)%nat /\ (z = 0)).
Proof.
  rewrite condition_wall_aux.
  split.
  all: intros; destruct H as [[m [H H1]] | H].
  2,4: right; exact H.
  all: left.
  + rewrite condition_gen in H1.
    destruct H1 as [m0 [H2 [H3 H4]]].
    exists m0.
    rewrite H3 in H.
    exact (conj H2 (conj H H4)).
  + set (m0 := Nat.sub (2 * m * m) (sum_nat m)).
    destruct H1.
    exists m0.
    split.
    - exact H0.
    - rewrite condition_gen.
      exists m.
      repeat split.
      * exact H.
      * exact H1.
Qed.

Lemma propagation_bounce_l (c : config) (n m : nat) : 
  forall z,
  In bounce_l (delta_n regles c n (z + Z.of_nat m)) /\
  (forall p, (0 <= p < m)%nat -> ~(In wall (delta_n regles c (n+p) (z + Z.of_nat (m - p)))))
  -> 
  In bounce_l (delta_n regles c (n+m) z).
Proof.
  induction m.
  + intros; destruct H.
    replace (z + Z.of_nat 0) with z in H by lia.
    rewrite Nat.add_0_r.
    exact H.
  + intros.
    destruct H.
    replace (Nat.add n (S m)) with (S (n+m)) by lia.
    cbn [delta_n].
    apply delta_delta_n_comm.
    apply in_bounce_l.
    right; left.
    split.
    - apply (IHm (z+1)).
      split.
      * replace (z + 1 + Z.of_nat m) with (z + Z.of_nat (S m)) by lia.
        exact H.
      * intros.
        assert (0 <= p < S m)%nat by lia.
        replace (z + 1 + Z.of_nat (m - p)) with (z + Z.of_nat (S m - p)) by lia.
        apply (H0 p H2).
    - assert (0 <= m < S m)%nat by lia.
      replace (z + 1) with (z + Z.of_nat (S m - m)) by lia.
      apply (H0 m H1).
Qed.

Lemma propagation_bounce_r (c : config) (z : Z) (n m : nat) :
  In bounce_r (delta_n regles c n z) /\
  (forall p, (0 <= p < m)%nat -> ~(In wall (delta_n regles c (n+p) (z + Z.of_nat p))))
  -> 
  In bounce_r (delta_n regles c (n+m) (z + Z.of_nat m)).
Proof.
  induction m.
  + intro; destruct H.
    replace (z + Z.of_nat 0) with z by lia.
    rewrite Nat.add_0_r.
    exact H.
  + intro.
    destruct H.
    replace (Nat.add n (S m)) with (S (n+m)) by lia.
    cbn [delta_n].
    apply delta_delta_n_comm.
    apply in_bounce_r.
    right; split.
    - replace (z + Z.of_nat (S m) - 1) with (z + Z.of_nat m) by lia.
      apply IHm.
      split.
      * exact H.
      * intros.
        assert (0 <= p < S m)%nat by lia.
        apply (H0 p H2).
    - assert (0 <= m < S m)%nat by lia.
      replace (z + Z.of_nat (S m) - 1) with (z + Z.of_nat m) by lia.
      apply (H0 m H1).
Qed.

Lemma bounce_l_between_walls_aux (c : config) (z : Z) (n m : nat) :
  (m > 1)%nat ->
  In wall (delta_n regles c n z) /\
  In wall (delta_n regles c n (z+Z.of_nat m)) /\
  In bounce_l (delta_n regles c n (z+Z.of_nat m-1)) /\ 
  (forall z_prime, 
    ((z <= z_prime < z+Z.of_nat m - 1) -> ~(In bounce_l (delta_n regles c n z_prime))) /\
    ((z < z_prime <= z+Z.of_nat m) -> 
      ~(In bounce_r (delta_n regles c n z_prime)) /\ (forall p, ~(In gen (delta_n regles c (n+p) z_prime)))
    ) /\
    ((z < z_prime < z+Z.of_nat m) -> forall p, ~(In wall (delta_n regles c (n+p) z_prime)))
  )
  -> 
  (forall p, 
    ((0 <= p < m)%nat -> (
      In bounce_l (delta_n regles c (n+p) (z + Z.of_nat m - 1 - Z.of_nat p)) /\
      (~(In bounce_r (delta_n regles c (n+p) (z + Z.of_nat m - 1 - Z.of_nat p)))
       \/ (z + Z.of_nat m - 1 - Z.of_nat p = z)) /\
      (forall z_prime, (z_prime <> (z + Z.of_nat m - 1 - Z.of_nat p)) ->
        ((z <= z_prime < z+Z.of_nat m) -> ~(In bounce_l (delta_n regles c (n+p) z_prime))) /\
        ((z < z_prime <= z+Z.of_nat m) -> ~(In bounce_r (delta_n regles c (n+p) z_prime)))
      )
    )) /\
    ((m <= p < 2*m)%nat -> (
      (~(In bounce_l (delta_n regles c (n+p) (z + Z.of_nat p - Z.of_nat m + 1)))
       \/ (z + Z.of_nat p - Z.of_nat m + 1 = z + Z.of_nat m)) /\
      In bounce_r (delta_n regles c (n+p) (z + Z.of_nat p - Z.of_nat m + 1)) /\
      (forall z_prime, (z_prime <> (z + Z.of_nat p - Z.of_nat m + 1)) ->
        ((z <= z_prime < z+Z.of_nat m) -> ~(In bounce_l (delta_n regles c (n+p) z_prime))) /\
        ((z < z_prime <= z+Z.of_nat m) -> ~(In bounce_r (delta_n regles c (n+p) z_prime)))
      ))
    )
  ).
Proof.
  intros.
  destruct H0 as [H0 [H1 [H2 H3]]].
  induction p.
  + split.
    - rewrite Nat.add_0_r.
      replace (z + Z.of_nat m - 1 - Z.of_nat 0) with (z + Z.of_nat m - 1) by lia.
      intro.
      repeat split.
      * exact H2.
      * assert (z < z + Z.of_nat m - 1 <= z + Z.of_nat m) by lia.
        destruct (H3 (z + Z.of_nat m - 1)) as [H6 [H7 H8]].
        destruct (H7 H5).
        left; exact H9.
      * intro.
        assert (z <= z_prime < z + Z.of_nat m - 1) by lia.
        destruct (H3 z_prime) as [H8 [H9 H10]].
        exact (H8 H7).
      * intro.
        destruct (H3 z_prime) as [H7 [H8 H9]].
        destruct (H8 H6).
        exact H10.
    - intro.
      destruct H4.
      assert (m > 0)%nat by lia.
      inversion H4.
      rewrite H7 in H6.
      inversion H6.
  + destruct IHp.
    replace (Nat.add n (S p)) with (S (n+p)) by lia.
    cbn [delta_n].
    destruct (Nat.ltb_spec (S p) m).
    - split.
      * intro.
        assert (0 <= p < m)%nat by lia.
        destruct (H4 H8) as [H9 [H10 H11]].
        repeat split.
        ++ apply delta_delta_n_comm.
           apply in_bounce_l.
           right; left; split.
           -- replace (z + Z.of_nat m - 1 - Z.of_nat (S p) + 1) with (z + Z.of_nat m - 1 - Z.of_nat p) by lia.
              exact H9.
           -- set (z_prime := z + Z.of_nat m - 1 - Z.of_nat (S p) + 1).
              assert (z < z_prime < z + Z.of_nat m) by lia.
              destruct (H3 z_prime) as [H13 [H14 H15]].
              apply (H15 H12).
        ++ destruct (z + Z.of_nat m - 1 - Z.of_nat (S p) =? z) eqn:Heq.
           -- apply Z.eqb_eq in Heq; right; exact Heq.
           -- apply Z.eqb_neq in Heq.
              left.
              intro.
              apply delta_delta_n_comm in H12.
              apply in_bounce_r in H12.
              destruct H12 as [[H12 H13] | [H12 H13]].
              ** set (z_prime := z + Z.of_nat m - 1 - Z.of_nat (S p) - 1).
                 assert (z_prime <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
                 destruct (H11 z_prime H14).
                 assert (z <= z_prime < z + Z.of_nat m) by lia.
                 apply H15 in H17.
                 contradiction.
              ** set (z_prime := z + Z.of_nat m - 1 - Z.of_nat (S p) - 1) in *.
                 destruct (z_prime =? z) eqn:Heq2.
                 +++ apply Z.eqb_eq in Heq2.
                     rewrite Heq2 in H13.
                     apply H13.
                     destruct p.
                     1: rewrite Nat.add_0_r.
                     2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                     all: exact H0.
                 +++ apply Z.eqb_neq in Heq2.
                     assert (z < z_prime <= z + Z.of_nat m) by lia.
                     assert (z_prime <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
                     destruct (H11 z_prime H15) as [H16 H17].
                     apply (H17 H14); exact H12.
        ++ intros H13 H14.
           apply delta_delta_n_comm in H14.
           apply in_bounce_l in H14.
           assert (z_prime + 1 <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
           destruct (H11 (z_prime + 1) H15) as [H16 H17].
           destruct H14 as [H14 | [[H14 H18] | [H14 H18]]].
           -- destruct (H3 (z_prime + 1)) as [H19 [H20 H21]].
              assert (z < z_prime + 1 <= z + Z.of_nat m) by lia.
              destruct (H20 H18).
              apply (H23 p); exact H14.
           -- destruct (z_prime + 1 =? z + Z.of_nat m) eqn:Heq.
              ** apply Z.eqb_eq in Heq.
                 apply H18.
                 destruct p.
                 1: rewrite Nat.add_0_r.
                 2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                 all: rewrite Heq; exact H1.
              ** assert (z <= z_prime + 1 < z + Z.of_nat m) by lia.
                 apply (H16 H19).
                 exact H14.
           -- assert (z < z_prime + 1 <= z + Z.of_nat m) by lia.
              apply (H17 H19).
              exact H14.
        ++ intros H13 H14.
           apply delta_delta_n_comm in H14.
           apply in_bounce_r in H14.
           destruct (z_prime - 1 =? z + Z.of_nat m - 1 - Z.of_nat p) eqn:Heq.
           -- apply Z.eqb_eq in Heq.
              assert (z < z_prime - 1 < z + Z.of_nat m) by lia.
              destruct (H3 (z_prime - 1)) as [H16 [H17 H18]].
              destruct H14 as [[H14 H19] | [H14 H19]].
              ** apply (H18 H15 p); exact H19.
              ** destruct H10.
                 +++ apply H10; rewrite <- Heq; exact H14.
                 +++ lia.
           -- apply Z.eqb_neq in Heq.
              destruct (H11 (z_prime - 1) Heq) as [H15 H16].
              destruct H14 as [[H14 H19] | [H14 H19]].
              ** assert (z <= z_prime - 1 < z + Z.of_nat m) by lia.
                 apply (H15 H17); exact H14.
              ** destruct (z_prime - 1 =? z) eqn:Heq2.
                 +++ apply Z.eqb_eq in Heq2.
                     apply H19.
                     rewrite Heq2.
                     destruct p.
                     1: rewrite Nat.add_0_r.
                     2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                     all: exact H0.
                 +++ assert (z < z_prime - 1 <= z + Z.of_nat m) by lia.
                     apply (H16 H17).
                     exact H14.
      * intro; exfalso; lia.
    - destruct (Nat.ltb_spec p m).
      * split.
        ++ intro; exfalso; lia.
        ++ assert (0 <= p < m)%nat by lia.
           destruct (H4 H8) as [H9 [H10 H11]].
           repeat split.
           -- left; intro.
              apply delta_delta_n_comm in H13.
              apply in_bounce_l in H13.
              replace (z + Z.of_nat (S p) - Z.of_nat m + 1 + 1) with (z + 2) in H13 by lia.
              destruct H13 as [H13 | [[H13 H14] | [H13 H14]]].
              ** assert (z < z+2 <= z + Z.of_nat m) by lia.
                 destruct (H3 (z+2)) as [H15 [H16 H17]].
                 destruct (H16 H14).
                 apply (H19 p).
                 exact H13.
              ** destruct (z+2 =? z + Z.of_nat m) eqn:Heq.
                 +++ apply Z.eqb_eq in Heq.
                     rewrite Heq in H14.
                     apply H14.
                     destruct p.
                     1: rewrite Nat.add_0_r.
                     2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                     all: exact H1.
                 +++ assert (z+2 <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
                     assert (z <= z+2 < z + Z.of_nat m) by lia.
                     destruct (H11 (z+2) H15).
                     apply (H17 H16).
                     exact H13.
              ** assert (z+2 <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
                 assert (z < z+2 <= z + Z.of_nat m) by lia.
                 destruct (H11 (z+2) H15).
                 apply (H18 H16).
                 exact H13.
           -- apply delta_delta_n_comm.
              apply in_bounce_r.
              left; split.
              ** replace (z + Z.of_nat (S p) - Z.of_nat m + 1 - 1) with (z + Z.of_nat m - 1 - Z.of_nat p) by lia.
                 exact H9.
              ** replace  (z + Z.of_nat (S p) - Z.of_nat m + 1 - 1) with z by lia.
                 destruct p.
                 1: rewrite Nat.add_0_r.
                 2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                 all: exact H0.
           -- intros H14 H15.
              apply delta_delta_n_comm in H15.
              apply in_bounce_l in H15.
              destruct H15 as [H15 | [[H15 H16] | [H15 H16]]].
              ** assert (z < z_prime + 1 <= z + Z.of_nat m) by lia.
                 destruct (H3 (z_prime + 1)) as [H17 [H18 H19]].
                 destruct (H18 H16).
                 apply (H21 p).
                 exact H15.
              ** destruct (z_prime + 1 =? z + Z.of_nat m) eqn:Heq.
                 +++ apply Z.eqb_eq in Heq.
                     rewrite Heq in H16.
                     apply H16.
                     destruct p.
                     1: rewrite Nat.add_0_r.
                     2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                     all: exact H1.
                 +++ assert (z_prime + 1 <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
                     assert (z <= z_prime + 1 < z + Z.of_nat m) by lia.
                     destruct (H11 (z_prime+1) H17).
                     apply (H19 H18).
                     exact H15.
              ** assert (z_prime + 1 <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
                 assert (z < z_prime + 1 <= z + Z.of_nat m) by lia.
                 destruct (H11 (z_prime + 1) H17).
                 apply (H20 H18).
                 exact H15.
           -- intros H14 H15.
              apply delta_delta_n_comm in H15.
              apply in_bounce_r in H15.
              assert (z_prime - 1 <> z + Z.of_nat m - 1 - Z.of_nat p) by lia.
              destruct (H11 (z_prime - 1) H16).
              destruct H15 as [[H15 H19] | [H15 H19]].
              ** assert (z <= z_prime - 1 < z + Z.of_nat m) by lia.
                 apply (H17 H20); exact H15.
              ** assert (z < z_prime - 1 <= z + Z.of_nat m) by lia.
                 apply (H18 H20).
                 exact H15.
      * split.
        ++ intro; exfalso; lia.
        ++ intro.
           assert (m <= p < 2*m)%nat by lia.
           destruct (H5 H9) as [H10 [H11 H12]].
           repeat split.
           -- destruct (z + Z.of_nat (S p) - Z.of_nat m + 1 =? z + Z.of_nat m) eqn: Heq.
              ** right; apply Z.eqb_eq in Heq; exact Heq.
              ** left; intro.
                 apply delta_delta_n_comm in H13.
                 apply in_bounce_l in H13.
                 apply Z.eqb_neq in Heq.
                 set (z_prime := z + Z.of_nat (S p) - Z.of_nat m + 1 + 1) in *.
                 assert (z_prime <> z + Z.of_nat p - Z.of_nat m + 1) by lia.
                 destruct H13 as [H13 | [[H13 H15] | [H13 H15]]].
                 +++ assert (z < z_prime <= z + Z.of_nat m) by lia.
                     destruct (H3 z_prime) as [H16 [H17 H18]].
                     destruct (H17 H15).
                     apply (H20 p); exact H13.
                 +++ destruct (z_prime =? z + Z.of_nat m) eqn:Heq2.
                     --- apply Z.eqb_eq in Heq2.
                         rewrite Heq2 in H15.
                         apply H15.
                         destruct p.
                         1: rewrite Nat.add_0_r.
                         2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                         all: exact H1.
                     --- assert (z <= z_prime < z + Z.of_nat m) by lia.
                         destruct (H12 z_prime H14).
                         apply (H17 H16); exact H13.
                 +++ assert (z < z_prime <= z + Z.of_nat m) by lia.
                     destruct (H12 z_prime H14).
                     apply (H18 H16); exact H13.
           -- apply delta_delta_n_comm.
              apply in_bounce_r.
              right; split.
              ** replace (z + Z.of_nat (S p) - Z.of_nat m + 1 - 1) with (z + Z.of_nat p - Z.of_nat m + 1) by lia.
                 exact H11.
              ** intro.
                 assert (z < z + Z.of_nat (S p) - Z.of_nat m + 1 - 1 < z + Z.of_nat m) by lia.
                 destruct (H3 (z + Z.of_nat (S p) - Z.of_nat m + 1 - 1)) as [H15 [H16 H17]].
                 apply (H17 H14 p H13).
           -- intros H14 H15.
              apply delta_delta_n_comm in H15.
              apply in_bounce_l in H15.
              destruct H15 as [H15 | [[H15 H16] | [H15 H16]]].
              ** assert (z < z_prime + 1 <= z + Z.of_nat m) by lia.
                 destruct (H3 (z_prime + 1)) as [H17 [H18 H19]].
                 destruct (H18 H16).
                 apply (H21 p H15).
              ** destruct (z_prime + 1 =?z + Z.of_nat p - Z.of_nat m + 1) eqn:Heq.
                 +++ apply Z.eqb_eq in Heq.
                     assert (z + Z.of_nat p - Z.of_nat m + 1 <> z + Z.of_nat m) by lia.
                     destruct H10.
                     --- rewrite Heq in H15.
                         exact (H10 H15).
                     --- contradiction.
                 +++ destruct (z_prime + 1 =? z + Z.of_nat m) eqn:Heq2.
                     --- apply Z.eqb_eq in Heq2.
                         rewrite Heq2 in H16.
                         apply H16.
                         destruct p.
                         1: rewrite Nat.add_0_r.
                         2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                         all: exact H1.
                     --- assert (z <= z_prime + 1 < z + Z.of_nat m) by lia.
                         apply Z.eqb_neq in Heq.
                         destruct (H12 (z_prime + 1) Heq).
                         exact (H18 H17 H15).
              ** destruct (z_prime + 1 =?z + Z.of_nat p - Z.of_nat m + 1) eqn:Heq.
                 +++ apply Z.eqb_eq in Heq.
                     assert (z < z_prime + 1 < z + Z.of_nat m) by lia.
                     destruct (H3 (z_prime + 1)) as [H18 [H19 H20]].
                     apply (H20 H17 p H16).
                 +++ assert (z < z_prime + 1 <= z + Z.of_nat m) by lia.
                     apply Z.eqb_neq in Heq.
                     destruct (H12 (z_prime + 1) Heq).
                     apply (H19 H17 H15).
           -- intros H14 H15.
              apply delta_delta_n_comm in H15.
              apply in_bounce_r in H15.
              destruct H15 as [[H15 H16] | [H15 H16]].
              ** assert (z_prime - 1 <> z + Z.of_nat p - Z.of_nat m + 1) by lia.
                 assert (z <= z_prime - 1 < z + Z.of_nat m) by lia.
                 destruct (H12 (z_prime - 1) H17).
                 apply (H19 H18 H15).
              ** assert (z_prime - 1 <> z + Z.of_nat p - Z.of_nat m + 1) by lia.
                 destruct (z_prime - 1 =? z) eqn:Heq.
                 +++ apply Z.eqb_eq in Heq.
                     rewrite Heq in H16.
                     apply H16.
                     destruct p.
                     1: rewrite Nat.add_0_r.
                     2: replace (Nat.add n (S p)) with (S (n+p)) by lia; apply in_wall_m; left.
                     all: exact H0.
                 +++ assert (z < z_prime - 1 <= z + Z.of_nat m) by lia.
                     destruct (H12 (z_prime - 1) H17).
                     apply (H20 H18 H15).
Qed.

Lemma bounce_l_between_walls (c : config) (z : Z) (n m : nat) :
  (m > 1)%nat ->
  In wall (delta_n regles c n z) /\
  In wall (delta_n regles c n (z+Z.of_nat m)) /\
  In bounce_l (delta_n regles c n (z+Z.of_nat m-1)) /\ 
  (forall z_prime, 
    ((z <= z_prime < z+Z.of_nat m - 1) -> ~(In bounce_l (delta_n regles c n z_prime))) /\
    ((z < z_prime <= z+Z.of_nat m) -> 
      ~(In bounce_r (delta_n regles c n z_prime)) /\ (forall p, ~(In gen (delta_n regles c (n+p) z_prime)))
    ) /\
    ((z < z_prime < z+Z.of_nat m) -> forall p, ~(In wall (delta_n regles c (n+p) z_prime)))
  )
  -> 
  (forall q p, 
    ((0 <= p < m)%nat -> (
      In bounce_l (delta_n regles c (n+q*2*m+p) (z + Z.of_nat m - 1 - Z.of_nat p)) /\
      (~(In bounce_r (delta_n regles c (n+q*2*m+p) (z + Z.of_nat m - 1 - Z.of_nat p)))
       \/ (z + Z.of_nat m - 1 - Z.of_nat p = z)) /\
      (forall z_prime, (z_prime <> (z + Z.of_nat m - 1 - Z.of_nat p)) ->
        ((z <= z_prime < z+Z.of_nat m) -> ~(In bounce_l (delta_n regles c (n+q*2*m+p) z_prime))) /\
        ((z < z_prime <= z+Z.of_nat m) -> ~(In bounce_r (delta_n regles c (n+q*2*m+p) z_prime)))
      )
    )) /\
    ((m <= p < 2*m)%nat -> (
      (~(In bounce_l (delta_n regles c (n+q*2*m+p) (z + Z.of_nat p - Z.of_nat m + 1)))
       \/ (z + Z.of_nat p - Z.of_nat m + 1 = z + Z.of_nat m)) /\
      In bounce_r (delta_n regles c (n+q*2*m+p) (z + Z.of_nat p - Z.of_nat m + 1)) /\
      (forall z_prime, (z_prime <> (z + Z.of_nat p - Z.of_nat m + 1)) ->
        ((z <= z_prime < z+Z.of_nat m) -> ~(In bounce_l (delta_n regles c (n+q*2*m+p) z_prime))) /\
        ((z < z_prime <= z+Z.of_nat m) -> ~(In bounce_r (delta_n regles c (n+q*2*m+p) z_prime)))
      ))
    )
  ).
Proof.
  intros H H0.
  induction q.
  + intro.
    replace (Nat.add (n + 0 * 2 * m) p) with (Nat.add n p) by lia.
    apply (bounce_l_between_walls_aux c z n m H H0 p).
  + assert (
    In wall (delta_n regles c (n + S q * 2 * m) z) /\
    In wall (delta_n regles c (n + S q * 2 * m) (z + Z.of_nat m)) /\
    In bounce_l (delta_n regles c (n + S q * 2 * m) (z + Z.of_nat m - 1)) /\
    (forall z_prime : Z,
     (z <= z_prime < z + Z.of_nat m - 1 -> ~ In bounce_l (delta_n regles c (n + S q * 2 * m) z_prime)) /\
     (z < z_prime <= z + Z.of_nat m ->
      ~ In bounce_r (delta_n regles c (n + S q * 2 * m) z_prime) /\
      (forall p : nat, ~ In gen (delta_n regles c (n + S q * 2 * m + p) z_prime))) /\
     (z < z_prime < z + Z.of_nat m ->
      forall p : nat, ~ In wall (delta_n regles c (n + S q * 2 * m + p) z_prime)))
    ).
    - destruct (IHq (Nat.sub (2*m) 1)).
      assert (m <= 2*m-1 < 2 * m)% nat by lia.
      destruct (H2 H3) as [H4 [H5 H6]].
      repeat split.
      1,2: replace (Nat.add n (S q * 2 * m)) with (S (n + (S q * 2 * m - 1))) by lia.
      1,2: apply in_wall_m; left.
      all: destruct H0 as [H01 [H02 [H03 H04]]].
      3-5: replace (Nat.add n (S q * 2 * m)) with (S (n + q * 2 * m + (2 * m - 1))) by lia.
      3-5: cbn [delta_n].
      * exact H01.
      * exact H02.
      * apply delta_delta_n_comm.
        apply in_bounce_l.
        right; right; split.
        ++ replace (z + Z.of_nat (2 * m - 1) - Z.of_nat m + 1) with (z + Z.of_nat m - 1 + 1) in H5 by lia.
           exact H5.
        ++ replace (z + Z.of_nat m - 1 + 1) with (z + Z.of_nat m) by lia.
           replace (Nat.add (n + q * 2 * m) (2 * m - 1)) with (S (n + (q * 2 * m + (2 * m - 1) - 1))) by lia.
           apply in_wall_m.
           left; exact H02.
      * intros H0 H7.
        apply delta_delta_n_comm in H7.
        apply in_bounce_l in H7.
        assert (z <= z_prime + 1 < z + Z.of_nat m) by lia.
        assert (z < z_prime + 1 <= z + Z.of_nat m) by lia.
        assert (z_prime + 1 <> z + Z.of_nat (2 * m - 1) - Z.of_nat m + 1) by lia.
        destruct (H6 (z_prime + 1) H10) as [H11 H12]. 
        destruct H7 as [H7 | [[H7 H13] | [H7 H13]]].
        ++ destruct (H04 (z_prime + 1)) as [H05 [H06 H07]].
           destruct (H06 H9).
           apply (H14 (Nat.add (q * 2 * m) (2 * m - 1))).
           rewrite Nat.add_assoc; exact H7.
        ++ apply (H11 H8); exact H7.
        ++ apply (H12 H9); exact H7.
      * intro.
        apply delta_delta_n_comm in H0.
        apply in_bounce_r in H0.
        assert (z_prime - 1 <> z + Z.of_nat (2 * m - 1) - Z.of_nat m + 1) by lia.
        destruct (H6 (z_prime - 1) H8) as [H9 H10]. 
        destruct H0 as [[H11 H12] | [H11 H12]].
        ++ assert (z <= z_prime - 1 < z + Z.of_nat m) by lia.
           apply (H9 H0 H11).
        ++ destruct (z_prime - 1 =? z) eqn:Heq.
           -- apply Z.eqb_eq in Heq.
              rewrite Heq in H12.
              replace (Nat.add (n + q * 2 * m) (2 * m - 1)) with (S (n + (q * 2 * m + (2 * m - 1)-1))) in H12 by lia.
              apply H12.
              apply in_wall_m.
              left; exact H01.
           -- assert (z < z_prime - 1 <= z + Z.of_nat m) by lia.
              apply (H10 H0 H11).
      * intro.
        destruct (H04 z_prime) as [H05 [H06 H07]].
        destruct (H06 H7).
        rewrite <- Nat.add_assoc.
        exact (H8 (Nat.add (S q * 2 * m) p)).
      * intros.
        destruct (H04 z_prime) as [H05 [H06 H07]].
        rewrite <- Nat.add_assoc.
        exact (H07 H0 (Nat.add (S q * 2 * m) p)).
    - apply bounce_l_between_walls_aux.
      ++ exact H.
      ++ exact H1.
Qed.

Lemma no_bounce_l_before_gen_aux (c : config) (z : Z) (n : nat) :
  In wall (delta_n regles c n z) /\
  (forall z_prime, 
    ((z < z_prime) -> 
       ~(In gen (delta_n regles c n z_prime)) /\
       ~(In bounce_r (delta_n regles c n z_prime))) /\
    ((z <= z_prime) ->  
        ~(In bounce_l (delta_n regles c n z_prime)))
  )
  -> 
   (forall z_prime, 
    ((z < z_prime) -> 
       ~(In bounce_r (delta_n regles c (S n) z_prime))) /\
    ((z <= z_prime) ->  
        ~(In bounce_l (delta_n regles c (S n) z_prime)))
  ).
Proof.
  intros.
  cbn [delta_n].
  destruct H.
  split.
  all: intros H1 H2; apply delta_delta_n_comm in H2.
  + apply in_bounce_r in H2.
    destruct (H0 (z_prime - 1)).
    destruct H2 as [[H5 H6] | [H5 H6]].
    - assert (z <= z_prime - 1) by lia.
      apply (H4 H2 H5).
    - destruct (z =? z_prime - 1) eqn:Heq.
      * apply Z.eqb_eq in Heq.
        rewrite <- Heq in H6.
        apply (H6 H).
      * assert (z < z_prime - 1) by lia.
        destruct (H3 H2).
        apply (H8 H5).
  + apply in_bounce_l in H2.
    assert (z < z_prime + 1) by lia.
    assert (z <= z_prime + 1) by lia.
    destruct (H0 (z_prime + 1)).
    destruct (H5 H3) as [H7 H8].
    destruct H2 as [H9 | [[H9 H10] | [H9 H10]]].
    - apply (H7 H9).
    - apply (H6 H4 H9).
    - apply (H8 H9).
Qed.

Lemma no_bounce_l_before_gen (c : config) (z : Z) (n m: nat) :
  In wall (delta_n regles c n z) /\
  (forall z_prime, 
    ((z < z_prime) -> 
       (forall p, (p < m)%nat -> ~(In gen (delta_n regles c (n+p) z_prime))) /\
       ~(In bounce_r (delta_n regles c n z_prime))) /\
    ((z <= z_prime) ->  
        ~(In bounce_l (delta_n regles c n z_prime)))
  )
  -> 
   (forall z_prime, 
    ((z < z_prime) -> 
       ~(In bounce_r (delta_n regles c (n+m) z_prime))) /\
    ((z <= z_prime) ->  
        ~(In bounce_l (delta_n regles c (n+m) z_prime)))
  ).
Proof.
  induction m.
  + intros.
    rewrite Nat.add_0_r.
    destruct H.
    destruct (H0 z_prime).
    assert (z < z_prime -> ~ In bounce_r (delta_n regles c n z_prime)).
    - intro.
      destruct (H1 H3).
      exact H5.
    - exact (conj H3 H2).
  + intros.
    destruct H.
    assert (
    In wall (delta_n regles c n z) /\
    (forall z_prime : Z,
      (z < z_prime ->
      (forall p : nat, (p < m)%nat -> ~ In gen (delta_n regles c (n+p) z_prime)) /\
      ~ In bounce_r (delta_n regles c n z_prime)) /\
    (z <= z_prime -> ~ In bounce_l (delta_n regles c n z_prime)))).
    - repeat split.
      2-4: destruct (H0 z_prime0) as [H2 H3].
      2,3: destruct (H2 H1) as [H4 H5].
      * exact H.
      * intros.
        assert (p < S m)%nat by lia.
        exact (H4 p H7).
      * exact H5.
      * exact H3. 
    - assert (In wall (delta_n regles c (n+m) z) /\
        (forall z_prime, 
          ((z < z_prime) -> 
             ~(In gen (delta_n regles c (n+m) z_prime)) /\
             ~(In bounce_r (delta_n regles c (n+m) z_prime))) /\
          ((z <= z_prime) ->  
              ~(In bounce_l (delta_n regles c (n+m) z_prime)))
        )).
      * repeat split.
        3,4: destruct (IHm H1 z_prime0) as [H3 H4].
        ++ destruct m.
           1: rewrite Nat.add_0_r.
           2: replace (Nat.add n (S m)) with (S (n+m)) by lia; apply in_wall_m; left.
           all: exact H.
        ++ assert (m < S m)%nat by lia.
           destruct (H0 (z_prime0)).
           destruct (H4 H2).
           apply (H6 m H3).
        ++ exact (H3 H2).
        ++ intro H5; exact (H4 H5).
      * replace (Nat.add n (S m)) with (S (n+m)) by lia.
        apply (no_bounce_l_before_gen_aux c z (n+m) H2 z_prime).
Qed. 

Lemma no_bounce_l_before_gen_fischer_aux_1_1 m m_prime :
  (m >= m_prime)%nat ->
  (2 * m * m - sum_nat m >= 2 * m_prime * m_prime - sum_nat m_prime)%nat.
Proof.
  induction m.
  + lia.
  + intro.
    destruct (S m =? m_prime)%nat eqn:Heq.
    - apply Nat.eqb_eq in Heq.
      rewrite Heq.
      lia.
    - apply Nat.eqb_neq in Heq.
      assert (m >= m_prime)%nat by lia.
      apply IHm in H0.
      rewrite position_gen_aux_2.
      lia. 
Qed.

Lemma no_bounce_l_before_gen_fischer_aux_1 m m_prime :
  (2 * m * m - sum_nat m < 2 * m_prime * m_prime - sum_nat m_prime)%nat ->
  (m < m_prime)%nat.
Proof.
  intro.
  destruct (Nat.lt_ge_cases m m_prime) as [H1 | H1].
  + exact H1.
  + apply no_bounce_l_before_gen_fischer_aux_1_1 in H1.
    exfalso; lia.
Qed.

Lemma no_bounce_l_before_gen_fischer_aux_2 m m_prime :
  (m < m_prime)%nat ->
  (2 * m * m - sum_nat m < 2 * m_prime * m_prime - sum_nat m_prime)%nat.
Proof.
  induction m_prime.
  + lia.
  + intro.
    destruct (m =? m_prime)%nat eqn:Heq.
    - apply Nat.eqb_eq in Heq.
      rewrite Heq.
      rewrite position_gen_aux_2.
      lia.
    - apply Nat.eqb_neq in Heq.
      assert (m < m_prime)%nat by lia.
      apply IHm_prime in H0.
      rewrite position_gen_aux_2.
      lia. 
Qed.

Lemma no_bounce_l_bounce_r_before_gen_fischer :
  forall m, (m > 0)%nat -> 
    forall n z_prime, (2*m*m-(sum_nat m) < n <= 2*(m+1)*(m+1)-(sum_nat (m+1)))%nat -> 
      ((Z.of_nat (sum_nat m) - 1 <= z_prime) ->
        ~(In bounce_l (delta_n regles config_0 n z_prime))) /\
      ((Z.of_nat (sum_nat m) - 1 < z_prime) ->
        ~(In bounce_r (delta_n regles config_0 n z_prime))).
Proof.
  destruct m.
  + intro; inversion H.
  + induction m.
    - intros.
      simpl in H0.
      destruct H0.
      destruct n as [| [| [| [| [| [ | ]]]]]].
      1,7: exfalso; lia.
      * destruct description_config_1 as [H2 [H3 [H4 [H5 [H6 H7]]]]]. 
        destruct (H7 z_prime) as [H9 [H10 [H11 [H12 [H13 [H14 [H15 [H16 H17]]]]]]]].
        split.
        all: intro.
        ++ exact H17.
        ++ exact H16.
      * destruct description_config_2 as [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]. 
        destruct (H8 z_prime) as [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]]].
        split.
        all: intro.
        ++ exact H18.
        ++ exact H17.
      * destruct description_config_3 as [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]. 
        destruct (H8 z_prime) as [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]]].
        split.
        all: intro.
        ++ exact H18.
        ++ exact H17.
      * destruct description_config_4 as [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]. 
        destruct (H9 z_prime) as [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]]].
        split.
        all: intro.
        ++ exact H18.
        ++ exact H17.
      * destruct description_config_5 as [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]. 
        destruct (H9 z_prime) as [H10 [H11 [H12 [H13 [H14 [H15 [H16 [H17 H18]]]]]]]].
        split.
        all: intro.
        ++ exact H18.
        ++ exact H17.
    - intros.
      set (z := Z.of_nat (sum_nat (S (S m))) - 1).
      set (n_prime := Nat.add (2 * S (S m) * S (S m) - sum_nat (S (S m))) 1).
      set (p := Nat.sub n n_prime).
      assert( In wall (delta_n regles config_0 n_prime z) /\
        (forall z_prime, 
          ((z < z_prime) -> 
             (forall p_prime, (p_prime < p)%nat -> ~(In gen (delta_n regles config_0 (n_prime+p_prime) z_prime))) /\
             ~(In bounce_r (delta_n regles config_0 n_prime z_prime))) /\
          ((z <= z_prime) ->  
              ~(In bounce_l (delta_n regles config_0 n_prime z_prime)))
        )
      ).
      * repeat split.
        ++ apply condition_wall.
           left; exists (S (S m)).
           repeat split.
           all: lia.
        ++ intros p_prime H2 H3.
           replace (S (S m) + 1)%nat with (S (S (S m))) in H0 by lia.
           assert (2 * (S (S m)) * (S (S m)) - sum_nat (S (S m)) < n_prime + p_prime < 2 * (S (S (S m))) * (S (S (S m))) - sum_nat (S (S (S m))))%nat by lia.
           apply condition_gen in H3.
           destruct H3 as [m_prime [H5 [H6 H7]]].
           assert (m_prime > (S (S m)))%nat.
           -- destruct H4.
              rewrite H6 in H3.
              apply (no_bounce_l_before_gen_fischer_aux_1 (S (S m)) m_prime H3).
           -- assert (m_prime < S (S (S m)))%nat.
              ** destruct H4.
                 rewrite H6 in H8.
                 apply (no_bounce_l_before_gen_fischer_aux_1 m_prime (S (S (S m))) H8).
              ** lia.
        ++ replace n_prime with (S (2 * S (S m) * S (S m) - sum_nat (S (S m)))) by lia.
           replace (S m + 1)%nat with (S (S m)) in IHm by lia.
           assert (S m > 0)%nat by lia.
           assert (2 * S m * S m - sum_nat (S m) < 2 * S (S m) * S (S m) - sum_nat (S (S m)) <= 2 * S (S m) * S (S m) - sum_nat (S (S m)))%nat.
           -- split.
              ** repeat rewrite position_gen_aux_2. lia.
              ** lia.
           -- assert (Z.of_nat (sum_nat (S m)) - 1 <= z_prime0 - 1).
              ** simpl sum_nat in *. lia.
              ** cbn [delta_n]; intro.
                 apply delta_delta_n_comm in H5.
                 apply in_bounce_r in H5.
                 destruct (IHm H2 (2 * S (S m) * S (S m) - sum_nat (S (S m)))%nat (z_prime0 - 1) H3) as [H6 H7].
                 destruct H5 as [[H8 H9] | [H8 H9]].
                 +++ apply (H6 H4 H8). 
                 +++ destruct (Z.of_nat (sum_nat (S m)) - 1 =? z_prime0 - 1) eqn:Heq.
                     --- apply Z.eqb_eq in Heq.
                         apply H9.
                         apply condition_wall.
                         destruct m.
                         *** right.
                             split.
                             ++++ lia.
                             ++++ simpl in Heq.
                                  rewrite Heq.
                                  reflexivity.
                         *** left; exists (S (S m)).
                             repeat split.
                             ++++ lia.
                             ++++ rewrite position_gen_aux_2.
                                  lia.
                             ++++ exact Heq.
                     --- assert (Z.of_nat (sum_nat (S m)) - 1 < z_prime0 - 1) by lia.
                         apply (H7 H5 H8).
        ++ intro.
           replace n_prime with (S (2 * S (S m) * S (S m) - sum_nat (S (S m)))) by lia.
           replace (S m + 1)%nat with (S (S m)) in IHm by lia.
           assert (S m > 0)%nat by lia.
           assert (2 * S m * S m - sum_nat (S m) < 2 * S (S m) * S (S m) - sum_nat (S (S m)) <= 2 * S (S m) * S (S m) - sum_nat (S (S m)))%nat.
           -- split.
              ** repeat rewrite position_gen_aux_2. lia.
              ** lia.
           -- assert (Z.of_nat (sum_nat (S m)) - 1 < z_prime0 + 1).
              ** simpl sum_nat in *. lia.
              ** assert (Z.of_nat (sum_nat (S m)) - 1 <= z_prime0 + 1) by lia.
                 cbn [delta_n]; intro.
                 apply delta_delta_n_comm in H6.
                 apply in_bounce_l in H6.
                 destruct H6.
                 +++ apply condition_gen in H6.
                     destruct H6 as [m0 [H6 [H7 H8]]].
                     destruct (Nat.lt_ge_cases (S (S m)) m0).
                     --- apply no_bounce_l_before_gen_fischer_aux_2 in H9.
                         lia.
                     --- destruct (Nat.lt_ge_cases m0 (S (S m))).
                         *** apply no_bounce_l_before_gen_fischer_aux_2 in H10.
                             lia.
                         *** assert (S (S m) = m0)%nat by lia.
                             unfold z in H1.
                             rewrite H11 in *.
                             assert (Z.of_nat (sum_nat m0) - 1 < z_prime0 + 1) by lia.
                             lia.
                 +++ destruct (IHm H2 (2 * S (S m) * S (S m) - sum_nat (S (S m)))%nat (z_prime0 + 1) H3) as [H7 H8].
                     destruct H6 as [[H9 H10] | [H9 H10]].
                     --- apply (H7 H5 H9). 
                     --- apply (H8 H4 H9). 
      * destruct (no_bounce_l_before_gen config_0 z n_prime p H1 z_prime) as [H2 H3].
        replace n with (n_prime + p)%nat by lia.
        exact (conj H3 H2).
Qed.

Lemma no_bounce_l_before_gen_fischer :
  forall m, (m > 0)%nat -> 
    forall n z_prime, (2*m*m-(sum_nat m) < n <= 2*(m+1)*(m+1)-(sum_nat (m+1)))%nat /\ (Z.of_nat (sum_nat m) - 1 <= z_prime) ->
      ~(In bounce_l (delta_n regles config_0 n z_prime)).
Proof.
  intros.
  pose proof no_bounce_l_bounce_r_before_gen_fischer.
  destruct H0.
  destruct (H1 m H n z_prime H0) as [H3 H4].
  exact (H3 H2).
Qed.

Lemma no_bounce_r_before_gen_fischer :
  forall m, (m > 0)%nat -> 
    forall n z_prime, (2*m*m-(sum_nat m) < n <= 2*(m+1)*(m+1)-(sum_nat (m+1)))%nat /\ (Z.of_nat (sum_nat m) - 1 < z_prime) ->
      ~(In bounce_r (delta_n regles config_0 n z_prime)).
Proof.
  intros.
  pose proof no_bounce_l_bounce_r_before_gen_fischer.
  destruct H0.
  destruct (H1 m H n z_prime H0) as [H3 H4].
  exact (H4 H2).
Qed.

Lemma sum_nat_mono (m1 m2 : nat) :
  (m1 <= m2)%nat -> (sum_nat m1 <= sum_nat m2)%nat.
Proof.
  intro.
  induction m2.
  - assert (m1 = 0)%nat by lia.
    rewrite H0; reflexivity.
  - destruct (m1 =? S m2)%nat eqn:Heq.
    * apply Nat.eqb_eq in Heq.
      rewrite Heq.
      reflexivity.
    * apply Nat.eqb_neq in Heq.
      assert (m1 <= m2)%nat by lia.
      apply IHm2 in H0.
      assert (sum_nat m2 <= sum_nat (S m2))%nat.
      + simpl; lia.
      + lia.
Qed.

Lemma sum_nat_strict_mono (m1 m2 : nat) :
  (m1 < m2)%nat -> (sum_nat m1 < sum_nat m2)%nat.
Proof.
  induction m2.
  - intro; lia.
  - intro.
    destruct (Nat.eq_dec m1 m2).
    + rewrite e. 
      simpl; lia.
    + assert (m1 < m2)%nat by lia.
      apply IHm2 in H0. 
      simpl; lia.
Qed.

Lemma sum_nat_injective (m1 m2 : nat) :
  sum_nat m1 = sum_nat m2 -> m1 = m2.
Proof.
  intro.
  destruct (Nat.lt_ge_cases m1 m2).
  - apply sum_nat_strict_mono in H0.
    exfalso; lia.
  - destruct (Nat.eq_dec m1 m2).
    + exact e.
    + assert (m2 < m1)%nat by lia.
      apply sum_nat_strict_mono in H1.
      exfalso; lia.
Qed.

Lemma no_bounce_l_before_gen_fischer_2 :
  forall m, (m > 1)%nat -> 
    forall n z_prime, (n <= 2*m*m-(sum_nat m))%nat /\ (Z.of_nat (sum_nat (m-1)) - 1 <= z_prime <= Z.of_nat (sum_nat m) - 1) ->
      ~(In bounce_l (delta_n regles config_0 n z_prime)).
Proof.
  intros.
  destruct n.
  + pose proof description_config_0.
    destruct H1 as [H2 [H3 H4]].
    destruct (H4 z_prime) as [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]]]].
    simpl; exact H15.
  + destruct n.
    - pose proof description_config_1.
      destruct H1 as [H2 [H3 [H4 [H5 [H6 H7]]]]].
      destruct (H7 z_prime) as [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]].
      exact H16.
    - assert (S (S n) > 1)%nat by lia.
      destruct (usefull_bounding (S (S n)) H1) as [m_prime [H2 H3]].
      destruct H0.
      assert (2 * (m_prime - 1) * (m_prime - 1) - sum_nat (m_prime - 1) <  2 * m * m - sum_nat m)%nat by lia.
      apply no_bounce_l_before_gen_fischer_aux_1 in H5.
      assert (m_prime - 1 <= m - 1)%nat by lia.
      apply sum_nat_mono in H6.
      assert (Z.of_nat (sum_nat (m_prime - 1)) - 1 <= z_prime) by lia.
      assert (m_prime - 1 > 0)%nat by lia.
      replace m_prime with (m_prime - 1 + 1)%nat in H3 by lia.
      replace (m_prime - 1 + 1 -1)%nat with (m_prime - 1)%nat in H3 by lia.
      apply (no_bounce_l_before_gen_fischer (m_prime - 1) H8 (S (S n)) z_prime (conj H3 H7)).
Qed.

Lemma no_bounce_r_before_gen_fischer_2 :
  forall m, (m > 1)%nat -> 
    forall n z_prime, (n <= 2*m*m-(sum_nat m))%nat /\ (Z.of_nat (sum_nat (m-1)) - 1 < z_prime <= Z.of_nat (sum_nat m) - 1) ->
      ~(In bounce_r (delta_n regles config_0 n z_prime)).
Proof.
  intros.
  destruct n.
  + pose proof description_config_0.
    destruct H1 as [H2 [H3 H4]].
    destruct (H4 z_prime) as [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]]]].
    simpl; exact H14.
  + destruct n.
    - pose proof description_config_1.
      destruct H1 as [H2 [H3 [H4 [H5 [H6 H7]]]]].
      destruct (H7 z_prime) as [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]].
      exact H15.
    - assert (S (S n) > 1)%nat by lia.
      destruct (usefull_bounding (S (S n)) H1) as [m_prime [H2 H3]].
      destruct H0.
      assert (2 * (m_prime - 1) * (m_prime - 1) - sum_nat (m_prime - 1) <  2 * m * m - sum_nat m)%nat by lia.
      apply no_bounce_l_before_gen_fischer_aux_1 in H5.
      assert (m_prime - 1 <= m - 1)%nat by lia.
      apply sum_nat_mono in H6.
      assert (Z.of_nat (sum_nat (m_prime - 1)) - 1 < z_prime) by lia.
      assert (m_prime - 1 > 0)%nat by lia.
      replace m_prime with (m_prime - 1 + 1)%nat in H3 by lia.
      replace (m_prime - 1 + 1 -1)%nat with (m_prime - 1)%nat in H3 by lia.
      apply (no_bounce_r_before_gen_fischer (m_prime - 1) H8 (S (S n)) z_prime (conj H3 H7)).
Qed.

Lemma usefull_bounding_2 (n : nat) :
  exists m, (m > 1)%nat /\ (Z.of_nat (sum_nat (m-1)) - 1 <= Z.of_nat n < Z.of_nat (sum_nat m) - 1).
Proof.
  induction n.
  + exists 2%nat.
    simpl; lia.
  + destruct IHn as [m [H1 H2]].
    destruct (Z.of_nat (S n) =? Z.of_nat (sum_nat m) - 1) eqn:Heq.
    - exists (S m).
      apply Z.eqb_eq in Heq.
      rewrite Heq.
      simpl.
      replace (m - 0)%nat with m by lia.
      lia.
    - exists m.
      apply Z.eqb_neq in Heq.
      lia.
Qed.

Lemma condition_bounce_l_aux_1 (m1 m2 : nat) :
  (2 * m1 * m1 - sum_nat m1 = 2 * m2 * m2 - sum_nat m2)%nat -> (m1 = m2)%nat.
Proof.
  intro.
  destruct (Nat.ltb_spec m1 m2).
  + apply no_bounce_l_before_gen_fischer_aux_2 in H0.
    exfalso; lia.
  + destruct (Nat.ltb_spec m2 m1).
    - apply no_bounce_l_before_gen_fischer_aux_2 in H1.
      exfalso; lia.
    - lia.
Qed.

Lemma condition_bounce_l_aux (n m p n_min : nat) (z_min : Z) :
  (p > 1)%nat /\
  Z.of_nat (sum_nat (p - 1)) - 1 <= Z.of_nat m < Z.of_nat (sum_nat p) - 1 /\
  (2 * p * p - sum_nat p < n)%nat /\
  n_min = S (2 * p * p - sum_nat p) /\
  z_min = Z.of_nat (sum_nat (p - 1)) - 1
  ->
  In wall (delta_n regles config_0 n_min z_min) /\
  In wall (delta_n regles config_0 n_min (z_min+Z.of_nat p)) /\
  In bounce_l (delta_n regles config_0 n_min (z_min+Z.of_nat p-1)) /\ 
  (forall z_prime, 
    ((z_min <= z_prime < z_min+Z.of_nat p - 1) -> ~(In bounce_l (delta_n regles config_0 n_min z_prime))) /\
    ((z_min < z_prime <= z_min+Z.of_nat p) -> 
        ~(In bounce_r (delta_n regles config_0 n_min z_prime)) /\ (forall p_prime, ~(In gen (delta_n regles config_0 (n_min+p_prime) z_prime)))
    ) /\
    ((z_min < z_prime < z_min+Z.of_nat p) -> forall p_prime, ~(In wall (delta_n regles config_0 (n_min+p_prime) z_prime)))
  ).
Proof.
  intro.
  destruct H as [H1 [H2 [H3 [H4 H5]]]].
  repeat split.
  + apply condition_wall.
    destruct (p =? 2)%nat eqn:Heq.
    - apply Nat.eqb_eq in Heq.
      right; rewrite H4; rewrite H5.
      rewrite Heq.
      simpl.
      lia.
    - apply Nat.eqb_neq in Heq.
      assert (p - 1 > 1)% nat by lia.
      left; exists (p - 1)%nat.
      repeat split.
      * exact H.
      * assert (p >= p-1)%nat by lia.
        apply no_bounce_l_before_gen_fischer_aux_1_1 in H0.
        lia.
      * symmetry in H5; exact H5.
  + apply condition_wall.
    left; exists p.
    repeat split.
    - exact H1.
    - lia.
    - replace p with (S (p - 1)) by lia.
      simpl sum_nat.
      lia.
  + rewrite H4.  
    cbn [delta_n].
    apply delta_delta_n_comm.
    apply in_bounce_l.
    left.
    apply condition_gen.
    exists p.
    repeat split.
    - exact H1.
    - replace p with (S (p - 1)) by lia.
      simpl sum_nat.
      lia.
  + intros H6 H7.
    rewrite H4 in H7.  
    cbn [delta_n] in H7.
    apply delta_delta_n_comm in H7.
    apply in_bounce_l in H7.
    destruct H7 as [H7 | [[H7 H8] | [H7 H8]]].
    - apply condition_gen in H7.
      destruct H7 as [m_prime [H7 [H8 H9]]].
      apply condition_bounce_l_aux_1 in H8.
      rewrite <- H8 in H9.
      replace p with (S (p - 1)) in H9 by lia.
      simpl sum_nat in H9.
      lia.
    - assert (Z.of_nat (sum_nat (p-1)) - 1 <= z_prime + 1 <= Z.of_nat (sum_nat p) - 1).
      * replace p with (S (p - 1)) by lia.
        simpl sum_nat.
        replace (p - 1 - 0)%nat with (p-1)%nat by lia.
        lia.
      * assert (2 * p * p - sum_nat p <= 2 * p * p - sum_nat p)%nat by lia. 
        apply (no_bounce_l_before_gen_fischer_2 p H1 (2 * p * p - sum_nat p) (z_prime + 1) (conj H0 H) H7).
    - apply condition_wall in H8.
      destruct H8 as [[m_prime [H8 [H9 H10]]] | [H8 H9]].
      * assert (sum_nat m_prime >= sum_nat (p-1))%nat by lia.
        apply no_bounce_l_before_gen_fischer_aux_1 in H9.
        assert (m_prime <= p - 1)%nat by lia.
        apply sum_nat_mono in H0.
        assert (sum_nat m_prime = sum_nat (p - 1))%nat by lia.
        apply sum_nat_injective in H11.
        rewrite H11 in *.
        exfalso; lia.
      * rewrite H5 in H6.
        replace (p - 1)%nat with (S (p - 2)) in H6 by lia.
        simpl in H6.
        lia.
  + intro.
    rewrite H4 in H0.  
    cbn [delta_n] in H0.
    apply delta_delta_n_comm in H0.
    apply in_bounce_r in H0.
    destruct H0 as [[H6 H7] | [H6 H7]].
    - assert (Z.of_nat (sum_nat (p-1)) - 1 <= z_prime - 1 <= Z.of_nat (sum_nat p) - 1).
      * replace p with (S (p - 1)) by lia.
        simpl sum_nat.
        replace (p - 1 - 0)%nat with (p-1)%nat by lia.
        lia.
      * assert (2 * p * p - sum_nat p <= 2 * p * p - sum_nat p)%nat by lia. 
        apply (no_bounce_l_before_gen_fischer_2 p H1 (2 * p * p - sum_nat p) (z_prime - 1) (conj H8 H0) H6).
    - destruct (z_prime - 1 =? z_min) eqn:Heq.
      * apply Z.eqb_eq in Heq.
        rewrite Heq in *.
        apply H7.
        apply condition_wall.
        destruct (p =? 2)%nat eqn:Heq2.
        ++ apply Nat.eqb_eq in Heq2.
           right; rewrite H5.
           rewrite Heq2.
           simpl.
           lia.
        ++ apply Nat.eqb_neq in Heq2.
           assert (p - 1 > 1)% nat by lia.
           left; exists (p - 1)%nat.
           repeat split.
           -- exact H0.
           -- assert (p - 1 < p)%nat by lia.
                apply no_bounce_l_before_gen_fischer_aux_2 in H8.
                lia.
           -- rewrite H5; reflexivity.
      * rewrite Z.eqb_neq in Heq.
        assert (Z.of_nat (sum_nat (p-1)) - 1 < z_prime - 1 <= Z.of_nat (sum_nat p) - 1).
        ++ replace p with (S (p - 1)) by lia.
           simpl sum_nat.
           replace (p - 1 - 0)%nat with (p-1)%nat by lia.
           lia.
        ++ assert (2 * p * p - sum_nat p <= 2 * p * p - sum_nat p)%nat by lia. 
           apply (no_bounce_r_before_gen_fischer_2 p H1 (2 * p * p - sum_nat p) (z_prime - 1) (conj H8 H0) H6).
  + intros p_prime H6.
    apply condition_gen in H6.
    destruct H6 as [m_prime [H6 [H7 H8]]].
    assert (Z.of_nat (sum_nat (p-1)) < Z.of_nat (sum_nat m_prime)) by lia.
    assert (z_min + Z.of_nat p = Z.of_nat (sum_nat p) - 1).
    - replace p with (S (p - 1)) by lia.
      simpl sum_nat.
      lia.
    - destruct (Z.of_nat (sum_nat m_prime) =? Z.of_nat (sum_nat p)) eqn:Heq.
      * apply Z.eqb_eq in Heq.
        assert (sum_nat m_prime = sum_nat p)%nat by lia.
        apply sum_nat_injective in H10.
        rewrite H10 in *.
        lia.
      * apply Z.eqb_neq in Heq.
        assert (Z.of_nat (sum_nat m_prime) < Z.of_nat (sum_nat p)) by lia.
        destruct (Nat.lt_ge_cases (p-1) m_prime).
        ++ destruct (Nat.lt_ge_cases m_prime p).
           -- lia.
           -- apply sum_nat_mono in H12; lia.
        ++ apply sum_nat_mono in H11; lia.
  + intros H6 p_prime H7.
    apply condition_wall in H7.
    destruct H7 as [[m_prime [H7 [H8 H9]]] | [H7 H8]].
    - assert (z_min + Z.of_nat p = Z.of_nat (sum_nat p) - 1).
      * replace p with (S (p - 1)) by lia.
        simpl; lia.
      * assert (sum_nat (p - 1) < sum_nat m_prime)%nat by lia.
        assert (sum_nat m_prime < sum_nat p)%nat by lia.
        destruct (Nat.lt_ge_cases (p-1) m_prime).
        ++ destruct (Nat.lt_ge_cases m_prime p).
           -- lia.
           -- apply sum_nat_mono in H12; lia.
        ++ apply sum_nat_mono in H11; lia.
    - rewrite H5 in H6.
      replace (p-1)%nat with (S (p - 2)) in H6 by lia.
      simpl in H6; lia.
Qed.

Lemma condition_bounce_l (n m : nat) : 
  In bounce_l (delta_n regles config_0 n (Z.of_nat m)) <-> 
  exists p, (p > 1)%nat /\ 
    (Z.of_nat (sum_nat (p - 1)) - 1 <= Z.of_nat m < Z.of_nat (sum_nat p) - 1) /\
    (exists q, (n = 2*p*p - sum_nat p + q*2*p + sum_nat p - 1 - m)%nat).
Proof.
  split.
  + intro.
    destruct (usefull_bounding_2 m) as [p H0].
    exists p.
    destruct H0.
    split.
    - exact H0.
    - split.
      * exact H1.
      * destruct (Nat.ltb_spec (2*p*p-(sum_nat p)) n).
        ++ pose (n_min := S (2 * p * p - sum_nat p )).
           pose (z_min := Z.of_nat (sum_nat (p - 1)) - 1).
           assert (n_min = S (2 * p * p - sum_nat p )) as H_n_min by reflexivity. 
           assert (z_min = Z.of_nat (sum_nat (p - 1)) - 1) as H_z_min by reflexivity.
           specialize (condition_bounce_l_aux n m p n_min z_min (conj H0 (conj H1 (conj H2 (conj H_n_min H_z_min))))) as H3.
           specialize (bounce_l_between_walls config_0 z_min n_min p H0 H3) as H4.
           pose (q := ((n-n_min)/(2*p))%nat).
           pose (r := ((n-n_min) mod (2*p))%nat).
           assert ((n-n_min) = 2 * p * q + r)%nat by (subst q r; apply Nat.div_mod; lia).
           assert (r < 2 * p)%nat by (subst r; apply Nat.mod_upper_bound; lia).
           destruct (H4 q r) as [H7 H8].
           destruct (Nat.lt_ge_cases r p).
           -- assert (0 <= r < p)%nat by lia.
              destruct (H7 H10) as [H11 [H12 H13]].
              destruct (Z.of_nat m =? z_min + Z.of_nat p - 1 - Z.of_nat r) eqn:Heq.
              ** apply Z.eqb_eq in Heq.
                 assert (z_min + Z.of_nat p = Z.of_nat (sum_nat p) - 1).
                 +++ unfold z_min.
                     replace p with (S (p-1)) by lia.
                     replace (S (p - 1) - 1)%nat with (p - 1)%nat by lia.
                     simpl; lia.
                 +++ assert (m = sum_nat p - 2 - r)%nat by lia.
                     exists q.
                     lia.
              ** apply Z.eqb_neq in Heq.
                 destruct (H13 (Z.of_nat m) Heq).
                 assert (z_min + Z.of_nat p = Z.of_nat (sum_nat p) - 1).
                 +++ unfold z_min.
                     replace p with (S (p-1)) by lia.
                     replace (S (p - 1) - 1)%nat with (p - 1)%nat by lia.
                     simpl; lia.
                 +++ rewrite H16 in H14.
                     exfalso; apply (H14 H1).
                     replace (n_min + q * 2 * p + r)%nat with n by lia.
                     exact H.
           -- exfalso.
              assert (p <= r < 2 * p)%nat by lia.
              destruct (H8 H10) as [H11 [H12 H13]].
              destruct (Z.of_nat m =? z_min + Z.of_nat r - Z.of_nat p + 1) eqn:Heq.
              ** apply Z.eqb_eq in Heq.
                 destruct H11.
                 +++ replace (n_min + q * 2 * p + r)%nat with n in H11 by lia.
                     rewrite <- Heq in H11.
                     apply (H11 H).
                 +++ assert (z_min + Z.of_nat p = Z.of_nat (sum_nat p) - 1).
                     --- unfold z_min.
                         replace p with (S (p-1)) by lia.
                         replace (S (p - 1) - 1)%nat with (p - 1)%nat by lia.
                         simpl; lia.
                     --- lia.
              ** apply Z.eqb_neq in Heq.
                 destruct (H13 (Z.of_nat m) Heq).
                 assert (z_min + Z.of_nat p = Z.of_nat (sum_nat p) - 1).
                 +++ unfold z_min.
                     replace p with (S (p-1)) by lia.
                     replace (S (p - 1) - 1)%nat with (p - 1)%nat by lia.
                     simpl; lia.
                 +++ rewrite H16 in H14.
                     replace (n_min + q * 2 * p + r)%nat with n in H14 by lia.
                     apply (H14 H1 H).
        ++ exfalso.
           assert (Z.of_nat (sum_nat (p - 1)) - 1 <= Z.of_nat m <= Z.of_nat (sum_nat p) - 1) by lia.
           apply (no_bounce_l_before_gen_fischer_2 p H0 n (Z.of_nat m) (conj H2 H3) H).
  + intro.
    destruct H as [p [H [H1 [q H2]]]].
    pose (n_min := S (2 * p * p - sum_nat p )).
    pose (z_min := Z.of_nat (sum_nat (p - 1)) - 1).
    assert (n_min = S (2 * p * p - sum_nat p )) as H_n_min by reflexivity. 
    assert (z_min = Z.of_nat (sum_nat (p - 1)) - 1) as H_z_min by reflexivity.
    assert (2 * p * p - sum_nat p < n)%nat by lia.
    specialize (condition_bounce_l_aux n m p n_min z_min (conj H (conj H1 (conj H0 (conj H_n_min H_z_min))))) as H3.
    specialize (bounce_l_between_walls config_0 z_min n_min p H H3) as H4.
    assert (n = n_min + q*2*p + (sum_nat p - m - 2))%nat by lia.
    replace (Z.of_nat (sum_nat (p - 1)) - 1) with (Z.of_nat (sum_nat p - p) - 1) in H1.
    - assert (0 <= sum_nat p - m - 2 < p)%nat by lia.
      destruct (H4 q  (sum_nat p - m - 2)%nat).
      destruct (H7 H6).
      rewrite <- H5 in H9.
      assert (z_min + Z.of_nat p = Z.of_nat (sum_nat p) - 1).
      * unfold z_min.
        replace p with (S (p-1)) by lia.
        replace (S (p - 1) - 1)%nat with (p - 1)%nat by lia.
        simpl; lia.
      * replace (z_min + Z.of_nat p - 1 - Z.of_nat (sum_nat p - m - 2)) with  (Z.of_nat m) in H9 by lia.
        exact H9.
    - replace p with (S (p - 1)) by lia.
      simpl.
      replace (p - 1 - 0)%nat with (p - 1)%nat by lia.
      lia.
Qed.

Lemma propagation_composite (c : config) (z : Z) (n m : nat) :
  In composite (delta_n regles c n z) -> In composite (delta_n regles c (n+m) (z - Z.of_nat m)).
Proof.
  intro.
  induction m.
  + replace (n+0)%nat with n by lia.
    replace (z - Z.of_nat 0) with z by lia.
    exact H.
  + replace (n + S m)%nat with (S (n+m)) by lia.
    cbn [delta_n].
    apply delta_delta_n_comm.
    apply in_composite.
    right; left. 
    replace (z - Z.of_nat (S m) + 1) with (z - Z.of_nat m) by lia.
    exact IHm.
Qed.
 
Lemma condition_composite (c : config) (n : nat) :
  forall z,
  In composite (delta_n regles c n z) <->
  (exists m, (0 < m <= n)%nat /\
    ((In init_1 (delta_n regles c (n-m) (z + Z.of_nat m - 1))) \/
    (In bounce_l (delta_n regles c (n-m) (z + Z.of_nat m))))) \/
  (In composite (c (z + Z.of_nat n))).
Proof.
  induction n.
  + split.
    - simpl.
      intro.
      rewrite Z.add_0_r.
      right; exact H.
    - intro.
      destruct H as [[m [H1 H2]] | H].
      * exfalso; lia.
      * simpl in *.
        rewrite Z.add_0_r in H; exact H.
  + split.
    - intro.
      cbn [delta_n] in H.
      apply delta_delta_n_comm in H.
      apply in_composite in H.
      destruct H as [H | [H | H]].
      1,3: left; exists 1%nat; replace (S n - 1)%nat with n by lia.
      * split.
        ++ lia.
        ++ left; replace (z + Z.of_nat 1 - 1) with z by lia; exact H.
      * split.
        ++ lia.
        ++ right; replace (z + Z.of_nat 1) with (z + 1) by lia; exact H.
      * apply (IHn (z + 1)) in H.
        destruct H as [[m [H1 [H2 | H2]]] | H].
        ++ left; exists (m + 1)%nat.
           split.
           -- lia.
           -- replace (z + Z.of_nat (m + 1) - 1) with (z + 1 + Z.of_nat m - 1) by lia.
              replace (S n - (m+1))%nat with (n - m)%nat by lia.
              left; exact H2.
        ++ left; exists (m + 1)%nat.
           split.
           -- lia.
           -- replace (z + Z.of_nat (m + 1)) with (z + 1 + Z.of_nat m) by lia.
              replace (S n - (m+1))%nat with (n - m)%nat by lia.
              right; exact H2.
        ++ right; replace (z + Z.of_nat (S n)) with (z + 1 + Z.of_nat n) by lia; exact H.
    - intro.
      destruct H as [[m [H1 [H2 | H2]]] | H].
      1,2: assert (In composite (delta_n regles c (S (S n - m)) (z + Z.of_nat m - 1))).
      1,3: cbn [delta_n]; apply delta_delta_n_comm; apply in_composite.
      ++ left; exact H2.
      ++ right; right; replace (z + Z.of_nat m - 1 + 1) with (z + Z.of_nat m) by lia; exact H2.
      ++ replace z with (z + Z.of_nat (m - 1) - Z.of_nat (m - 1)) by lia.
         replace (S n) with (S n - (m - 1) + (m - 1))%nat by lia.
         apply propagation_composite.
         replace (S n - (m - 1))%nat with (S (S n - m)) by lia.
         replace (z + Z.of_nat (m - 1)) with (z + Z.of_nat m - 1) by lia.
         exact H.
      ++ replace z with (z + Z.of_nat (m - 1) - Z.of_nat (m - 1)) by lia.
         replace (S n) with (S n - (m - 1) + (m - 1))%nat by lia.
         apply propagation_composite.
         replace (S n - (m - 1))%nat with (S (S n - m)) by lia.
         replace (z + Z.of_nat (m - 1)) with (z + Z.of_nat m - 1) by lia.
         exact H.
      ++ replace z with (z + Z.of_nat (S n) - Z.of_nat (S n)) by lia.
         replace (S n) with (0 + S n)%nat by lia.
         apply propagation_composite.
         cbn [delta_n].
         replace (z + Z.of_nat (0 + S n)) with (z + Z.of_nat (S n)) by lia.
         exact H.
Qed.

Lemma correction_fischer (n : nat) :
  In composite (delta_n regles config_0 n 0) <->
  (exists m q, (m > 1)%nat /\ (q >= m)%nat /\ (n = 2*q*m - 1)%nat) \/ (n = 1)%nat.
Proof.
  split.
  + intro.
    apply condition_composite in H.
    destruct H as [[m [H [H1 | H1]]] | H].
    - destruct (n =? m)%nat eqn:Heq.
      * apply Nat.eqb_eq in Heq.
        rewrite Heq in *.
        replace (m-m)%nat with 0%nat in H1 by lia.
        simpl in H1.
        destruct description_config_0 as [H2 [H3 H4]].
        destruct (Z.of_nat m - 1 =? 0) eqn:Heq2.
        ++ right; lia.
        ++ apply Z.eqb_neq in Heq2.
           exfalso; apply (H3 (Z.of_nat m - 1) Heq2 H1).
      * apply Nat.eqb_neq in Heq.
        replace (n-m)%nat with (S (n - m - 1)) in H1 by lia.
        cbn [delta_n] in H1.
        apply delta_delta_n_comm in H1.
        apply in_init_1 in H1.
        inversion H1.
    - replace (0 + Z.of_nat m) with (Z.of_nat m) by lia.
      apply condition_bounce_l in H1.
      destruct H1 as [p [H1 [H2 [q H3]]]].
      pose proof (sum_nat_inf_square p).
      assert (n = 2 * (p + q) * p - 1)%nat by lia.
      left; exists p; exists (p + q)%nat.
      lia.
    - destruct description_config_0 as [H2 [H3 H4]].
      destruct (H4 (0 + Z.of_nat n)) as [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]]]].
      exfalso; apply (H16 H).
  + intro.
    destruct H as [[m [q [H1 [H2 H3]]]] | H].
    - apply condition_composite.
      left; exists (sum_nat (m - 1))%nat.
      split.
      * split.
        ++ replace (m - 1)%nat with (S (m - 2)) by lia.
           simpl; lia.
        ++ assert (n >= (m-1)*(m-1) - 1)%nat by nia.
           pose proof (sum_nat_inf_square (m-1)).
           nia.
      * right.
        apply condition_bounce_l.
        exists m.
        repeat split.
        ++ exact H1.  
        ++ lia.
        ++ replace m with (S (m-1)) by lia.
           replace (S (m - 1) - 1)%nat with (m - 1)%nat by lia.
           simpl.
           lia.
        ++ exists (q - m)%nat.
           pose proof (sum_nat_inf_square m).
           nia.
    - destruct description_config_1 as [H1 [H2 [H3 [H4 H5]]]].
      rewrite H; exact H4.
Qed.
  







