Require Import PeanoNat List Bool.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

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
   
Definition signal := nat.
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

(* ======== Définition de la satisfiabilité d'une formule ============
   La satifiabilité se définit comme pour les formules de la logique propositionnelle
   où les règles (s,k) s'interprètent dans une configuration c et à une position z
   comme "le signal s apparait à la position z+k de la configuration c"
*)
   
Fixpoint signal_sat_z (c : config) (z : Z) (phi : signal_form) : bool :=
  match phi with
  | f_true => true
  | f_false => false
  | f_atome (k,s) => existsb (fun x => Nat.eqb x s) (c (z+k))
  | f_and phi1 phi2 => (signal_sat_z c z phi1) && (signal_sat_z c z phi2)
  | f_or phi1 phi2 => (signal_sat_z c z phi1) || (signal_sat_z c z phi2)
  | f_not psi => negb (signal_sat_z c z psi)
  end.

(*========= delta: la fonction globale de l'automate ===========*)

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
  
(* definition alternative qui pourra peut être nous aider plus tard:
 -> finalement non, pas utilisée
Fixpoint delta_aux (rs : rules) (c_pred : config) (c : config) : config :=
  match rs with
    | [] => c
    | t::q => delta_aux q c_pred (delta_one_cell t c_pred c)
  end.
 
Definition delta (rs : rules) (c : config) : config :=
  delta_aux rs c empty_config.
  *)
 
(*======= transformation sur les formules ===========*)

(* décalage des indices *)
Fixpoint phi_k (phi : signal_form) (k : Z) : signal_form :=
  match phi with
  | f_true => f_true
  | f_false => f_false
  | f_atome (k2,s) => f_atome (k+k2,s)
  | f_and phi1 phi2 => f_and (phi_k phi1 k) (phi_k phi2 k) 
  | f_or phi1 phi2 => f_or (phi_k phi1 k) (phi_k phi2 k) 
  | f_not psi => f_not (phi_k psi k)
  end.

(* Une formule est satisfaite à la position z+k de la configuration
   ssi cette même formule dans laquelle les indices sont décalés de k 
       est satisfaite à la position z de la configuration c *)
Lemma sig_sat_phi_phi_k (c : config) (phi : signal_form) (k z : Z) : 
  signal_sat_z c (z+k) phi = signal_sat_z c z (phi_k phi k).
Proof.
  induction phi.
  4,5,6: simpl.
  4,5: rewrite IHphi1; rewrite IHphi2.
  6: rewrite IHphi.
  1,2,4,5,6: reflexivity.
  + unfold phi_k.
    destruct p as [k2 s].
    simpl.
    rewrite Z.add_assoc.
    reflexivity.
Qed.

(* Formules pour deux étapes:
  Pour toute règle donnant s on fait la formule en deux étapes 
  de cette règle en remplaçant les atomes (k,s) par la disjonstion
  de toutes les règles qui peuvent donner s décalées de k *)
Fixpoint new_atom (rs : rules) (s : signal) (k : Z) : signal_form :=
  match rs with
  | [] => f_false
  | (phi,s2)::q => if Nat.eqb s s2 then f_or (phi_k phi k) (new_atom q s k) 
                  else new_atom q s k
  end.

Fixpoint phi_2_steps (rs : rules) (phi : signal_form) : signal_form :=
  match phi with
  | f_true => f_true
  | f_false => f_false
  | f_atome (k,s) => new_atom rs s k
  | f_and phi1 phi2 => f_and (phi_2_steps rs phi1) (phi_2_steps rs phi2) 
  | f_or phi1 phi2 => f_or (phi_2_steps rs phi1) (phi_2_steps rs phi2) 
  | f_not psi => f_not (phi_2_steps rs psi)
  end.

(* On veut maintenant montrer que phi est satisfaite dans la position z 
   dans la configuration delta(c) ssi sa version en deux étapes est satisfaite
   dans la position k dans la configuration c (que la règle en 2 étapes fait
   bien ce qu'on souhaite) *)
   
(* Si une règle n'est pas vérifiée en z dans c alors elle n'a pas d'influence
   sur la liste delta(c)(z) *)
Lemma unverified_rule (rs : rules) (c : config) (phi : signal_form) (s : signal)  (z : Z) :
  signal_sat_z c z phi = false -> delta ((phi, s) :: rs) c z =  delta rs c z.
Proof.
  intros Hphi.
  simpl.
  rewrite Hphi.
  reflexivity.
Qed.

(* phi_2_step_correct est le lemme qui nous intéresse et les autres sont des 
   sous-résultats qui nous servent dans la démonstration *)
Lemma phi_2_steps_correct_1_1 (rs : rules) (c : config) (z k : Z) (s s_prime : signal) (psi: signal_form) :
  existsb (fun x => Nat.eqb x s) (delta ((psi, s_prime) :: rs) c (z + k)) = true 
  <-> (existsb (fun x => Nat.eqb x s) (delta rs c (z + k)) = true) \/ (signal_sat_z c (z + k) psi = true /\ Nat.eqb s s_prime = true).
Proof.
  split.
  + intro.
    destruct (signal_sat_z c (z + k) psi) eqn:Heq.
    - destruct (Nat.eqb s s_prime) eqn: Heq2.
      * right; split. 
        all:reflexivity.
      * left.
        simpl delta in H.
        rewrite Heq in H.
        simpl existsb in H.
        rewrite orb_true_iff in H.
        destruct H.
        -- rewrite Nat.eqb_eq in H.
           rewrite Nat.eqb_neq in Heq2.
           symmetry in H.
           contradiction.
        -- exact H. 
    - apply (unverified_rule rs c psi s_prime (z + k)) in Heq.
      rewrite Heq in H.
      left; exact H.
  + intro.
    destruct H.
    all: simpl delta.
    - destruct (signal_sat_z c (z + k) psi).
      all: simpl existsb.
      1: rewrite orb_true_iff; right.
      all: exact H.
    - destruct H.
      rewrite H.
      simpl existsb.
      rewrite orb_true_iff; left.
      rewrite Nat.eqb_eq.
      symmetry.
      rewrite Nat.eqb_eq in H0.
      exact H0.
Qed.

Lemma phi_2_steps_correct_1 (rs : rules) (c : config) (z k : Z) (s : signal) :
  existsb (fun x => Nat.eqb x s) (delta rs c (z + k)) = true <-> exists phi, (signal_sat_z c (z + k) phi = true /\ In (phi,s) rs).
Proof.
  split.
  + intro.
    induction rs.
    - inversion H.
    - destruct a as [psi s_prime].
      apply phi_2_steps_correct_1_1 in H.
      destruct H.
      * apply IHrs in H.
        destruct H as [phi H].
        destruct H.
        exists phi.
        split.
        -- exact H.
        -- simpl In.
           right; exact H0.
      * destruct H.
        exists psi.
        split.
        -- exact H.
        -- simpl In.
           left.
           rewrite Nat.eqb_eq in H0.
           rewrite H0.
           reflexivity.
  + intro.
    destruct H as [phi [H1 H2]].
    induction rs.
    - inversion H2.
    - destruct a as [psi s_prime].
      simpl In in H2.
      destruct H2.
      * simpl delta.
        inversion H.
        rewrite H1.
        simpl existsb.
        rewrite orb_true_iff.
        left; rewrite Nat.eqb_eq; reflexivity.
      * apply IHrs in H.
        simpl delta.
        destruct (signal_sat_z c (z + k) psi).
        -- simpl existsb.
           rewrite orb_true_iff.
           right; exact H.
        -- exact H.
Qed.

Lemma phi_2_steps_correct_2 (rs : rules) (c : config) (z k : Z) (s : signal) :
  (exists phi : signal_form, signal_sat_z c (z + k) phi = true /\ In (phi, s) rs)
  <-> signal_sat_z c z (new_atom rs s k) = true.
Proof.
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    induction rs.
    - inversion H2.
    - destruct a as [psi s_prime].
      destruct (Nat.eqb s s_prime) eqn:Heq.
      * simpl new_atom.
        rewrite Heq.
        simpl signal_sat_z.
        rewrite orb_true_iff.
        simpl In in H2.
        destruct H2.
        -- inversion H.
           left.
           rewrite sig_sat_phi_phi_k in H1.
           exact H1.
        -- right.
           apply IHrs in H.
           exact H.
      * simpl new_atom.
        rewrite Heq.
        simpl In in H2.
        destruct H2.
        -- rewrite Nat.eqb_neq in Heq.
           inversion H.
           rewrite H3 in Heq.
           contradiction.
        -- apply IHrs in H.
           exact H.
  + intro.
    induction rs.
    - simpl in H.
      inversion H.
    - destruct a as [psi s_prime].
      simpl new_atom in H.
      destruct (Nat.eqb s s_prime) eqn:Heq.
      * simpl signal_sat_z in H.
        rewrite orb_true_iff in H.
        destruct H.
        -- exists psi.
           split.
           ** rewrite sig_sat_phi_phi_k.
              exact H.
           ** rewrite Nat.eqb_eq in Heq.
              rewrite Heq.
              simpl In.
              left; reflexivity.
        -- apply IHrs in H.
           destruct H as [phi H].
           exists phi.
           destruct H.
           simpl In.
           split.
           ** exact H.
           ** right; exact H0.
      * apply IHrs in H.
        destruct H as [phi H].
        exists phi.
        destruct H.
        simpl In.
        split.
        -- exact H.
        -- right; exact H0.            
Qed.

Lemma phi_2_steps_correct (rs : rules) (c : config) (phi : signal_form) (z : Z) :
  signal_sat_z (delta rs c) z phi = true <-> signal_sat_z c z (phi_2_steps rs phi) = true.
Proof.
  induction phi.
  1,2,4,5,6: simpl.
  3:rewrite andb_true_iff.
  4:rewrite orb_true_iff.
  3,4: rewrite IHphi1; rewrite IHphi2.
  3:rewrite andb_true_iff.
  4:rewrite orb_true_iff.
  1,2,3,4: reflexivity.
  + apply not_iff_compat in IHphi.
    rewrite !not_true_iff_false in IHphi.
    rewrite !negb_true_iff.
    exact IHphi.
  + split.
    - simpl.
      destruct p as [k s].
      intro.
      apply phi_2_steps_correct_1 in H.
      apply phi_2_steps_correct_2 in H.
      exact H.
    - simpl.
      destruct p as [k s].
      intro.
      apply phi_2_steps_correct_1.
      apply phi_2_steps_correct_2.
      exact H.
Qed.

Lemma phi_2_steps_correct_v2 (rs : rules) (c : config) (phi : signal_form) (z : Z) :
  signal_sat_z (delta rs c) z phi = signal_sat_z c z (phi_2_steps rs phi).
Proof.
  case (signal_sat_z (delta rs c) z phi) eqn:H.
  + apply phi_2_steps_correct in H.
    symmetry in H.
    exact H.
  + pose proof (phi_2_steps_correct rs c phi z) as H2.
    apply not_iff_compat in H2.
    apply not_true_iff_false in H.
    apply H2 in H.
    apply not_true_iff_false in H.
    symmetry.
    exact H.
Qed.


(*========== règles pour un automate qui va 2 fois plus vite ===========*)

Fixpoint rules_2_steps (rs : rules) (rs_dec : rules) : rules :=
  match rs_dec with
  | [] => []
  | (phi,s)::q => (phi_2_steps rs phi,s)::(rules_2_steps rs q)
  end.
  
(* on n'a pas l'injectivité de phi_2_steps donc on a des résultats différents 
   dans chaque sens (mais ces résultats sont suffisants) *)
Lemma in_rules_2_steps_1 (rs1 : rules) (rs2 : rules) (phi : signal_form) (s : signal) : 
  In (phi, s) rs1 -> In (phi_2_steps rs2 phi, s) (rules_2_steps rs2 rs1).
Proof.
  intro.
  induction rs1.
  + simpl in H. 
    contradiction.
  + destruct a as (psi, s_prime).
    simpl in H.
    destruct H.
    - simpl.
      inversion H.
      left; reflexivity.
    - simpl.
      right.
      exact (IHrs1 H). 
Qed.

Lemma in_rules_2_steps_2 (rs1 : rules) (rs2 : rules) (phi : signal_form) (s : signal) : 
  In (phi, s) (rules_2_steps rs2 rs1) -> exists psi, In (psi, s) rs1 /\ phi = phi_2_steps rs2 psi.
Proof.
  intro.
  induction rs1.
  + simpl in H. 
    contradiction.
  + destruct a as (psi, s_prime).
    destruct H.
    - exists psi.
      inversion H.
      split.
      * simpl.
        left; reflexivity.
      * reflexivity.
    - apply IHrs1 in H.
      destruct H as [psi_2 [H1 H2]].
      exists psi_2.
      split.
      * simpl.
        right; exact H1.
      * exact H2. 
Qed.

(*========= et maintenant le résultat qui nous intéresse ===========
  On montre qu'un signal est dans delta(delta(c)) avec les règles classiques
  ssi il est dans delta(c) avec les règles qui font deux étapes en une*)

Lemma rules_2_steps_correct_aux (rs : rules) (c : config) (z : Z) (s : signal) :
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

Lemma rules_2_steps_correct (rs : rules) (c : config) (z : Z) (s : signal) :
  In s (delta rs (delta rs c) z) <-> In s (delta (rules_2_steps rs rs) c z).
Proof.
  rewrite (rules_2_steps_correct_aux (rules_2_steps rs rs) c z s).
  rewrite (rules_2_steps_correct_aux rs (delta rs c) z s).
  split.
  + intro.
    destruct H as [phi [H1 H2]].
    exists (phi_2_steps rs phi).
    split.
    - apply (phi_2_steps_correct rs c phi z).
      exact H1.
    - apply (in_rules_2_steps_1 rs rs phi s) in H2.
      exact H2.
  + intro.
    destruct H as [phi [H1 H2]].
    apply (in_rules_2_steps_2 rs rs phi s) in H2.
    destruct H2 as [psi [H2 H3]].
    exists psi.
    split.
    - apply (phi_2_steps_correct rs c psi z).
      rewrite H3 in H1.
      exact H1.
    - exact H2. 
Qed.


(* et maintenant pour k étapes d'un coup ( k = n+1 ) *)

Fixpoint rules_k_steps (rs : rules) (k : nat) : rules :=
  match k with
  | 0%nat => rs 
  | S m => rules_2_steps rs (rules_k_steps rs m)
  end.

Fixpoint delta_n (rs : rules) (c : config) (n : nat) :=
  match n with
  | 0%nat => c
  | S m => delta_n rs (delta rs c) m
  end.
  
Lemma rules_k_steps_correct_aux (rs : rules) (z : Z) (s : signal) (k : nat) :
  forall c, In s ((delta_n rs c (S k)) z) <-> exists phi, signal_sat_z c z phi = true /\ In (phi, s) (rules_k_steps rs k).
Proof.
  induction k.
  + intro.
    simpl. 
    apply rules_2_steps_correct_aux.
  + simpl.
    intro.
    specialize (IHk (delta rs c)).
    rewrite IHk.
    split.
    - intro.
      destruct H as [phi [H1 H2]].
      exists (phi_2_steps rs phi).
      split.
      * apply (phi_2_steps_correct rs c phi z).
        exact H1.
      * apply (in_rules_2_steps_1 (rules_k_steps rs k) rs phi s) in H2.
        exact H2.
    - intro.  
      destruct H as [phi [H1 H2]].
      apply (in_rules_2_steps_2 (rules_k_steps rs k) rs phi s) in H2.
      destruct H2 as [psi [H2 H3]].
      exists psi.
      split.
      * apply (phi_2_steps_correct rs c psi z).
        rewrite H3 in H1.
        exact H1.
      * exact H2.
Qed.

Lemma rules_k_steps_correct (rs : rules) (c : config) (z : Z) (s : signal) (k : nat) :
  In s (delta_n rs c (S k) z) <-> In s (delta (rules_k_steps rs k) c z).
Proof.
  rewrite rules_k_steps_correct_aux.
  rewrite (rules_2_steps_correct_aux (rules_k_steps rs k) c z s).
  reflexivity.
Qed.

