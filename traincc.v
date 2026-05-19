Require Import String.
Require Import List.
Include ListNotations.
Require Import Bool.
Include BoolNotations.

(* on définit le langage logique *)
Inductive prop :=
| Atom (s:string)
| Imp (p1 p2: prop)
| And (p1 p2: prop)
| Not (p:prop).

(* la comparaison de formules est décidable
   on pourra écrire: if (prop_dec p1 p2) then ... else ... *)
Lemma prop_dec: forall (p1 p2: prop), {p1=p2}+{p1<>p2}.
Proof.
  decide equality.
  apply string_dec.
Defined.

(* négation avec simplification pour éviter Not (Not p) *)
Definition neg p :=
  match p with
  | Not p => p
  | p => Not p
  end.

(* représentation de la formule p&q => q&p *)
Definition exemple := Imp (And (Atom "p") (Atom "q")) (And (Atom "q") (Atom "p")).

(* on manipulera des buts qui sont des couples (liste d'hypothèses, conclusion) *)
Definition goal: Type := list prop * prop.

(* les règles de preuve de la logique des propositions *)
Inductive isTrue: list prop -> prop -> Prop :=
| pHYP: forall h c, In c h -> isTrue h c
| pAnd_i: forall h p q, isTrue h p -> isTrue h q -> isTrue h (And p q)
| pAnd_e1: forall h p q, isTrue h (And p q) -> isTrue h p
| pAnd_e2: forall h p q, isTrue h (And p q) -> isTrue h q
| pImp_i: forall h p q, isTrue (p::h) q -> isTrue h (Imp p q)
| pImp_e: forall h p q, In p h -> isTrue h (Imp p q) -> isTrue h q
| pContra: forall h p q, isTrue (neg q::h) p -> isTrue (neg q::h) (Not p) -> isTrue h q.

(* on démontre que la formule donnée en exemple est prouvable *)
(* TODO 2pts *)
Lemma isTrue_ex: isTrue [] exemple.
Proof.
Admitted.

(* on introduit maintenant le type des arbres de preuve. *)
Inductive proof :=
| HYP
| And_i (pr1 pr2: proof)
| And_e1 (q: prop) (pr: proof)
| And_e2 (p: prop) (pr: proof)
| Imp_i (pr: proof)
| Imp_e (p: prop) (pr: proof)
| Contra (p: prop) (pr1 pr2: proof).

(* renvoie true si pr est un arbre de preuve pour h |- c *)
Check List.In_dec.
Fixpoint check pr h c :=
  match pr, c with
  | HYP, _ => if List.In_dec prop_dec c h then true else false
  | And_i pr1 pr2, And p1 p2 => check pr1 h p1 && check pr2 h p2
  | And_e1 q pr, p => check pr h (And p q)
  | And_e2 p pr, q => check pr h (And p q)
  | Imp_i pr, Imp p q => check pr (p::h) q
  | Imp_e p pr, q => if List.In_dec prop_dec p h then check pr h (Imp p q) else false
  | Contra p pr1 pr2, q => check pr1 (neg q::h) p && check pr2 (neg q::h) (Not p)
  | _, _ => false
  end.

(* TODO 3 pts *)
Lemma isTrue_check: forall h c, isTrue h c -> exists pr, check pr h c = true.
Proof.
Admitted.

(* TODO 3 pts *)
Lemma check_isTrue: forall pr h c, check pr h c = true -> isTrue h c.
Proof.
Admitted.

(* exemples d'arbres de preuve *)
Definition prf1 :=
  Imp_i (And_i (And_e2 (Atom "p") HYP)
               (And_e1 (Atom "q") HYP)).

Definition prf2 :=
  Imp_i (And_i
        (And_e1 (Atom "p")
           (And_i (And_e2 (Atom "p") HYP)
                  (And_e1 (Atom "q") HYP)))
        (And_e1 (Atom "q") HYP)).

(* TODO 0,5pts *)
Lemma check1: check prf1 [] exemple = true.
Proof.
Admitted.

(* TODO 0,5pts *)
Lemma check2: check prf2 [] exemple = true.
Proof.
Admitted.

(* TODO 5pts *)
Lemma check_mono: forall pr h1 h2 c, (forall p, In p h1 -> In p h2) -> check pr h1 c = true -> check pr h2 c = true.
Proof.
Admitted.

(* TODO 1.5pts *)
Lemma isTrue_mono: forall h1 c, isTrue h1 c -> forall h2, (forall p, In p h1 -> In p h2) -> isTrue h2 c.
Proof.
Admitted.

(* on s'intéresse maintenant à la simplification de preuves *)
Fixpoint apply (s: proof->proof) pr :=
  s (match pr with
     | HYP => HYP
     | And_i pr1 pr2 => And_i (apply s pr1) (apply s pr2)
     | And_e1 q pr => And_e1 q (apply s pr)
     | And_e2 p pr => And_e2 p (apply s pr)
     | Imp_i pr => Imp_i (apply s pr)
     | Imp_e p pr => Imp_e p (apply s pr)
     | Contra p pr1 pr2 => Contra p (apply s pr1) (apply s pr2)
     end).

Fixpoint apply_all (l: list (proof->proof)) pr :=
  match l with
  | [] => pr
  | s::l => apply_all l (apply s pr)
  end.

Definition correct (s:proof->proof) := forall pr h c, check pr h c = true -> check (s pr) h c = true.

Lemma apply_ok: forall s, correct s -> correct (apply s).
Proof.
Admitted.

(* TODO 1pt *)
Lemma apply_all_ok: forall l, (forall s, In s l -> correct s) -> correct (apply_all l).
Proof.
Admitted.

(* quelques simplifications basiques *)
Definition simpl_And_e1 pr :=
  match pr with
  | And_e1 _ (And_i pr1 pr2) => pr1
  | _ => pr
  end.

Definition simpl_And_e2 pr :=
  match pr with
  | And_e2 _ (And_i pr1 pr2) => pr2
  | _ => pr
  end.

Definition simpl_Imp_e pr :=
  match pr with
  | Imp_e _ (Imp_i pr) => pr
  | _ => pr
  end.

(* TODO 1,5pts *)
Lemma simpl_And_e1_ok: correct simpl_And_e1.
Proof.
Admitted.

(* TODO 1,5pts *)
Lemma simpl_And_e2_ok: correct simpl_And_e2.
Proof.
Admitted.