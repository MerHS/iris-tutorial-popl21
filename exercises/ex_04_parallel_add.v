(**
In this exercise we use the spin-lock from the previous exercise to implement
the running example during the lecture of the tutorial: proving that when two
threads increase a reference that's initially zero by two, the result is four.
*)
From iris.algebra Require Import excl_auth frac_auth numbers.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lib.par proofmode notation.
From exercises Require Import ex_03_spinlock.

(** The program as a heap-lang expression. We use the heap-lang [par] module for
parallel composition. *)
Definition parallel_add : expr :=
  let: "r" := ref #0 in
  ( FAA "r" #2 )
  |||
  ( FAA "r" #2 )
  ;;
  !"r".

(** 1st proof : we only prove that the return value is even.
No ghost state is involved in this proof. *)
Section proof1.
  Context `{!heapG Σ, !spawnG Σ}.

  Definition parallel_add_inv_1 (r : loc) : iProp Σ :=
    (∃ n : Z, r ↦ #n ∗ ⌜ Zeven n ⌝)%I.

  Definition evenN: namespace := nroot .@ "evenN".

  (** *Exercise*: finish the missing cases of this proof. *)
  Lemma parallel_add_spec_1 :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (inv_alloc nroot _ (parallel_add_inv_1 r) with "[Hr]") as "#Hinv".
    { iExists 0%Z. iNext. iFrame. }
    wp_smart_apply (wp_par (λ _, True%I) (λ _, True%I)).
    - iInv "Hinv" as (n) ">[Hr %]" "Hclose".
      wp_faa.
      iApply "Hclose".
      iExists (n + 2%Z)%Z.
      iNext; iFrame.
      iPureIntro.
      by apply Zeven_plus_Zeven.
    - iInv "Hinv" as (n) ">[Hr %]" "Hclose".
      wp_faa.
      iMod ("Hclose" with "[Hr]") as "_".
      {
        (* Re-establish invariant. *)
        iExists _.
        iFrame.
        iPureIntro.
        by apply Zeven_plus_Zeven.
      }
      done.
    - iIntros (v1 v2) "_".
      iNext.
      wp_seq.
      iInv "Hinv" as (rv) ">[Hr %]" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Hr]") as "_".
      { iNext. iExists rv. eauto with iFrame. }
      iModIntro.
      iApply "Post".
      auto.
  Qed.
End proof1.

(** 2nd proof : we prove that the program returns 4 exactly.
We need a piece of ghost state: integer ghost variables.

Whereas we previously abstracted over an arbitrary "ghost state" [Σ] in the
proofs, we now need to make sure that we can use integer ghost variables. For
this, we add the type class constraint:

  inG Σ (excl_authR ZO)

*)

Section proof2.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (excl_authR ZO)}.

  Definition parallel_add_inv_2 (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    (∃ n1 n2 : Z, r ↦ #(n1 + n2)
            ∗ own γ1 (●E n1) ∗ own γ2 (●E n2))%I.

  (** Some helping lemmas for ghost state that we need in the proof. In actual
  proofs we tend to inline simple lemmas like these, but they are here to
  make things easier to understand. *)
  Lemma ghost_var_alloc n :
    ⊢ |==> ∃ γ, own γ (●E n) ∗ own γ (◯E n).
  Proof.
    iMod (own_alloc (●E n ⋅ ◯E n)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ n m :
    own γ (●E n) -∗ own γ (◯E m) -∗ ⌜ n = m ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    (* iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?. *)
    (* iPureIntro. *)
    (* by apply excl_auth_agree_L. *)
    (* iApply (excl_auth_agree_L with "Hx"). *)
    by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ n' n m :
    own γ (●E n) -∗ own γ (◯E m) ==∗ own γ (●E n') ∗ own γ (◯E n').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E n' ⋅ ◯E n') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

  (** *Exercise*: finish the missing cases of the proof. *)
  Lemma parallel_add_spec_2 :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc 0) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hγ2● Hγ2◯]".
    iMod (inv_alloc nroot _ (parallel_add_inv_2 r γ1 γ2) with "[Hr Hγ1● Hγ2●]") as "#Hinv".
    {
      iNext.
      rewrite /parallel_add_inv_2.
      iExists _, _. iFrame.
    }
    wp_smart_apply (wp_par (λ _, own γ1 (◯E 2%Z)) (λ _, own γ2 (◯E 2%Z))
                with "[Hγ1◯] [Hγ2◯]").
    - iInv "Hinv" as (n1 n2) ">(Hr & Hγ1● & Hγ2●)" "Hclose".
      wp_faa.
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
      iMod (ghost_var_update γ1 2 with "Hγ1● Hγ1◯") as "[Hγ1● Hγ1◯]".
      iMod ("Hclose" with "[- Hγ1◯]"); [|by auto].
      iExists _, _. iFrame "Hγ1● Hγ2●". rewrite (_ : 2 + n2 = 0 + n2 + 2)%Z; [done|ring].
    - iInv "Hinv" as (n1 n2) ">(Hr & Hγ1● & Hγ2●)" "Hclose".
      wp_faa.
      iDestruct (ghost_var_agree with "Hγ2● Hγ2◯") as %->.
      iMod (ghost_var_update γ2 2 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]".
      iMod ("Hclose" with "[- Hγ2◯]"); [|by auto].
      iExists _, _. iFrame "Hγ1● Hγ2●". rewrite (_ : n1 + 2 = n1 + 0 + 2)%Z; [done|ring].
    - iIntros (v1 v2) "[Hγ1◯ Hγ2◯]".
      iNext. wp_seq.
      iInv "Hinv" as (n1 n2) ">(Hr & Hγ1● & Hγ2●)" "Hclose".
      iDestruct (ghost_var_agree with "Hγ1● Hγ1◯") as %->.
      iDestruct (ghost_var_agree with "Hγ2● Hγ2◯") as %->.
      wp_load.
      iMod ("Hclose" with "[- Post]").
      { iExists _, _. iFrame. }
      by iApply "Post".
  Qed.
End proof2.

(** 3rd proof (not shown in the talk) : we prove that the program returns 4
exactly, but using a fractional authoritative ghost state.  We need another kind
of ghost resource for this, but we only need one ghost variable no matter how
many threads there are. *)
Section proof3.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (frac_authR natR)}.

  Definition parallel_add_inv_3 (r : loc) (γ : gname) : iProp Σ :=
    (∃ n : nat, r ↦ #n ∗ own γ (●F n))%I.

  Lemma ghost_var_frac_agree γ (n m p q: nat):
    own γ (●F n) -∗ own γ (◯F{1 / 2} p) -∗ own γ (◯F{1 / 2} q) -∗ ⌜ #n = #(p + q) ⌝.
  Proof.
    iIntros "Hγ● H1 H2".
    iDestruct (own_valid_3 with "H1 H2 Hγ●") as "H3".
    rewrite -frac_auth_frag_op.
    rewrite Qp_half_half.
    iDestruct "H3" as %?%frac_auth_agree.
    rewrite (_: n = p + q); last by [].
    by rewrite Nat2Z.inj_add.
  Qed.

  (** *Exercise*: finish the missing cases of the proof. *)
  Lemma parallel_add_spec_3 :
    {{{ True }}} parallel_add {{{ RET #4; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (own_alloc (●F 0 ⋅ ◯F 0)) as (γ) "[Hγ● [Hγ1◯ Hγ2◯]]".
    { by apply auth_both_valid. }
    iMod (inv_alloc nroot _ (parallel_add_inv_3 r γ) with "[Hr Hγ●]") as "#Hinv".
    { iExists _. iFrame. }
    assert (forall (n k p: nat), ●F n ⋅ ◯F{1 / 2} p ~~> ●F (n + k) ⋅ ◯F{1 / 2} (k + p)) as Hhalf.
    {
      intros n k p. rewrite (comm plus).
      apply frac_auth_update.
      apply (op_local_update_discrete n p k).
      auto.
    }
    wp_smart_apply (wp_par (λ _, own γ (◯F{1/2} 2)) (λ _, own γ (◯F{1/2} 2))
                      with "[Hγ1◯] [Hγ2◯]").
    - iInv "Hinv" as (n) ">[Hr Hγ●]" "Hclose".
      wp_faa.
      iMod (own_update_2 _ _ _ (●F (n+2) ⋅ ◯F{1/2} 2) with "Hγ● Hγ1◯") as "[Hγ● Hγ1◯]"; [eapply Hhalf|].
      iMod ("Hclose" with "[Hr Hγ●]"); [|by auto].
      iExists _. iFrame. by rewrite Nat2Z.inj_add.
    - iInv "Hinv" as (n) ">[Hr Hγ●]" "Hclose".
      wp_faa.
      iMod (own_update_2 _ _ _ (●F (n+2) ⋅ ◯F{1/2} 2) with "Hγ● Hγ2◯") as "[Hγ● Hγ2◯]"; [eapply Hhalf|].
      iMod ("Hclose" with "[Hr Hγ●]"); [|by auto].
      iExists _. iFrame. by rewrite Nat2Z.inj_add.
    - iIntros (v1 v2) "[Hγ1◯ Hγ2◯] !>".
      wp_seq.
      iInv "Hinv" as (n) ">[Hr Hγ●]" "Hclose".
      wp_load.
      iDestruct (ghost_var_frac_agree with "Hγ● Hγ1◯ Hγ2◯") as %Hn; first by [].
      rewrite (_: n = 4); last first.
      { inversion Hn. lia. }
      iMod ("Hclose" with "[Hr Hγ●]"); [|by iApply "Post"].
      iNext. iExists 4.
      iFrame.
  Qed.


  Fixpoint parallel_faa_n n : expr :=
    match n with
    | O => ( FAA "r" #2 )
    | S n =>  (parallel_faa_n n) ||| ( FAA "r" #2 )
    end.

  Definition parallel_add_n n : expr :=
    let: "r" := ref #0 in
      (parallel_faa_n n)
      ;;
        !"r".

  Lemma parallel_add_spec_n (n: nat) :
    {{{ True }}} parallel_add_n n {{{ RET #(2 * n); True }}}.
  P    roof.

  Admitted.
  
End proof3.
