(**
In this exercise we consider a variant of the previous exercise. We have a
reference which is initially 0 and two threads running in parallel. One thread
increases the value of the reference by 2, whereas the other multiples the
value of the reference by two. An interesting aspect of this exercise is that
the outcome of this program is non-deterministic. Depending on which thread runs
first, the outcome is either 2 or 4.

There is no "fetch-and-multiply" operation in heap_lang, so we use a lock
instead to make both the addition and the multiplication atomic.

Contrary to the earlier exercises, this exercise is nearly entirely open.
*)
From iris.algebra Require Import excl_auth frac_auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation lib.par.
From exercises Require Import ex_03_spinlock.

Definition parallel_add_mul : expr :=
  let: "r" := ref #0 in
  let: "l" := newlock #() in
  (
    (acquire "l";; "r" <- !"r" + #2;; release "l")
  |||
    (acquire "l";; "r" <- !"r" * #2;; release "l")
  );;
  acquire "l";;
  !"r".

(** In this proof we will make use of Boolean ghost variables. *)
Section proof.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (excl_authR boolO)}.

  (** The same helping lemmas for ghost variables that we have already seen in
  the previous exercise. *)
  Lemma ghost_var_alloc b :
    ⊢ |==> ∃ γ, own γ (●E b) ∗ own γ (◯E b).
  Proof.
    iMod (own_alloc (●E b ⋅ ◯E b)) as (γ) "[??]".
    - by apply excl_auth_valid.
    - by eauto with iFrame.
  Qed.

  Lemma ghost_var_agree γ b c :
    own γ (●E b) -∗ own γ (◯E c) -∗ ⌜ b = c ⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %<-%excl_auth_agree_L.
  Qed.

  Lemma ghost_var_update γ b' b c :
    own γ (●E b) -∗ own γ (◯E c) ==∗ own γ (●E b') ∗ own γ (◯E b').
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E b' ⋅ ◯E b') with "Hγ● Hγ◯") as "[$$]".
    { by apply excl_auth_update. }
    done.
  Qed.

  (** *Difficult exercise*: come up with a suitable invariant and prove the spec
  of [parallel_add_mul]. In this proof, you should use Boolean ghost variables,
  and the rules for those as given above. You are allowed to use any number of
  Boolean ghost variables. *)
  Definition parallel_add_mul_inv (r : loc) (γ1 γ2 : gname) : iProp Σ :=
    (∃ (b1 b2 : bool) (z : Z),
        r ↦ #z ∗
       ⌜match b1, b2 with
        | true,  true  => (z = 2 ∨ z = 4)%Z
        | true,  false => z = 2%Z
        | false, _     => z = 0%Z
        end⌝
       ∗ own γ1 (●E b1) ∗ own γ2 (●E b2)
    )%I.

  Lemma parallel_add_mul_spec :
    {{{ True }}} parallel_add_mul {{{ z, RET #z; ⌜ z = 2%Z ∨ z = 4%Z ⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add_mul. wp_alloc r as "Hr". wp_let.
    iMod (ghost_var_alloc false) as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc false) as (γ2) "[Hγ2● Hγ2◯]".
    wp_apply (newlock_spec (parallel_add_mul_inv r γ1 γ2) with "[Hr Hγ1● Hγ2●]").
    { iExists false, false, 0%Z. iFrame. simpl. auto. }
    iIntros (l) "#Hl".
    wp_let.
    (* iMod (inv_alloc nroot _ (parallel_add_mul_inv r γ1 γ2) with "[Hγ1● Hγ2●]") as "#Hinvx". *)
    (* { iNext. iExists false, false. iFrame. } *)
    (* wp_bind (_ ||| _)%E. *)
    wp_smart_apply (wp_par (λ _, own γ1 (◯E true)) (λ _, own γ2 (◯E true))
                      with "[Hγ1◯] [Hγ2◯]").
    - wp_bind (acquire _).
      wp_apply (acquire_spec with "Hl"); iIntros "Hr".
      iDestruct "Hr" as (b1 b2 n) "(Hr & Hb & H1 & H2)".
      wp_seq. wp_load. wp_store.
      iDestruct (ghost_var_agree with "H1 Hγ1◯") as %->.
      iDestruct "Hb" as %->.
      iMod (ghost_var_update γ1 true with "H1 Hγ1◯") as "[H1x H1y]".
      wp_apply (release_spec with "[- H1y $Hl]").
      { iExists true, b2, 2%Z. iFrame. iPureIntro. destruct b2; lia. }
        by iIntros.
    - wp_bind (acquire _).
      wp_apply (acquire_spec with "Hl"); iIntros "Hr".
      iDestruct "Hr" as (b1 b2 n) "(Hr & Hb & H1 & H2)".
      wp_seq. wp_load. wp_store.
      iDestruct (ghost_var_agree with "H2 Hγ2◯") as %->.
      iMod (ghost_var_update γ2 true with "H2 Hγ2◯") as "[H1x H1y]".
      wp_apply (release_spec with "[- H1y $Hl]").
      { iExists b1, true, (n * 2)%Z. iFrame.
        destruct b1; iDestruct "Hb" as %->; iPureIntro; lia.
      }
        by iIntros.
    - iIntros (v1 v2) "[H1 H2]".
      iNext.
      wp_seq.
      wp_apply (acquire_spec _ with "Hl"). iIntros "Hr".
      iDestruct "Hr" as  (b1 b2 n) "(Hr & Hb & H1r & H2r)".
      wp_seq; wp_load.
      iApply "Post".
      iDestruct (ghost_var_agree γ1 with "H1r H1") as %->.
      iDestruct (ghost_var_agree γ2 with "H2r H2") as %->.
      auto.
  Qed.
End proof.
