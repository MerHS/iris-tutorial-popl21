(**
In this exercise we implement the running example during the lecture of the
tutorial: proving that when two threads increase a reference that's initially
zero by two, the result is four.
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
    iDestruct "H3" as %->%frac_auth_agree_L.
    iPureIntro.
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
      (* iCombine "Hγ1◯ Hγ2◯" as "Hγ◯". *)
      (* iDestruct (own_valid_2 with "Hγ● Hγ◯") as %->%frac_auth_agree_L. *)
      iDestruct (ghost_var_frac_agree with "Hγ● Hγ1◯ Hγ2◯") as %Hn; first by [].
      rewrite (_: n = 4); last first.
      { inversion Hn. lia. }
      iMod ("Hclose" with "[Hr Hγ●]"); [|by iApply "Post"].
      iNext. iExists 4.
      iFrame.
  Qed.

  Definition parallel_faa_n : val :=
    rec: "parallel_faa_n" "n" "r" :=
      if: (BinOp LeOp "n" #0) then FAA "r" #2 else ("parallel_faa_n" (BinOp MinusOp "n" #1) "r") ||| ( FAA "r" #2 ).

  Definition parallel_add_n n : expr :=
    let: "r" := ref #0 in
      parallel_faa_n #n "r"
      ;;
      !"r".

  Lemma parallel_add_spec_n (n: nat) :
    {{{ True }}} parallel_add_n n {{{ RET #(2 * (n + 1)); True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add_n. wp_alloc r as "Hr". wp_let.
    iMod (own_alloc (●F 0 ⋅ ◯F 0)) as (γ) "[Hγ● Hγ◯]".
    { by apply auth_both_valid. }
    iMod (inv_alloc nroot _ (parallel_add_inv_3 r γ) with "[Hr Hγ●]") as "#Hinv".
    { iExists _. iFrame. }
    assert (forall (n k p: nat) q, ●F n ⋅ ◯F{q} p ~~> ●F (n + k) ⋅ ◯F{q} (p + k)) as Hup.
    {
      intros n0 k p q.
      apply frac_auth_update.
      rewrite (comm plus). rewrite [p + _](comm plus).
      apply (op_local_update_discrete n0 p k).
      auto.
    }
    destruct n.
    - wp_rec. wp_pures.
      wp_bind (FAA _ _).
      iInv "Hinv" as (n) ">[Hr Hg]" "Hclose".
      wp_faa.
      iMod (own_update_2 _ _ _ (●F (n+2) ⋅ ◯F 2) with "Hg Hγ◯") as "[Hg Hγ◯]".
      {
        apply frac_auth_update.
        rewrite (comm plus).
        apply (op_local_update_discrete n 0 2).
        auto.
      }
      iMod ("Hclose" with "[Hg Hr]").
      { iExists (n + 2).
        iFrame.
        iNext.
        rewrite Nat2Z.inj_add.
        iFrame.
      }
      iModIntro.
      wp_seq.
      iInv "Hinv" as (l) ">[Hr Hg]" "Hclose".
      wp_load.
      iDestruct (own_valid_2 with "Hg Hγ◯") as %->%frac_auth_agree_L.
      iMod ("Hclose" with "[Hg Hr]").
      { iExists 2. iFrame. }
      by iApply "Post".
    - wp_rec.
      wp_let.
      wp_op.
      wp_if_false.
      pose nq:= (pos_to_Qp (Pos.of_nat (S n))).
      pose lq:= (nq / (nq + 1))%Qp.
      pose rq:= (1 / (nq + 1))%Qp.
      rewrite (_: 1%Qp = (lq + rq)%Qp); last first.
      {
        subst lq rq.
        rewrite -Qp_div_add_distr Qp_div_diag.
        auto.
      }
      rewrite (frac_auth_frag_op lq rq 0 0).
      iDestruct (own_op _ _ _ with "Hγ◯") as "[Hlq Hrq]".
      wp_smart_apply (wp_par (λ _, own γ (◯F{lq} (2 * (S n)))) (λ _, own γ (◯F{rq} 2))
                      with "[Hlq] [Hrq]").
      + subst nq lq rq.
        wp_op.
        rewrite (_ : (_ - _)%Z = Z.of_nat n); last by lia.
        remember (pos_to_Qp (Pos.of_nat (S n))) as nq.
        remember (nq / (nq + 1))%Qp as lq.
        assert (forall k, 0 <= k <= n ->
                     inv nroot (parallel_add_inv_3 r γ) -∗
                         own γ (◯F{((pos_to_Qp (Pos.of_nat (S k))) / (nq + 1))%Qp} 0) -∗
                         WP parallel_faa_n #k #r {{ _, own γ (◯F{((pos_to_Qp (Pos.of_nat (S k))) / (nq + 1))%Qp} (2 * (S k))) }}) as HX.
        {
          intros.
          iIntros "#Hinv Hk".
          iInduction k as [|k] "IH" ; wp_rec.
          - wp_pures.
            iInv "Hinv" as (l) ">[Hr Hg]" "Hclose".
            wp_faa.
            iMod (own_update_2 _ _ _ (●F (l + 2) ⋅ ◯F{_} 2) with "Hg Hk") as "[Hl Hk]".
            { rewrite {2}(_: 2 = 0 + 2); last by lia. by apply Hup. }
            iMod ("Hclose" with "[Hr Hl]"); last by [].
            iExists _. iFrame.
            by rewrite Nat2Z.inj_add.
          - wp_let.
            wp_op.
            wp_if.
            remember (pos_to_Qp (Pos.of_nat (S k))) as kq'.
            remember (kq' / (nq + 1))%Qp as lkq'.
            remember (1 / (nq + 1))%Qp as rkq'.
            remember (pos_to_Qp (Pos.of_nat (S (S k)))) as kq.
            remember (kq / (nq + 1))%Qp as lkq.
            rewrite (_: lkq = (lkq' + rkq')%Qp); last first.
            {
              subst.
              rewrite -Qp_div_add_distr.
              rewrite (_: pos_to_Qp (Pos.of_nat (S (S k))) = (pos_to_Qp (Pos.of_nat (S k)) + 1)%Qp); first by [].
              rewrite pos_to_Qp_add.
              apply pos_to_Qp_inj_iff.
              lia.
            }
            rewrite (frac_auth_frag_op lkq' rkq' 0 0).
            iDestruct (own_op _ _ _ with "Hk") as "[Hlq Hrq]".
            wp_smart_apply (wp_par (λ _, own γ (◯F{lkq'} (2 * (S k)))) (λ _, own γ (◯F{rkq'} 2))
                              with "[Hlq] [Hrq]").
            + wp_op. rewrite (_: (S k - 1)%Z = Z.of_nat k); last by lia.
              iApply "IH"; last by [].
              iPureIntro. lia.
            + iInv "Hinv" as (l) ">[Hr Hg]" "Hclose".
              wp_faa.
              iMod (own_update_2 _ _ _ (●F (l + 2) ⋅ ◯F{_} 2) with "Hg Hrq") as "[Hl Hrq]".
              { rewrite {2}(_: 2 = 0 + 2); last by lia. by apply Hup. }
              iMod ("Hclose" with "[Hr Hl]"); last by [].
              iExists _. iFrame.
              by rewrite Nat2Z.inj_add.
            + iIntros (v1 v2) "[Hl Hr]".
              iCombine "Hl Hr" as "H".
              iNext.
              rewrite (_: (2 * (S (S k))) = (2 * S k + 2)); [auto | lia].
        }
        destruct n.
        { simpl.
          wp_rec. wp_pures.
          iInv "Hinv" as (l) ">[Hr Hg]" "Hclose".
          wp_faa.
          iMod (own_update_2 _ _ _ (●F (l + 2) ⋅ ◯F{lq} 2) with "Hg Hlq") as "[Hl Hrq]".
          { rewrite {2}(_: 2 = 0 + 2); last by lia. by apply Hup. }
          iMod ("Hclose" with "[Hr Hl]"); last by [].
          iExists _. iFrame.
          by rewrite Nat2Z.inj_add.
        }
        assert (0 <= (S n) /\ (S n) <= (S n)) as Hn; first by lia.
        subst.
        iApply ((HX (S n) Hn) with "Hinv Hlq").
      + iInv "Hinv" as (l) ">[Hr Hg]" "Hclose".
        wp_faa.
        iMod (own_update_2 _ _ _ (●F (l + 2) ⋅ ◯F{rq} 2) with "Hg Hrq") as "[Hl Hrq]".
        { rewrite {2}(_: 2 = 0 + 2); last by lia. by apply Hup. }
        iMod ("Hclose" with "[Hr Hl]"); last by [].
        iExists _. iFrame.
        by rewrite Nat2Z.inj_add.
      + iIntros (v1 v2) "[Hlq Hrq]".
        iNext. wp_seq.
        iInv "Hinv" as (l) ">[Hr Hg]" "Hclose".
        wp_load.
        iCombine "Hlq Hrq" as "Hl".
        rewrite (_: (lq + rq)%Qp = 1%Qp); last first.
        {
          subst lq rq.
          rewrite -Qp_div_add_distr Qp_div_diag.
          auto.
        }
        iDestruct (own_valid_2 with "Hg Hl") as %->%frac_auth_agree_L.
        iMod ("Hclose" with "[Hg Hr]").
        { iExists _. iFrame. }
        rewrite (_: 2 * S n + 2 = 2 * (S n + 1)); last by lia.
        rewrite (_: Z.of_nat (2 * _)%nat = (2 * (S n + 1))%Z); last by lia.
        by iApply "Post".
    Qed.
End proof3.
