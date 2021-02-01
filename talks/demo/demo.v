From iris.algebra.lib Require Import excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import lib.par proofmode notation.
Set Default Proof Using "All".
Open Scope Z.

(*! Part 1: verifying swap *)


(** * The swap function, defined as a heap-lang value. *)
Definition swap : val := λ: "x" "y",
  let: "tmp" := !"x" in
  "x" <- !"y";;
  "y" <- "tmp".


Section proof.
Context `{!heapG Σ}.




Lemma ipm_demo {A} P R (Φ: A → iProp Σ) :
  P ∗ (∃ a, Φ a) ∗ R -∗ ∃ a, Φ a ∗ P.
Proof.
  iIntros "[HP [HΦ HR]]".
  (* iIntros "H".
  iDestruct "H" as "[HP [HΦ HR]]". *)
  iDestruct "HΦ" as (x) "HΦ".
  iExists x.
  iSplitL "HΦ".
  - iAssumption.
  - iAssumption.
Qed.




Lemma swap_spec x y v1 v2 :
  {{{ x ↦ v1 ∗ y ↦ v2 }}} swap #x #y {{{ RET #(); x ↦ v2 ∗ y ↦ v1 }}}.
Proof.
  iIntros (Φ) "[Hx Hy] Post".

  (* The "Texan triple" [ {{{ P }}} e {{{ RET v, Q }}} ] is
     syntactic sugar for:

         ∀ Φ, P -∗ (Q -∗ Φ v) -∗ WP e {{ v, Φ v }}

     Which is logically equivalent to
     [ P -∗ WP e {{ x, x = v ∗ Q }} ] *)

  unfold swap.
  wp_lam. wp_let.
  wp_load. wp_let.
  wp_load. wp_store.
  wp_store.
  iModIntro.
  iApply "Post".
  iSplitL "Hx".
  - iApply "Hx".
  - iApply "Hy".
Qed.
End proof.



(*! Part 2: verifying parallel add 2 example *)

Definition parallel_add : expr :=
  let: "r" := ref #0 in
  (FAA "r" #2 ||| FAA "r" #2);;
  !"r".

Section proof.
  Context `{!heapG Σ, !spawnG Σ}.

  (* we need to name our invariant; any name will do here *)
  Let N := nroot.@"example".

  Definition parallel_add_inv (r : loc) : iProp Σ :=
    (∃ n : Z, r ↦ #n ∗ ⌜ Zeven n ⌝)%I.

  (** * main body of the proof *)
  (* [inv N P] was written as a box around [P] (with no name [N]) in the
  lecture *)
  Lemma faa_preserves_even (r : loc) :
    {{{ inv N (parallel_add_inv r) }}}
      FAA #r #2
    {{{ (n : Z), RET #n; True }}}.
  Proof.
    iIntros (Φ) "#Hinv Post".
    iInv "Hinv" as (n) ">[Hr %]".
    wp_faa.
    iModIntro.
    iSplitL "Hr".
    { iNext. iExists (n + 2); iFrame.
      iPureIntro. apply Zeven_plus_Zeven; done. }
    by iApply "Post".
  Qed.

  Lemma parallel_add_spec_even :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜Zeven n⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add. wp_alloc r as "Hr". wp_let.
    iMod (inv_alloc N _ (parallel_add_inv r) with "[Hr]") as "#Hinv".
    { iNext. unfold parallel_add_inv.
      iExists 0. iFrame. }
    wp_smart_apply (wp_par (λ _, True%I) (λ _, True%I)).
    { (* first thread *)
      wp_apply (faa_preserves_even with "[$Hinv]").
      done. }
    { (* first thread *)
      wp_apply (faa_preserves_even with "[$Hinv]").
      done. }

    iIntros (??) "_".
    iNext.
    wp_pures.
    iInv "Hinv" as (n) ">[Hr %]".
    wp_load.
    iModIntro.
    iSplitL "Hr".
    { iExists _; by iFrame. }
    iApply "Post".
    done.
  Qed.
End proof.



(*! Part 3: verifying parallel add returns 4 *)
Section proof.
  Context `{!heapG Σ, !spawnG Σ, !inG Σ (excl_authR ZO)}.

  Let N := nroot.@"example2".

  (* [●E n] and [◯E n] are elements of the particular RA we used in
  lecture to derive ghost variables, written ●n and ◯n in lecture *)
  (* [own γ (●E n)] was written like γ ↪● n in the lecture (and general
  ghost ownership was written with a dashed box with a superscript γ) *)

  Definition parallel_add_inv_2 (r : loc) (γ1 γ2 : gname)
    : iProp Σ :=
    ∃ (n1 n2 : Z), r ↦ #(n1 + n2) ∗
                   own γ1 (●E n1) ∗ own γ2 (●E n2).

  (* these are the three lemmas for ghost variables, derived from the
     general axioms for ownership *)
  (* note: there are simpler ways to do these proofs, here we're trying
     to stick to the lecture *)

  Lemma ghost_var_alloc (n : Z) :
    True ==∗ ∃ γ, own γ (●E n) ∗ own γ (◯E n).
  Proof.
    iIntros "_".
    iMod (own_alloc (●E n ⋅ ◯E n)) as (γ) "[H● H◯]".
    { apply excl_auth_valid. }
    iModIntro. iExists _; iFrame.
  Qed.

  Lemma ghost_var_agree (γ : gname) (n1 n2 : Z) :
    own γ (●E n1) ∗ own γ (◯E n2) -∗ ⌜n1 = n2⌝.
  Proof.
    iIntros "[H1 H2]".
    iDestruct (own_op with "[$H1 $H2]") as "H".
    iDestruct (own_valid with "H") as %H.
    apply excl_auth_agree_L in H; done.
  Qed.

  Lemma ghost_var_update (n' : Z) (γ : gname) (n : Z) :
    own γ (●E n) ∗ own γ (◯E n) ==∗ own γ (●E n') ∗ own γ (◯E n').
  Proof.
    iIntros "[H1 H2]".
    iDestruct (own_op with "[$H1 $H2]") as "H".
    iMod (own_update _ _ (●E n' ⋅ ◯E n') with "H")
      as "[H1 H2]".
    { apply excl_auth_update. }
    by iFrame.
  Qed.

  Lemma parallel_add_spec :
    {{{ True }}} parallel_add {{{ n, RET #n; ⌜n = 4⌝ }}}.
  Proof.
    iIntros (Φ) "_ Post".
    unfold parallel_add.
    wp_alloc r as "Hr".
    wp_let.
    iMod (ghost_var_alloc 0 with "[//]") as (γ1) "[Hγ1● Hγ1◯]".
    iMod (ghost_var_alloc 0 with "[//]") as (γ2) "[Hγ2● Hγ2◯]".
    iMod (inv_alloc N _ (parallel_add_inv_2 r γ1 γ2) with "[Hr Hγ1● Hγ2●]") as "#Hinv".
    { iNext. iExists _, _; iFrame. }
    (* note that we have pre- and postconditions for each thread here,
    reporting what each thread contributed *)
    wp_smart_apply (wp_par (λ _, own γ1 (◯E 2))%I (λ _, own γ2 (◯E 2))%I with
                  "[Hγ1◯] [Hγ2◯]").

    { iInv "Hinv" as (n1 n2) ">(Hr & Hγ1 & Hγ2)".
      wp_faa.
      iDestruct (ghost_var_agree with "[$Hγ1 $Hγ1◯]") as %->.
      iMod (ghost_var_update 2 with "[$Hγ1 $Hγ1◯]") as "[Hγ1 Hγ1◯]".
      iFrame "Hγ1◯".
      iModIntro. iNext. iExists _, _; iFrame.
      replace (2 + n2) with (0 + n2 + 2) by lia.
      iAssumption. }

    { iInv "Hinv" as (n1 n2) ">(Hr & Hγ1 & Hγ2)".
      wp_faa.
      iDestruct (ghost_var_agree with "[$Hγ2 $Hγ2◯]") as %->.
      iMod (ghost_var_update 2 with "[$Hγ2 $Hγ2◯]") as "[Hγ2 Hγ2◯]".
      iFrame "Hγ2◯".
      iModIntro. iNext. iExists _, _; iFrame.
      replace (n1 + 2) with (n1 + 0 + 2) by lia.
      iAssumption. }

    iIntros (v1 v2) "[Hγ1◯ Hγ2◯] !>".
    wp_seq.
    iInv "Hinv" as (n1 n2) ">(Hr & Hγ1 & Hγ2)".
    iDestruct (ghost_var_agree with "[$Hγ1 $Hγ1◯]") as %->.
    iDestruct (ghost_var_agree with "[$Hγ2 $Hγ2◯]") as %->.
    wp_load.
    iModIntro.
    iSplitL "Hr Hγ1 Hγ2".
    { iNext. iExists _, _; iFrame. }
    iApply "Post".
    done.
  Qed.

End proof.
