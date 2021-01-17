From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import weakestpre.
From iris.heap_lang Require Import lang.
From iris.heap_lang Require Import notation proofmode.
From iris.algebra Require Import csum agree excl.

Section ghoststate.
  Context `{!heapG Σ}.
  Context `{!inG Σ (exclR unitO)}. (* necessary stuff to define token_γ *)

  Definition token γ := own γ (Excl ()).
  Lemma new_token E : ⊢ |={E}=> ∃ γ, token γ.
  Proof. iMod (own_alloc (Excl ())) as (γ) "Hγ"; eauto; try done. Qed.
  Lemma token_excl γ : token γ ∗ token γ -∗ False.
  Proof.
    iIntros "[H1 H2]".
    by iDestruct (own_valid_2 with "H1 H2") as %Hfoo.
  Qed.

End ghoststate.

Section par.
  Context `{!heapG Σ}.
  Context `{!inG Σ (exclR unitO)}. (* necessary stuff to define token_γ *)

  Definition join : val := rec: "join" "x" :=
    match: !"x" with
      SOME "v" => "v"
    | NONE => "join" "x"
    end.
  Definition par : val := λ: "f1" "f2",
    let: "x" := ref NONE in
    Fork ("x" <- SOME ("f1" #()));;
    let: "v2" := "f2" #() in (join "x", "v2").


  Parameter Ψ1 Ψ2 : val → iProp Σ.
  Definition N := nroot.@"par".
  Definition inv_par γ x := inv N (x ↦ NONEV ∨ ∃ v, x ↦ SOMEV v ∗ (Ψ1 v ∨ token γ)).

  Lemma join_spec γ x :
    inv_par γ x -∗ token γ -∗ WP join #x {{ Ψ1 }}.
  Proof.
    iIntros "#HI Htok".
    iLöb as "IH".
    wp_rec. wp_bind (! #x)%E.
    unfold inv_par. iInv N as "[Hx|Hx]" "Hcl".
    - wp_load. iMod ("Hcl" with "[Hx]") as "_"; eauto.
      iModIntro. wp_pures. iApply ("IH" with "Htok").
    - iDestruct "Hx" as (v) "[Hx Hv]".
      wp_load. iDestruct "Hv" as "[Hv|Hv]"; last first.
      { iExFalso. iApply token_excl; iFrame. }
      iMod ("Hcl" with "[Hx Htok]") as "_".
      { iNext. iRight. iExists _; eauto with iFrame. }
      iModIntro. wp_pures. done.
  Qed.

  Lemma par_spec e1 e2 (Φ : val → iProp Σ) :
    WP e1 {{ Ψ1 }} -∗
    WP e2 {{ Ψ2 }} -∗
    (∀ v1 v2, Ψ1 v1 -∗ Ψ2 v2 -∗ Φ (v1, v2)%V) -∗
    WP par (λ: <>, e1) (λ: <>, e2) {{ Φ }}.
  Proof.
    iIntros "He1 He2 HΦ".
    wp_pures. wp_rec. wp_pures.
    wp_alloc x as "Hx". wp_pures.
    iMod new_token as (γ) "Htok".
    iMod (inv_alloc N _ (x ↦ NONEV ∨ ∃ v, x ↦ SOMEV v ∗ (Ψ1 v ∨ token γ))%I
            with "[Hx]") as "#H".
    { iNext. iLeft. done. }
    wp_apply (wp_fork with "[He1]").
    - iNext. wp_pures. wp_bind e1. iApply (wp_wand with "He1").
      iIntros (v1) "Hv". wp_pures.
      iInv N as "[Hx|Hx]" "Hcl".
      + wp_store. iApply "Hcl".
        iNext. iRight. iExists _. eauto with iFrame.
      + iDestruct "Hx" as (v') "[Hx Hv']".
        wp_store. iApply "Hcl". iNext. iRight.
        iExists _; iFrame "Hx". eauto with iFrame.
    - wp_pures. wp_bind e2. iApply (wp_wand with "He2").
      iIntros (v2) "Hv2". wp_pures.
      wp_bind (join _). iApply (wp_wand with "[Htok]").
      { iApply (join_spec with "H Htok"). }
      iIntros (v1) "Hv1". wp_pures.
      iApply ("HΦ" with "Hv1 Hv2").
  Qed.

End par.


Section spin_lock.
  Context `{!heapG Σ}.
  Context `{!inG Σ (exclR unitO)}. (* necessary stuff to define token_γ *)

  Definition newlock : val := λ: <>, ref #false.
  Definition acquire : val := rec: "acquire" "lk" :=
     if: CAS "lk" #false #true then #()
     else "acquire" "lk".
  Definition release : val := λ: "lk", "lk" <- #false.

  Definition locked γ := token γ.
  Definition is_lock γ v R := (∃ N (lk : loc),
      ⌜v = #lk⌝ ∗ inv N (∃ (b : bool), lk ↦ #b ∗ (⌜b = true⌝ ∨ locked γ ∗ R)))%I.

  Lemma newlock_spec R Φ :
    R -∗
    (∀ γ lk, is_lock γ lk R -∗ Φ lk) -∗
    WP newlock #() {{ Φ }}.
  Proof.
    iIntros "HR HΦ".
    wp_rec. iApply wp_fupd. wp_alloc lk as "Hlk".
    pose (N:=nroot.@"spin_lock").
    iMod new_token as (γ) "Htok".
    iMod (inv_alloc N _ (∃ (b : bool), lk ↦ #b ∗ (⌜b = true⌝ ∨ locked γ ∗ R))%I
            with "[HR Htok Hlk]") as "#H".
    { iNext. iExists false. iFrame. eauto with iFrame. }
    iModIntro. iApply "HΦ".
    iExists _,_. iFrame "H". done.
  Qed.

  Lemma is_lock_persistent γ lk R :
    is_lock γ lk R -∗ □ is_lock γ lk R.
  Proof. by iIntros "#H". Qed.

  Lemma acquire_spec γ lk R Φ :
    is_lock γ lk R -∗
    (R -∗ locked γ -∗ Φ #()) -∗
    WP acquire lk {{ Φ }}.
  Proof.
    iDestruct 1 as (N l ->) "#H". iIntros "HΦ".
    iLöb as "IH".
    wp_rec. wp_bind (CmpXchg _ _ _).
    iInv N as (b) "[Hb HR]" "Hcl".
    destruct b; simplify_eq/=.
    - wp_cmpxchg_fail.
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iNext. iExists _. eauto with iFrame. }
      iModIntro. wp_pures. by iApply "IH".
    - wp_cmpxchg_suc.
      iAssert (locked γ ∗ R)%I with "[HR]" as "[Hlocked HR]" .
      { iDestruct "HR" as "[%|$]". done. }
      iMod ("Hcl" with "[Hb]") as "_".
      { iNext. iExists _. iFrame "Hb". eauto. }
      iModIntro. wp_pures. by iApply ("HΦ" with "HR Hlocked").
  Qed.

  Lemma release_spec γ lk R Φ :
    is_lock γ lk R -∗
    R -∗
    locked γ -∗
    Φ #() -∗
    WP release lk {{ Φ }}.
  Proof.
    iDestruct 1 as (N l ->) "#H". iIntros "HR Hlocked HΦ".
    wp_rec.
    iInv N as (b) "[Hb HR']" "Hcl".
    wp_store.
    iMod ("Hcl" with "[-HΦ]") as "_".
    { iNext. iExists _. iFrame "Hb". eauto with iFrame. }
    done.
  Qed.

End spin_lock.

Definition oneshotR := csumR (exclR unitR) (agreeR unitR).
Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
Proof. solve_inG. Qed.

Section oneshot.
  Context `{!heapG Σ, !oneshotG Σ}.

  Definition pending γ := own γ (Cinl (Excl ())).
  Definition shot γ := own γ (Cinr (to_agree ())).
  Lemma new_pending : ⊢ |==> ∃ γ, pending γ.
  Proof. by apply own_alloc. Qed.
  Lemma pending_not_shot γ `{oneshotG Σ} :
    pending γ -∗ shot γ -∗ False.
  Proof.
    iIntros "Hp Hs".
    iDestruct (own_valid_2 with "Hs Hp") as %?. done.
  Qed.
  Lemma shot_persistent γ : shot γ -∗ □ shot γ.
  Proof. auto. Qed.
  Lemma shoot γ : pending γ ==∗ shot γ.
  Proof.
    apply own_update. by apply cmra_update_exclusive.
  Qed.

  Definition shootN := nroot .@ "shootN".

  Definition prog2 : expr :=
    let: "x" := ref #2 in
    Fork ("x" <- #1);;
    "x" <- #0;;
    !"x".

  Lemma prog2_spec :
    ⊢ WP prog2 {{ v, ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}.
  Proof.
    unfold prog2. wp_alloc x as "Hx".
    iMod new_pending as (γ) "Hp".
    iMod (inv_alloc N _ (( pending γ ∗ (∃ v, x ↦ v) ) ∨ (shot γ  ∗ (x ↦ #0 ∨ x ↦ #1)))%I
            with "[Hx Hp]") as "#H".
    { iNext. iLeft; iFrame. eauto with iFrame. }
    wp_pures. wp_apply wp_fork.
    - iInv N as "[[Hp Hx]|[Hs Hx]]" "Hcl".
      + iDestruct "Hx" as (v) "Hx". wp_store; eauto.
        iApply "Hcl". iNext. eauto with iFrame.
      + iDestruct "Hx" as "[Hx|Hx]"; wp_store; eauto.
        * iApply "Hcl". iNext. eauto with iFrame.
        * iApply "Hcl". iNext. eauto with iFrame.
    - wp_pures. wp_bind (#x <- #0)%E.
      iApply (wp_wand _ _ _ (λ v, shot γ)).
      { iInv N as "[[Hp Hx]|[#Hs Hx]]" "Hcl".
        + iDestruct "Hx" as (v) "Hx". wp_store; eauto.
          iMod (shoot with "Hp") as "#Hs".
          iMod ("Hcl" with "[-]") as "_".
          { iNext. eauto with iFrame. }
          done.
        + iDestruct "Hx" as "[Hx|Hx]"; wp_store; eauto; iFrame "Hs".
          * iApply "Hcl". iNext. eauto with iFrame.
          * iApply "Hcl". iNext. eauto with iFrame. }
      iIntros (?) "#Hs". wp_pures.
      iInv N as "[[>Hp Hx]|[_ Hx]]" "Hcl".
      { iExFalso. by iApply (pending_not_shot with "Hp Hs"). }
      iDestruct "Hx" as "[Hx|Hx]"; wp_load; eauto.
        * iMod ("Hcl" with "[-]"). iNext. eauto with iFrame.
          eauto with iFrame.
        * iMod ("Hcl" with "[-]"). iNext. eauto with iFrame.
          eauto with iFrame.
  Qed.

End oneshot.
