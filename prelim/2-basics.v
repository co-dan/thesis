From iris.heap_lang Require Import notation proofmode.

Section proofmode.
  Context `{!heapG Σ}. (* Ghost stated required for HeapLang *)

  Lemma example (P Q : iProp Σ) : P -∗ (P -∗ Q) -∗ Q.
  Proof. iIntros "H1 H2". iApply ("H2" with "H1"). Qed.

  Lemma example2 (P Q : nat → iProp Σ) :
    (∀ x, P x -∗ Q (x+1)) -∗ (∃ x, P x) -∗ (∃ x, Q x).
  Proof.
    iIntros "H1 H2". iDestruct "H2" as (x) "H2".
    iExists (x+1). iApply ("H1" with "H2").
  Qed.

  Lemma example_wp (l1 l2 : loc) (v1 v2 w1 : val) :
    l1 ↦ v1 ∗ l2 ↦ v2 -∗
    WP (#l1 <- w1;; ! #l2) {{ v, ⌜v = v2⌝ }}.
  Proof.
    iIntros "[H1 H2]". wp_store. wp_load. eauto.
  Qed.
End proofmode.

Section list.
  Context `{!heapG Σ}.

  Definition llnil : val := λ: <>, NONEV.
  Definition llcons : val := λ: "x" "l", SOME ("x", "l").

  Definition llhead : val := λ: "l",
    match: "l" with
      SOME "p" => Fst "p"
    | NONE => #false
    end.

  Definition lltail : val := λ: "l",
    match: "l" with
      SOME "p" => Snd "p"
    | NONE => #false
    end.

  Definition llmember : val := rec: "llmember" "x" "l" :=
    match: "l" with
      SOME "p" => let: "h" := Fst "p" in

                  let: "t" := Snd "p" in
                  if: "h" = "x" then #true else "llmember" "x" "t"
    | NONE => #false
    end.

  Definition llfilter : val := rec: "llfilter" "f" "l" :=
    match: "l" with
      SOME "p" => let: "h" := Fst "p" in

                  let: "t" := Snd "p" in
                  if: "f" "h"
                  then llcons "h" ("llfilter" "f" "t")
                  else "llfilter" "f" "t"
    | NONE => llnil #()
    end.

  Fixpoint is_list (hd : val) (xs : list val) : iProp Σ :=
    match xs with
    | [] => ⌜hd = NONEV⌝
    | x :: xs => ∃ hd', ⌜hd = SOMEV (x,hd')⌝ ∗ is_list hd' xs
  end.

  Lemma is_list_dup v xs :
    is_list v xs ⊢ is_list v xs ∗ is_list v xs.
  Proof.
    revert v. induction xs as [|h t IHt]; first eauto.
    intros v. simpl. iDestruct 1 as (hd ->) "H".
    rewrite IHt. iDestruct "H" as "[H1 H2]".
    iSplitL "H1"; iExists _; eauto.
  Qed.

  Lemma wp_llnil :
    (⊢ WP llnil #() {{ v, is_list v [] }})%I.
  Proof. wp_rec. eauto. Qed.

  Lemma wp_llcons (h t : val) (ws : list val) :
    is_list t ws -∗
    WP llcons h t {{ v, is_list v (h::ws) }}.
  Proof. iIntros "Ht". wp_rec. wp_pures. simpl. eauto. Qed.

  Lemma wp_llhead v h ws :
    is_list v (h::ws) -∗
    WP llhead v {{ v', ⌜v' = h⌝ ∗ is_list v (h::ws) }}.
  Proof.
    simpl.
    iDestruct 1 as (hd ->) "Hhd".
    wp_rec. wp_pures. iSplit; eauto.
  Qed.

  Lemma wp_lltail v h ws :
    is_list v (h::ws) -∗
    WP lltail v {{ v', is_list v' ws }}.
  Proof.
    simpl.
    iDestruct 1 as (hd ->) "Hhd".
    wp_rec. wp_pures. eauto.
  Qed.

  Lemma wp_llfilter (f l : val) (P : val → iProp Σ) ws :
    is_list l ws -∗
    □ (∀ v : val, WP f v {{ v', (⌜v' = #true⌝ ∗ P v) ∨ ⌜v' = #false⌝ }}) -∗
    WP llfilter f l {{ v, ∃ ws', is_list v ws' ∗ ([∗ list] w'∈ws', P w') }}.
  Proof.
    iIntros "Hws #Hf".
    iLöb as "IH" forall (l ws).
    wp_rec. wp_pures.
    destruct ws as [|h t]; simpl.
    - iDestruct "Hws" as %->. wp_pures.
      iApply wp_wand. iApply wp_llnil.
      iIntros (v) "Hv". iExists []. iFrame. eauto.
    - iDestruct "Hws" as (hd ->) "Hhd". wp_pures.
      wp_bind (f h). iApply wp_wand.
      { iApply "Hf". }
      iIntros (v). iDestruct 1 as "[[-> Hh]|->]"; wp_pures.
      + wp_bind (llfilter _ _). iApply (wp_wand with "[Hhd]").
        { iApply ("IH" with "Hhd"). }
        iIntros (v). iDestruct 1 as (ws') "[Hws HP]".
        iApply (wp_wand with "[Hws]").
        { iApply (wp_llcons with "Hws"). }
        iIntros (v') "Hv'". iExists _. iFrame.
      + iApply ("IH" with "Hhd").
  Qed.

  Lemma wp_llmember (x l : val) ws :
    val_is_unboxed x →
    (* ^ make sure that we can safely compare `x` with other values *)
    is_list l ws -∗
    WP llmember x l {{ v, is_list l ws ∗
                      ((⌜v = #true⌝ ∗ ⌜x ∈ ws⌝) ∨ (⌜v = #false⌝ ∗ ⌜x ∉ ws⌝)) }}.
  Proof.
    iIntros (?) "Hl".
    iLöb as "IH" forall (l ws).
    wp_rec. wp_pures.
    destruct ws as [|h ws]; simpl.
    - iDestruct "Hl" as "->". wp_pures. repeat iSplit; eauto.
      iRight. iSplit; eauto. iPureIntro. set_solver.
    - iDestruct "Hl" as (t ->) "Ht". wp_pures.
      case_bool_decide; wp_pures.
      + iSplitL. { iExists _; eauto. }
        iLeft. iSplit; eauto. iPureIntro; set_solver.
      + iSpecialize ("IH" with "Ht").
        iApply (wp_wand with "IH").
        iIntros (v) "[Ht [[-> %]|[-> %]]]".
        * iSplitL.
          { iExists _; eauto. }
          iLeft; iSplit; eauto. iPureIntro; set_solver.
        * iSplitL.
          { iExists _; eauto. }
          iRight. iSplit; eauto. iPureIntro. set_solver.
  Qed.

End list.

Section mset.
  Context `{!heapG Σ}.

  Definition mset_create : val := λ: <>, ref (llnil #()).

  Definition mset_member : val := λ: "x" "v",
    let: "l" := !"v" in
    llmember "x" "l".

  Definition mset_add : val := λ: "x" "v",
    let: "l" := !"v" in
    "v" <- llcons "x" "l".

  Definition mset_clear : val := λ: "v", "v" <- llnil #().

  Definition is_mset (v : val) (X : gset val) : iProp Σ :=
    (∃ hd ws (l : loc), ⌜v = #l⌝ ∗ l ↦ hd ∗ is_list hd ws ∗
        ⌜NoDup ws ∧ X = list_to_set ws⌝)%I.


  Lemma wp_mset_create :
    ⊢ WP mset_create #() {{ v, is_mset v ∅ }}.
  Proof.
    wp_rec. wp_bind (llnil #()).
    iApply wp_wand; first iApply wp_llnil.
    iIntros (v) "Hv". wp_alloc r as "Hr".
    iExists _,_,_. iFrame. iSplit; eauto. iPureIntro.
    split; eauto || econstructor.
  Qed.

  Lemma wp_mset_add v X (x : val) :
    x ∉ X →
    is_mset v X -∗ WP mset_add x v {{ v', ⌜v' = #()⌝ ∗ is_mset v ({[x]} ∪ X) }}.
  Proof.
    iIntros (Hx) "Hv".
    wp_rec. wp_pures.
    iDestruct "Hv" as (hd ws l ->) "(Hl & Hws & %)".
    wp_load. wp_pures. wp_bind (llcons _ _).
    iApply (wp_wand with "[Hws]").
    { iApply (wp_llcons with "Hws"). }
    iIntros (v) "Hv". wp_store. iSplit; eauto.
    iExists _,_,_. iFrame. iSplit; eauto.
    iPureIntro. destruct_and!. rewrite NoDup_cons. set_solver.
  Qed.

  Lemma wp_mset_member v X (x : val) :
    val_is_unboxed x →
    is_mset v X -∗
    WP mset_member x v {{ v', is_mset v X ∗
                            (⌜v' = #true⌝ ∗ ⌜x ∈ X⌝ ∨ ⌜v' = #false⌝ ∗ ⌜x ∉ X⌝) }}.
  Proof.
    iIntros (?) "Hv".
    wp_rec. wp_pures.
    iDestruct "Hv" as (hd ws l ->) "(Hl & Hws & %)".
    wp_load. wp_pures.
    iApply (wp_wand with "[Hws]").
    { iApply (wp_llmember with "Hws"); auto. }
    iIntros (v) "[Hws [[-> %]|[-> %]]]".
    - iSplitL.
      { iExists _,_,_. eauto with iFrame. }
      iLeft. iSplit; eauto. iPureIntro. set_solver.
    - iSplitL.
      { iExists _,_,_. eauto with iFrame. }
      iRight. iSplit; eauto. iPureIntro. set_solver.
  Qed.

  Lemma wp_mset_clear v X :
    is_mset v X -∗ WP mset_clear v {{ v', ⌜v' = #()⌝ ∗ is_mset v ∅ }}.
  Proof.
    iDestruct 1 as (hd ws l ->) "(Hl & _ & _)".
    wp_rec. wp_bind (llnil #()).
    iApply wp_wand; first iApply wp_llnil.
    iIntros (v) "Hv". wp_store. iSplit; eauto.
    iExists _,_,_. iFrame "Hl Hv".
    iSplit; eauto. iPureIntro.
    split; eauto || econstructor.
  Qed.

End mset.
