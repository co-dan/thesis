From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import weakestpre.
From iris.heap_lang Require Import lang.
From iris.heap_lang Require Import notation proofmode.

Section invariants.
  Context `{!heapG Σ}. (* Ghost stated required for HeapLang *)

  Definition prog1 : expr :=
    let: "x" := ref #0 in
    Fork ("x" <- #1);;
    !"x".

  Definition N := nroot.@"myinvariant".

  Lemma prog1_spec :
    ⊢ WP prog1 {{ v, ⌜v = #0⌝ ∨ ⌜v = #1⌝ }}.
  Proof.
    unfold prog1. wp_alloc x as "Hx".
    iMod (inv_alloc N _ (x ↦ #0 ∨ x ↦ #1)%I with "[Hx]") as "#H".
    { iNext. iLeft; eauto. }
    wp_pures. wp_apply wp_fork.
    - iInv N as "[Hx|Hx]"; wp_store; eauto.
    - wp_pures. iInv N as "[Hx|Hx]"; wp_load; iModIntro; eauto.
  Qed.

End invariants.
