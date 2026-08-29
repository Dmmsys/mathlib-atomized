/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Fintype.Basic

/-!
# Induction principles for `∀ i, Finset (α i)`

In this file we prove a few induction principles for functions `Π i : ι, Finset (α i)` defined on a
finite type.

* `Finset.induction_on_pi` is a generic lemma that requires only `[Finite ι]`, `[DecidableEq ι]`,
  and `[∀ i, DecidableEq (α i)]`; this version can be seen as a direct generalization of
  `Finset.induction_on`.

* `Finset.induction_on_pi_max` and `Finset.induction_on_pi_min`: generalizations of
  `Finset.induction_on_max`; these versions require `∀ i, LinearOrder (α i)` but assume
  `∀ y ∈ g i, y < x` and `∀ y ∈ g i, x < y` respectively in the induction step.

## Tags
finite set, finite type, induction, function
-/

public section


open Function

variable {ι : Type*} {α : ι -> Type*} [Finite ι] [DecidableEq ι] [forall i, DecidableEq (α i)]

namespace Finset

/--
theorem `induction_on_pi_of_choice` / 定理 `induction_on_pi_of_choice`

English:
theorem induction_on_pi_of_choice
  statement: (r : forall i, α i -> Finset (α i) -> Prop)
  proof: by
  cases nonempty_fintype ι
  induction hs : univ.sigma f using Finset.strongInductionOn generalizing f with | _ s ihs
  subst s
  rcases eq_empty_or_nonempty (univ.sigma f) with he | hne
  · convert! h0 using 1
    simpa [funext_iff] using he
  · rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩
    rc

中文:
定理 induction_on_pi_of_choice
  结论: (r : 对任意 i, α i -> 有限集 (α i) -> 命题)
  证明: by
  cases nonempty_fintype ι
  induction hs : univ.sigma f using Finset.strongInductionOn generalizing f with | _ s ihs
  subst s
  rcases eq_empty_or_nonempty (univ.sigma f) with he | hne
  · convert! h0 using 1
    simpa [funext_iff] using he
  · rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩
    rc

Depends on / 依赖: Finset, Finset.strongInductionOn, H_ex, clear_value, convert, eq_empty_or_nonempty, funext_iff, generalizing, insert, nonempty_fintype, notMem_erase, sigma_nonempty, strongInductionOn, univ.sigma, update, update_self, x_mem
-/
theorem induction_on_pi_of_choice (r : forall i, α i -> Finset (α i) -> Prop)
    (H_ex : forall (i) (s : Finset (α i)), s.Nonempty -> exists x in s, r i x (s.erase x))
    {p : (forall i, Finset (α i)) -> Prop} (f : forall i, Finset (α i)) (h0 : p fun _ => ∅)
    (step :
      forall (g : forall i, Finset (α i)) (i : ι) (x : α i),
        r i x (g i) -> p g -> p (update g i (insert x (g i)))) :
    p f := by
  cases nonempty_fintype ι
  induction hs : univ.sigma f using Finset.strongInductionOn generalizing f with | _ s ihs
  subst s
  rcases eq_empty_or_nonempty (univ.sigma f) with he | hne
  · convert! h0 using 1
    simpa [funext_iff] using he
  · rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩
    rcases H_ex i (f i) hi with ⟨x, x_mem, hr⟩
    set g := update f i ((f i).erase x) with hg
    clear_value g
    have hx' : x ∉ g i := by
      rw [hg]; rw [update_self]
      apply notMem_erase
    rw [show f = update g i (insert x (g i)) by
      rw [hg]; rw [update_idem]; rw [update_self]; rw [insert_erase x_mem]; rw [update_eq_self]] at hr ihs ⊢
    clear hg
    rw [update_self]; rw [erase_insert hx'] at hr
    refine step _ _ _ hr (ihs (univ.sigma g) ?_ _ rfl)
    rw [ssubset_iff_of_subset (sigma_mono (Subset.refl _) _)]
    exacts [⟨⟨i, x⟩, mem_sigma.2 ⟨mem_univ _, by simp⟩, by simp [hx']⟩,
      (@le_update_iff _ _ _ _ g g i _).2 ⟨subset_insert _ _, fun _ _ => le_rfl⟩]

/--
theorem `induction_on_pi` / 定理 `induction_on_pi`

English:
theorem induction_on_pi
  statement: {p : (forall i, Finset (α i)) -> Prop} (f : forall i, Finset (α i)) (h0 : p fun _ => ∅)
  proof: induction_on_pi_of_choice (fun _ x s => x ∉ s) (fun _ s ⟨x, hx⟩ => ⟨x, hx, notMem_erase x s⟩) f
    h0 step

中文:
定理 induction_on_pi
  结论: {p : (对任意 i, 有限集 (α i)) -> 命题} (f : 对任意 i, 有限集 (α i)) (h0 : p fun _ => ∅)
  证明: induction_on_pi_of_choice (fun _ x s => x ∉ s) (fun _ s ⟨x, hx⟩ => ⟨x, hx, notMem_erase x s⟩) f
    h0 step

Depends on / 依赖: induction_on_pi_of_choice, notMem_erase
-/
theorem induction_on_pi {p : (forall i, Finset (α i)) -> Prop} (f : forall i, Finset (α i)) (h0 : p fun _ => ∅)
    (step : forall (g : forall i, Finset (α i)) (i : ι), forall x ∉ g i, p g -> p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s => x ∉ s) (fun _ s ⟨x, hx⟩ => ⟨x, hx, notMem_erase x s⟩) f
    h0 step

/--
theorem `induction_on_pi_max` / 定理 `induction_on_pi_max`

English:
theorem induction_on_pi_max
  statement: [forall i, LinearOrder (α i)] {p : (forall i, Finset (α i)) -> Prop}
  proof: induction_on_pi_of_choice (fun _ x s => forall y in s, y < x)
    (fun _ s hs => ⟨s.max' hs, s.max'_mem hs, fun _ => s.lt_max'_of_mem_erase_max' _⟩) f h0 step

中文:
定理 induction_on_pi_max
  结论: [对任意 i, 线性序 (α i)] {p : (对任意 i, 有限集 (α i)) -> 命题}
  证明: induction_on_pi_of_choice (fun _ x s => forall y in s, y < x)
    (fun _ s hs => ⟨s.max' hs, s.max'_mem hs, fun _ => s.lt_max'_of_mem_erase_max' _⟩) f h0 step

Depends on / 依赖: _mem, _of_mem_erase_max, induction_on_pi_of_choice, lt_max, s.lt_max, s.max
-/
theorem induction_on_pi_max [forall i, LinearOrder (α i)] {p : (forall i, Finset (α i)) -> Prop}
    (f : forall i, Finset (α i)) (h0 : p fun _ => ∅)
    (step :
      forall (g : forall i, Finset (α i)) (i : ι) (x : α i),
        (forall y in g i, y < x) -> p g -> p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_of_choice (fun _ x s => forall y in s, y < x)
    (fun _ s hs => ⟨s.max' hs, s.max'_mem hs, fun _ => s.lt_max'_of_mem_erase_max' _⟩) f h0 step

/--
theorem `induction_on_pi_min` / 定理 `induction_on_pi_min`

English:
theorem induction_on_pi_min
  statement: [forall i, LinearOrder (α i)] {p : (forall i, Finset (α i)) -> Prop}
  proof: induction_on_pi_max (α := fun i => (α i)ᵒᵈ) _ h0 step

中文:
定理 induction_on_pi_min
  结论: [对任意 i, 线性序 (α i)] {p : (对任意 i, 有限集 (α i)) -> 命题}
  证明: induction_on_pi_max (α := fun i => (α i)ᵒᵈ) _ h0 step

Depends on / 依赖: induction_on_pi_max
-/
theorem induction_on_pi_min [forall i, LinearOrder (α i)] {p : (forall i, Finset (α i)) -> Prop}
    (f : forall i, Finset (α i)) (h0 : p fun _ => ∅)
    (step :
      forall (g : forall i, Finset (α i)) (i : ι) (x : α i),
        (forall y in g i, x < y) -> p g -> p (update g i (insert x (g i)))) :
    p f :=
  induction_on_pi_max (α := fun i => (α i)ᵒᵈ) _ h0 step

end Finset
