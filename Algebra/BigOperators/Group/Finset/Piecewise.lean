/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Piecewise

/-!
# Interaction of big operators with piecewise functions

This file proves lemmas on the sum and product of piecewise functions, including `ite` and `dite`.
-/

public section

variable {ι κ M β γ : Type*} {s : Finset ι}

namespace Finset

section CommMonoid

variable [CommMonoid M]

@[to_additive]
/--
theorem `prod_apply_dite` / 定理 `prod_apply_dite`

English:
theorem prod_apply_dite
  statement: {p : ι -> Prop} [DecidablePred p]
  proof: calc
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x in s with p x, h (if hx : p x then f x hx else g x hx)) *
          ∏ x in s with ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x : {x in s | p x}, h (if hx : 

中文:
定理 prod_apply_dite
  结论: {p : ι -> 命题} [DecidablePred p]
  证明: calc
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x in s with p x, h (if hx : p x then f x hx else g x hx)) *
          ∏ x in s with ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x : {x in s | p x}, h (if hx : 

Depends on / 依赖: mem_filt, prod_attach, prod_filter_mul_prod_filter_not
-/
theorem prod_apply_dite {p : ι -> Prop} [DecidablePred p]
    [DecidablePred fun x => ¬p x] (f : forall x : ι, p x -> γ) (g : forall x : ι, ¬p x -> γ) (h : γ -> M) :
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x : {x in s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x in s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
  calc
    (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
        (∏ x in s with p x, h (if hx : p x then f x hx else g x hx)) *
          ∏ x in s with ¬p x, h (if hx : p x then f x hx else g x hx) :=
      (prod_filter_mul_prod_filter_not s p _).symm
    _ = (∏ x : {x in s | p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
          ∏ x : {x in s | ¬p x}, h (if hx : p x.1 then f x.1 hx else g x.1 hx) :=
      congr_arg₂ _ (prod_attach _ _).symm (prod_attach _ _).symm
    _ = (∏ x : {x in s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
          ∏ x : {x in s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
      congr_arg₂ _ (prod_congr rfl fun x _hx =>
        congr_arg h (dif_pos <| by simpa using (mem_filter.mp x.2).2))
        (prod_congr rfl fun x _hx => congr_arg h (dif_neg <| by simpa using (mem_filter.mp x.2).2))

@[to_additive]
/--
theorem `prod_apply_ite` / 定理 `prod_apply_ite`

English:
theorem prod_apply_ite
  statement: {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ)
  proof: (prod_apply_dite _ _ _).trans congr_arg₂ _ (prod_attach _ (h ∘ f)) (prod_attach _ (h ∘ g))

@[to_additive]

中文:
定理 prod_apply_ite
  结论: {s : Finset ι} {p : ι -> 命题} [DecidablePred p] (f g : ι -> γ)
  证明: (prod_apply_dite _ _ _).trans congr_arg₂ _ (prod_attach _ (h ∘ f)) (prod_attach _ (h ∘ g))

@[to_additive]

Depends on / 依赖: prod_apply_dite, prod_attach
-/
theorem prod_apply_ite {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ)
    (h : γ -> M) :
    (∏ x in s, h (if p x then f x else g x)) =
      (∏ x in s with p x, h (f x)) * ∏ x in s with ¬p x, h (g x) :=
(prod_apply_dite _ _ _).trans congr_arg₂ _ (prod_attach _ (h ∘ f)) (prod_attach _ (h ∘ g))

@[to_additive]
/--
theorem `prod_dite` / 定理 `prod_dite`

English:
theorem prod_dite
  statement: {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f : forall x : ι, p x -> M)
  proof: by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]

中文:
定理 prod_dite
  结论: {s : Finset ι} {p : ι -> 命题} [DecidablePred p] (f : 对任意 x : ι, p x -> M)
  证明: by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]

Depends on / 依赖: prod_apply_dite
-/
theorem prod_dite {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f : forall x : ι, p x -> M)
    (g : forall x : ι, ¬p x -> M) :
    ∏ x in s, (if hx : p x then f x hx else g x hx) =
      (∏ x : {x in s | p x}, f x.1 (by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x in s | ¬p x}, g x.1 (by simpa using (mem_filter.mp x.2).2) := by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]
/--
theorem `prod_ite` / 定理 `prod_ite`

English:
theorem prod_ite
  given: {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f g : ι -> M)
  proof: by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]

中文:
定理 prod_ite
  条件: {s : Finset ι} {p : ι -> 命题} [DecidablePred p] (f g : ι -> M)
  证明: by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]

Depends on / 依赖: prod_apply_ite
-/
theorem prod_ite {s : Finset ι} {p : ι -> Prop} [DecidablePred p] (f g : ι -> M) :
    ∏ x in s, (if p x then f x else g x) = (∏ x in s with p x, f x) * ∏ x in s with ¬p x, g x := by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]
/--
lemma `prod_dite_of_false` / 引理 `prod_dite_of_false`

English:
lemma prod_dite_of_false
  statement: {p : ι -> Prop} [DecidablePred p] (h : forall i in s, ¬ p i)
  proof: by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ => x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]

中文:
引理 prod_dite_of_false
  结论: {p : ι -> 命题} [DecidablePred p] (h : 对任意 i in s, ¬ p i)
  证明: by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ => x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]

Depends on / 依赖: prod_bij
-/
lemma prod_dite_of_false {p : ι -> Prop} [DecidablePred p] (h : forall i in s, ¬ p i)
    (f : forall i, p i -> M) (g : forall i, ¬ p i -> M) :
    ∏ i in s, (if hi : p i then f i hi else g i hi) = ∏ i : s, g i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ => x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[to_additive]
/--
lemma `prod_ite_of_false` / 引理 `prod_ite_of_false`

English:
lemma prod_ite_of_false
  given: {p : ι -> Prop} [DecidablePred p] (h : forall x in s, ¬p x) (f g : ι -> M)
  proof: (prod_dite_of_false h _ _).trans (prod_attach _ _)

@[to_additive]

中文:
引理 prod_ite_of_false
  条件: {p : ι -> 命题} [DecidablePred p] (h : 对任意 x in s, ¬p x) (f g : ι -> M)
  证明: (prod_dite_of_false h _ _).trans (prod_attach _ _)

@[to_additive]

Depends on / 依赖: prod_attach, prod_dite_of_false
-/
lemma prod_ite_of_false {p : ι -> Prop} [DecidablePred p] (h : forall x in s, ¬p x) (f g : ι -> M) :
    ∏ x in s, (if p x then f x else g x) = ∏ x in s, g x :=
  (prod_dite_of_false h _ _).trans (prod_attach _ _)

@[to_additive]
/--
lemma `prod_dite_of_true` / 引理 `prod_dite_of_true`

English:
lemma prod_dite_of_true
  statement: {p : ι -> Prop} [DecidablePred p] (h : forall i in s, p i) (f : forall i, p i -> M)
  proof: by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ => x) ?_ ?_ ?_ ?_ ?_ <;> grind

@[to_additive]

中文:
引理 prod_dite_of_true
  结论: {p : ι -> 命题} [DecidablePred p] (h : 对任意 i in s, p i) (f : 对任意 i, p i -> M)
  证明: by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ => x) ?_ ?_ ?_ ?_ ?_ <;> grind

@[to_additive]

Depends on / 依赖: prod_bij
-/
lemma prod_dite_of_true {p : ι -> Prop} [DecidablePred p] (h : forall i in s, p i) (f : forall i, p i -> M)
    (g : forall i, ¬ p i -> M) :
    ∏ i in s, (if hi : p i then f i hi else g i hi) = ∏ i : s, f i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ => x) ?_ ?_ ?_ ?_ ?_ <;> grind

@[to_additive]
/--
lemma `prod_ite_of_true` / 引理 `prod_ite_of_true`

English:
lemma prod_ite_of_true
  given: {p : ι -> Prop} [DecidablePred p] (h : forall x in s, p x) (f g : ι -> M)
  proof: (prod_dite_of_true h _ _).trans (prod_attach _ _)

@[to_additive]

中文:
引理 prod_ite_of_true
  条件: {p : ι -> 命题} [DecidablePred p] (h : 对任意 x in s, p x) (f g : ι -> M)
  证明: (prod_dite_of_true h _ _).trans (prod_attach _ _)

@[to_additive]

Depends on / 依赖: prod_attach, prod_dite_of_true
-/
lemma prod_ite_of_true {p : ι -> Prop} [DecidablePred p] (h : forall x in s, p x) (f g : ι -> M) :
    ∏ x in s, (if p x then f x else g x) = ∏ x in s, f x :=
  (prod_dite_of_true h _ _).trans (prod_attach _ _)

@[to_additive]
/--
theorem `prod_apply_ite_of_false` / 定理 `prod_apply_ite_of_false`

English:
theorem prod_apply_ite_of_false
  statement: {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ) (k : γ -> M)
  proof: by
  simp_rw [apply_ite k]
  exact prod_ite_of_false h _ _

@[to_additive]

中文:
定理 prod_apply_ite_of_false
  结论: {p : ι -> 命题} [DecidablePred p] (f g : ι -> γ) (k : γ -> M)
  证明: by
  simp_rw [apply_ite k]
  exact prod_ite_of_false h _ _

@[to_additive]

Depends on / 依赖: apply_ite, prod_ite_of_false, simp_rw
-/
theorem prod_apply_ite_of_false {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ) (k : γ -> M)
    (h : forall x in s, ¬p x) : (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (g x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_false h _ _

@[to_additive]
/--
theorem `prod_apply_ite_of_true` / 定理 `prod_apply_ite_of_true`

English:
theorem prod_apply_ite_of_true
  statement: {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ) (k : γ -> M)
  proof: by
  simp_rw [apply_ite k]
  exact prod_ite_of_true h _ _

@[to_additive (attr := simp)]

中文:
定理 prod_apply_ite_of_true
  结论: {p : ι -> 命题} [DecidablePred p] (f g : ι -> γ) (k : γ -> M)
  证明: by
  simp_rw [apply_ite k]
  exact prod_ite_of_true h _ _

@[to_additive (attr := simp)]

Depends on / 依赖: apply_ite, prod_ite_of_true, simp_rw
-/
theorem prod_apply_ite_of_true {p : ι -> Prop} [DecidablePred p] (f g : ι -> γ) (k : γ -> M)
    (h : forall x in s, p x) : (∏ x in s, k (if p x then f x else g x)) = ∏ x in s, k (f x) := by
  simp_rw [apply_ite k]
  exact prod_ite_of_true h _ _

@[to_additive (attr := simp)]
/--
theorem `prod_ite_mem` / 定理 `prod_ite_mem`

English:
theorem prod_ite_mem
  given: [DecidableEq ι] (s t : Finset ι) (f : ι -> M)
  proof: by
  rw [← Finset.prod_filter]; rw [Finset.filter_mem_eq_inter]

@[to_additive]

中文:
定理 prod_ite_mem
  条件: [DecidableEq ι] (s t : Finset ι) (f : ι -> M)
  证明: by
  rw [← Finset.prod_filter]; rw [Finset.filter_mem_eq_inter]

@[to_additive]

Depends on / 依赖: Finset, Finset.filter_mem_eq_inter, Finset.prod_filter, filter_mem_eq_inter, prod_filter
-/
theorem prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : ι -> M) :
    ∏ i in s, (if i in t then f i else 1) = ∏ i in s inter t, f i := by
  rw [← Finset.prod_filter]; rw [Finset.filter_mem_eq_inter]

@[to_additive]
/--
lemma `prod_attach_eq_prod_dite` / 引理 `prod_attach_eq_prod_dite`

English:
lemma prod_attach_eq_prod_dite
  given: [Fintype ι] (s : Finset ι) (f : s -> M) [DecidablePred (· in s)]
  proof: by
  rw [Finset.prod_dite]; rw [Finset.univ_eq_attach]; rw [Finset.prod_const_one]; rw [mul_one]
  congr
  · simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

@[to_additive (attr := simp)]

中文:
引理 prod_attach_eq_prod_dite
  条件: [Fintype ι] (s : Finset ι) (f : s -> M) [DecidablePred (· in s)]
  证明: by
  rw [Finset.prod_dite]; rw [Finset.univ_eq_attach]; rw [Finset.prod_const_one]; rw [mul_one]
  congr
  · simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_const_one, Finset.prod_dite, Finset.univ_eq_attach, Function, Function.hfunext, Subtype, Subtype.heq_iff_coe_eq, contextual, heq_iff_coe_eq, hfunext, mul_one, prod_const_one, prod_dite, univ_eq_attach
-/
lemma prod_attach_eq_prod_dite [Fintype ι] (s : Finset ι) (f : s -> M) [DecidablePred (· in s)] :
    ∏ i in s.attach, f i = ∏ i, if h : i in s then f ⟨i, h⟩ else 1 := by
  rw [Finset.prod_dite]; rw [Finset.univ_eq_attach]; rw [Finset.prod_const_one]; rw [mul_one]
  congr
  · simp
  · ext; simp
  · apply Function.hfunext <;> simp +contextual [Subtype.heq_iff_coe_eq]

@[to_additive (attr := simp)]
/--
theorem `prod_dite_eq` / 定理 `prod_dite_eq`

English:
theorem prod_dite_eq
  given: [DecidableEq ι] (s : Finset ι) (a : ι) (b : forall x : ι, a = x -> M)
  proof: by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]

中文:
定理 prod_dite_eq
  条件: [DecidableEq ι] (s : Finset ι) (a : ι) (b : 对任意 x : ι, a = x -> M)
  证明: by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_eq_one, Finset.prod_eq_single, dif_neg, dif_pos, h.symm, prod_eq_one, prod_eq_single, split_ifs
-/
theorem prod_dite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : forall x : ι, a = x -> M) :
    ∏ x in s, (if h : a = x then b x h else 1) = ite (a in s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]
/--
theorem `prod_dite_eq'` / 定理 `prod_dite_eq'`

English:
theorem prod_dite_eq'
  given: [DecidableEq ι] (s : Finset ι) (a : ι) (b : forall x : ι, x = a -> M)
  proof: by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]

中文:
定理 prod_dite_eq'
  条件: [DecidableEq ι] (s : Finset ι) (a : ι) (b : 对任意 x : ι, x = a -> M)
  证明: by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]

Depends on / 依赖: Finset, Finset.prod_eq_one, Finset.prod_eq_single, dif_neg, dif_pos, prod_eq_one, prod_eq_single, split_ifs
-/
theorem prod_dite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : forall x : ι, x = a -> M) :
    ∏ x in s, (if h : x = a then b x h else 1) = ite (a in s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intro _ _ h
      rw [dif_neg]
      exact h
    · simp [h]
  · rw [Finset.prod_eq_one]
    grind

@[to_additive (attr := simp)]
/--
theorem `prod_ite_eq` / 定理 `prod_ite_eq`

English:
theorem prod_ite_eq
  given: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M)
  proof: prod_dite_eq s a fun x _ => b x

中文:
定理 prod_ite_eq
  条件: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M)
  证明: prod_dite_eq s a fun x _ => b x

Depends on / 依赖: prod_dite_eq
-/
theorem prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) :
    (∏ x in s, ite (a = x) (b x) 1) = ite (a in s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `Finset.prod_ite_eq` is that the arguments to `Eq` are swapped. -/
@[to_additive (attr := simp) /-- A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped. -/]
/--
theorem `prod_ite_eq'` / 定理 `prod_ite_eq'`

English:
theorem prod_ite_eq'
  given: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M)
  proof: prod_dite_eq' s a fun x _ => b x

@[to_additive]

中文:
定理 prod_ite_eq'
  条件: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M)
  证明: prod_dite_eq' s a fun x _ => b x

@[to_additive]

Depends on / 依赖: prod_dite_eq
-/
theorem prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) :
    (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[to_additive]
/--
theorem `prod_ite_eq_of_mem` / 定理 `prod_ite_eq_of_mem`

English:
theorem prod_ite_eq_of_mem
  given: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h : a in s)
  proof: by
  simp only [prod_ite_eq, if_pos h]

中文:
定理 prod_ite_eq_of_mem
  条件: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h : a in s)
  证明: by
  simp only [prod_ite_eq, if_pos h]

Depends on / 依赖: if_pos, prod_ite_eq
-/
theorem prod_ite_eq_of_mem [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h : a in s) :
    (∏ x in s, if a = x then b x else 1) = b a := by
  simp only [prod_ite_eq, if_pos h]

/-- The difference with `Finset.prod_ite_eq_of_mem` is that the arguments to `Eq` are swapped. -/
@[to_additive]
/--
theorem `prod_ite_eq_of_mem'` / 定理 `prod_ite_eq_of_mem'`

English:
theorem prod_ite_eq_of_mem'
  given: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h : a in s)
  proof: by
  simp only [prod_ite_eq', if_pos h]

@[to_additive (attr := simp)]

中文:
定理 prod_ite_eq_of_mem'
  条件: [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h : a in s)
  证明: by
  simp only [prod_ite_eq', if_pos h]

@[to_additive (attr := simp)]

Depends on / 依赖: if_pos, prod_ite_eq
-/
theorem prod_ite_eq_of_mem' [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι -> M) (h : a in s) :
    (∏ x in s, if x = a then b x else 1) = b a := by
  simp only [prod_ite_eq', if_pos h]

@[to_additive (attr := simp)]
/--
theorem `prod_pi_mulSingle'` / 定理 `prod_pi_mulSingle'`

English:
theorem prod_pi_mulSingle'
  given: [DecidableEq ι] (a : ι) (x : M) (s : Finset ι)
  proof: prod_dite_eq' _ _ _

@[to_additive (attr := simp)]

中文:
定理 prod_pi_mulSingle'
  条件: [DecidableEq ι] (a : ι) (x : M) (s : Finset ι)
  证明: prod_dite_eq' _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: prod_dite_eq
-/
theorem prod_pi_mulSingle' [DecidableEq ι] (a : ι) (x : M) (s : Finset ι) :
    ∏ a' in s, Pi.mulSingle a x a' = if a in s then x else 1 :=
  prod_dite_eq' _ _ _

@[to_additive (attr := simp)]
/--
theorem `prod_pi_mulSingle` / 定理 `prod_pi_mulSingle`

English:
theorem prod_pi_mulSingle
  statement: {M : ι -> Type*} [DecidableEq ι] [forall a, CommMonoid (M a)] (a : ι)
  proof: prod_dite_eq _ _ _

@[to_additive]

中文:
定理 prod_pi_mulSingle
  结论: {M : ι -> 类型} [DecidableEq ι] [对任意 a, CommMonoid (M a)] (a : ι)
  证明: prod_dite_eq _ _ _

@[to_additive]

Depends on / 依赖: prod_dite_eq
-/
theorem prod_pi_mulSingle {M : ι -> Type*} [DecidableEq ι] [forall a, CommMonoid (M a)] (a : ι)
    (f : forall a, M a) (s : Finset ι) :
    (∏ a' in s, Pi.mulSingle a' (f a') a) = if a in s then f a else 1 :=
  prod_dite_eq _ _ _

@[to_additive]
/--
theorem `prod_piecewise` / 定理 `prod_piecewise`

English:
theorem prod_piecewise
  given: [DecidableEq ι] (s t : Finset ι) (f g : ι -> M)
  proof: by
  simp only [piecewise]
  rw [prod_ite]; rw [filter_mem_eq_inter]; rw [← sdiff_eq_filter]

@[to_additive]

中文:
定理 prod_piecewise
  条件: [DecidableEq ι] (s t : Finset ι) (f g : ι -> M)
  证明: by
  simp only [piecewise]
  rw [prod_ite]; rw [filter_mem_eq_inter]; rw [← sdiff_eq_filter]

@[to_additive]

Depends on / 依赖: filter_mem_eq_inter, piecewise, prod_ite, sdiff_eq_filter
-/
theorem prod_piecewise [DecidableEq ι] (s t : Finset ι) (f g : ι -> M) :
    (∏ x in s, (t.piecewise f g) x) = (∏ x in s inter t, f x) * ∏ x in s \ t, g x := by
  simp only [piecewise]
  rw [prod_ite]; rw [filter_mem_eq_inter]; rw [← sdiff_eq_filter]

@[to_additive]
/--
theorem `prod_inter_mul_prod_sdiff` / 定理 `prod_inter_mul_prod_sdiff`

English:
theorem prod_inter_mul_prod_sdiff
  given: [DecidableEq ι] (s t : Finset ι) (f : ι -> M)
  proof: by
  convert! (s.prod_piecewise t f f).symm
  simp +unfoldPartialApp [Finset.piecewise]

@[deprecated (since := "2026-06-03")] alias prod_inter_mul_prod_diff := prod_inter_mul_prod_sdiff

@[to_additive]

中文:
定理 prod_inter_mul_prod_sdiff
  条件: [DecidableEq ι] (s t : Finset ι) (f : ι -> M)
  证明: by
  convert! (s.prod_piecewise t f f).symm
  simp +unfoldPartialApp [Finset.piecewise]

@[deprecated (since := "2026-06-03")] alias prod_inter_mul_prod_diff := prod_inter_mul_prod_sdiff

@[to_additive]

Depends on / 依赖: Finset, Finset.piecewise, convert, piecewise, prod_piecewise, s.prod_piecewise, unfoldPartialApp
-/
theorem prod_inter_mul_prod_sdiff [DecidableEq ι] (s t : Finset ι) (f : ι -> M) :
    (∏ x in s inter t, f x) * ∏ x in s \ t, f x = ∏ x in s, f x := by
  convert! (s.prod_piecewise t f f).symm
  simp +unfoldPartialApp [Finset.piecewise]

@[deprecated (since := "2026-06-03")] alias prod_inter_mul_prod_diff := prod_inter_mul_prod_sdiff

@[to_additive]
/--
theorem `prod_eq_mul_prod_sdiff_singleton` / 定理 `prod_eq_mul_prod_sdiff_singleton`

English:
theorem prod_eq_mul_prod_sdiff_singleton
  statement: [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι -> M)
  proof: by
  by_cases hs : i in s
  · convert! (s.prod_inter_mul_prod_sdiff { i } f).symm
    simp [hs]
  · simp_all only [not_false_eq_true, forall_const, one_mul]
    apply Finset.prod_congr <;> aesop

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton := prod_eq_mul_prod_sdiff_si

中文:
定理 prod_eq_mul_prod_sdiff_singleton
  结论: [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι -> M)
  证明: by
  by_cases hs : i in s
  · convert! (s.prod_inter_mul_prod_sdiff { i } f).symm
    simp [hs]
  · simp_all only [not_false_eq_true, forall_const, one_mul]
    apply Finset.prod_congr <;> aesop

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton := prod_eq_mul_prod_sdiff_si

Depends on / 依赖: Finset, Finset.prod_congr, convert, forall_const, not_false_eq_true, one_mul, prod_congr, prod_inter_mul_prod_sdiff, s.prod_inter_mul_prod_sdiff
-/
theorem prod_eq_mul_prod_sdiff_singleton [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι -> M)
    (h : i ∉ s -> f i = 1) : ∏ x in s, f x = f i * ∏ x in s \ {i}, f x := by
  by_cases hs : i in s
  · convert! (s.prod_inter_mul_prod_sdiff { i } f).symm
    simp [hs]
  · simp_all only [not_false_eq_true, forall_const, one_mul]
    apply Finset.prod_congr <;> aesop

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton := prod_eq_mul_prod_sdiff_singleton

@[to_additive]
/--
theorem `prod_eq_mul_prod_sdiff_singleton_of_mem` / 定理 `prod_eq_mul_prod_sdiff_singleton_of_mem`

English:
theorem prod_eq_mul_prod_sdiff_singleton_of_mem
  statement: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s)
  proof: prod_eq_mul_prod_sdiff_singleton _ _ (by simp_all)

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton_of_mem := prod_eq_mul_prod_sdiff_singleton_of_mem

@[to_additive]

中文:
定理 prod_eq_mul_prod_sdiff_singleton_of_mem
  结论: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s)
  证明: prod_eq_mul_prod_sdiff_singleton _ _ (by simp_all)

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton_of_mem := prod_eq_mul_prod_sdiff_singleton_of_mem

@[to_additive]

Depends on / 依赖: prod_eq_mul_prod_sdiff_singleton
-/
theorem prod_eq_mul_prod_sdiff_singleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s)
    (f : ι -> M) : ∏ x in s, f x = f i * ∏ x in s \ {i}, f x :=
  prod_eq_mul_prod_sdiff_singleton _ _ (by simp_all)

@[deprecated (since := "2026-06-03")]
alias prod_eq_mul_prod_diff_singleton_of_mem := prod_eq_mul_prod_sdiff_singleton_of_mem

@[to_additive]
/--
theorem `prod_eq_prod_sdiff_singleton_mul` / 定理 `prod_eq_prod_sdiff_singleton_mul`

English:
theorem prod_eq_prod_sdiff_singleton_mul
  statement: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s)
  proof: by
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem h]; rw [mul_comm]

@[deprecated (since := "2026-06-03")]
alias prod_eq_prod_diff_singleton_mul := prod_eq_prod_sdiff_singleton_mul

@[to_additive]

中文:
定理 prod_eq_prod_sdiff_singleton_mul
  结论: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s)
  证明: by
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem h]; rw [mul_comm]

@[deprecated (since := "2026-06-03")]
alias prod_eq_prod_diff_singleton_mul := prod_eq_prod_sdiff_singleton_mul

@[to_additive]

Depends on / 依赖: mul_comm, prod_eq_mul_prod_sdiff_singleton_of_mem
-/
theorem prod_eq_prod_sdiff_singleton_mul [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s)
    (f : ι -> M) : ∏ x in s, f x = (∏ x in s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem h]; rw [mul_comm]

@[deprecated (since := "2026-06-03")]
alias prod_eq_prod_diff_singleton_mul := prod_eq_prod_sdiff_singleton_mul

@[to_additive]
/--
theorem `_root_.Fintype.prod_eq_mul_prod_compl` / 定理 `_root_.Fintype.prod_eq_mul_prod_compl`

English:
theorem _root_.Fintype.prod_eq_mul_prod_compl
  given: [DecidableEq ι] [Fintype ι] (a : ι) (f : ι -> M)
  proof: prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ a) f

@[to_additive]

中文:
定理 _root_.Fintype.prod_eq_mul_prod_compl
  条件: [DecidableEq ι] [Fintype ι] (a : ι) (f : ι -> M)
  证明: prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ a) f

@[to_additive]

Depends on / 依赖: mem_univ, prod_eq_mul_prod_sdiff_singleton_of_mem
-/
theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq ι] [Fintype ι] (a : ι) (f : ι -> M) :
    ∏ i, f i = f a * ∏ i in {a}ᶜ, f i :=
  prod_eq_mul_prod_sdiff_singleton_of_mem (mem_univ a) f

@[to_additive]
/--
theorem `_root_.Fintype.prod_eq_prod_compl_mul` / 定理 `_root_.Fintype.prod_eq_prod_compl_mul`

English:
theorem _root_.Fintype.prod_eq_prod_compl_mul
  given: [DecidableEq ι] [Fintype ι] (a : ι) (f : ι -> M)
  proof: prod_eq_prod_sdiff_singleton_mul (mem_univ a) f

中文:
定理 _root_.Fintype.prod_eq_prod_compl_mul
  条件: [DecidableEq ι] [Fintype ι] (a : ι) (f : ι -> M)
  证明: prod_eq_prod_sdiff_singleton_mul (mem_univ a) f

Depends on / 依赖: mem_univ, prod_eq_prod_sdiff_singleton_mul
-/
theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq ι] [Fintype ι] (a : ι) (f : ι -> M) :
    ∏ i, f i = (∏ i in {a}ᶜ, f i) * f a :=
  prod_eq_prod_sdiff_singleton_mul (mem_univ a) f

/--
theorem `dvd_prod_of_mem` / 定理 `dvd_prod_of_mem`

English:
theorem dvd_prod_of_mem
  given: (f : ι -> M) {a : ι} {s : Finset ι} (ha : a in s)
  statement: f a ∣ ∏ i in s, f i
  proof: by
  classical
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem ha]
    exact dvd_mul_right _ _

@[to_additive]

中文:
定理 dvd_prod_of_mem
  条件: (f : ι -> M) {a : ι} {s : Finset ι} (ha : a in s)
  结论: f a ∣ ∏ i in s, f i
  证明: by
  classical
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem ha]
    exact dvd_mul_right _ _

@[to_additive]

Depends on / 依赖: Finset, Finset.prod_eq_mul_prod_sdiff_singleton_of_mem, classical, dvd_mul_right, prod_eq_mul_prod_sdiff_singleton_of_mem
-/
theorem dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset ι} (ha : a in s) : f a ∣ ∏ i in s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem ha]
    exact dvd_mul_right _ _

@[to_additive]
/--
theorem `prod_update_of_notMem` / 定理 `prod_update_of_notMem`

English:
theorem prod_update_of_notMem
  statement: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∉ s) (f : ι -> M)
  proof: by
  apply prod_congr rfl
  intro j hj
  have : j != i := by
    rintro rfl
    exact h hj
  simp [this]

@[to_additive]

中文:
定理 prod_update_of_notMem
  结论: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∉ s) (f : ι -> M)
  证明: by
  apply prod_congr rfl
  intro j hj
  have : j != i := by
    rintro rfl
    exact h hj
  simp [this]

@[to_additive]

Depends on / 依赖: prod_congr
-/
theorem prod_update_of_notMem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∉ s) (f : ι -> M)
    (b : M) : ∏ x in s, Function.update f i b x = ∏ x in s, f x := by
  apply prod_congr rfl
  intro j hj
  have : j != i := by
    rintro rfl
    exact h hj
  simp [this]

@[to_additive]
/--
theorem `prod_update_of_mem` / 定理 `prod_update_of_mem`

English:
theorem prod_update_of_mem
  given: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M) (b : M)
  proof: by
  rw [update_eq_piecewise]; rw [prod_piecewise]
  simp [h]

中文:
定理 prod_update_of_mem
  条件: [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M) (b : M)
  证明: by
  rw [update_eq_piecewise]; rw [prod_piecewise]
  simp [h]

Depends on / 依赖: prod_piecewise, update_eq_piecewise
-/
theorem prod_update_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M) (b : M) :
    ∏ x in s, Function.update f i b x = b * ∏ x in s \ singleton i, f x := by
  rw [update_eq_piecewise]; rw [prod_piecewise]
  simp [h]

/-- See also `Finset.prod_ite_zero`. -/
@[to_additive /-- See also `Finset.sum_boole`. -/]
/--
theorem `prod_ite_one` / 定理 `prod_ite_one`

English:
theorem prod_ite_one
  statement: (s : Finset ι) (p : ι -> Prop) [DecidablePred p]
  proof: by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi]; rw [if_pos hpi]
exact fun j hj hji => if_neg fun hpj => hji h _ hj _ hi hpj hpi
  · push Not at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[to_additive sum_boole_nsmul]

中文:
定理 prod_ite_one
  结论: (s : Finset ι) (p : ι -> 命题) [DecidablePred p]
  证明: by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi]; rw [if_pos hpi]
exact fun j hj hji => if_neg fun hpj => hji h _ hj _ hi hpj hpi
  · push Not at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[to_additive sum_boole_nsmul]

Depends on / 依赖: if_neg, if_pos, prod_eq_one, prod_eq_single_of_mem, split_ifs
-/
theorem prod_ite_one (s : Finset ι) (p : ι -> Prop) [DecidablePred p]
    (h : forall i in s, forall j in s, p i -> p j -> i = j) (a : M) :
    ∏ i in s, ite (p i) a 1 = ite (exists i in s, p i) a 1 := by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi]; rw [if_pos hpi]
exact fun j hj hji => if_neg fun hpj => hji h _ hj _ hi hpj hpi
  · push Not at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[to_additive sum_boole_nsmul]
/--
theorem `prod_pow_boole` / 定理 `prod_pow_boole`

English:
theorem prod_pow_boole
  given: [DecidableEq ι] (s : Finset ι) (f : ι -> M) (a : ι)
  proof: by simp

@[to_additive]

中文:
定理 prod_pow_boole
  条件: [DecidableEq ι] (s : Finset ι) (f : ι -> M) (a : ι)
  证明: by simp

@[to_additive]
-/
theorem prod_pow_boole [DecidableEq ι] (s : Finset ι) (f : ι -> M) (a : ι) :
    (∏ x in s, f x ^ ite (a = x) 1 0) = ite (a in s) (f a) 1 := by simp

@[to_additive]
/--
lemma `prod_eq_prod_iff_single` / 引理 `prod_eq_prod_iff_single`

English:
lemma prod_eq_prod_iff_single
  statement: [IsRightCancelMul M] {f g : ι -> M} {i : ι} (hi : i in s)
  proof: by
  classical
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]; rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]; rw [prod_congr rfl (by simpa)]; rw [mul_left_inj]

中文:
引理 prod_eq_prod_iff_single
  结论: [IsRightCancelMul M] {f g : ι -> M} {i : ι} (hi : i in s)
  证明: by
  classical
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]; rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]; rw [prod_congr rfl (by simpa)]; rw [mul_left_inj]

Depends on / 依赖: classical, mul_left_inj, prod_congr, prod_eq_mul_prod_sdiff_singleton_of_mem
-/
lemma prod_eq_prod_iff_single [IsRightCancelMul M] {f g : ι -> M} {i : ι} (hi : i in s)
    (hfg : forall j in s, j != i -> f j = g j) : ∏ j in s, f j = ∏ j in s, g j ↔ f i = g i := by
  classical
  rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]; rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi]; rw [prod_congr rfl (by simpa)]; rw [mul_left_inj]

end CommMonoid

/--
lemma `card_filter` / 引理 `card_filter`

English:
lemma card_filter
  given: (p) [DecidablePred p] (s : Finset ι)
  proof: by simp [sum_ite]

中文:
引理 card_filter
  条件: (p) [DecidablePred p] (s : Finset ι)
  证明: by simp [sum_ite]

Depends on / 依赖: sum_ite
-/
lemma card_filter (p) [DecidablePred p] (s : Finset ι) :
    #{i in s | p i} = ∑ i in s, ite (p i) 1 0 := by simp [sum_ite]

end Finset

namespace Fintype

open Finset

variable [CommMonoid M] [Fintype ι]

@[to_additive]
/--
lemma `prod_ite_eq_ite_exists` / 引理 `prod_ite_eq_ite_exists`

English:
lemma prod_ite_eq_ite_exists
  statement: (p : ι -> Prop) [DecidablePred p] (h : forall i j, p i -> p j -> i = j)
  proof: by
  simp [prod_ite_one univ p (by simpa using h)]

中文:
引理 prod_ite_eq_ite_exists
  结论: (p : ι -> 命题) [DecidablePred p] (h : 对任意 i j, p i -> p j -> i = j)
  证明: by
  simp [prod_ite_one univ p (by simpa using h)]

Depends on / 依赖: prod_ite_one
-/
lemma prod_ite_eq_ite_exists (p : ι -> Prop) [DecidablePred p] (h : forall i j, p i -> p j -> i = j)
    (a : M) : ∏ i, ite (p i) a 1 = ite (exists i, p i) a 1 := by
  simp [prod_ite_one univ p (by simpa using h)]

variable [DecidableEq ι]

@[to_additive]
/--
lemma `prod_ite_mem` / 引理 `prod_ite_mem`

English:
lemma prod_ite_mem
  given: (s : Finset ι) (f : ι -> M)
  statement: ∏ i, (if i in s then f i else 1) = ∏ i in s, f i
  proof: by
  simp

中文:
引理 prod_ite_mem
  条件: (s : Finset ι) (f : ι -> M)
  结论: ∏ i, (if i in s then f i else 1) = ∏ i in s, f i
  证明: by
  simp
-/
lemma prod_ite_mem (s : Finset ι) (f : ι -> M) : ∏ i, (if i in s then f i else 1) = ∏ i in s, f i := by
  simp

/-- See also `Finset.prod_dite_eq`. -/
@[to_additive /-- See also `Finset.sum_dite_eq`. -/]
/--
lemma `prod_dite_eq` / 引理 `prod_dite_eq`

English:
lemma prod_dite_eq
  given: (i : ι) (f : forall j, i = j -> M)
  proof: by
  rw [Finset.prod_dite_eq]; rw [if_pos (mem_univ _)]

中文:
引理 prod_dite_eq
  条件: (i : ι) (f : 对任意 j, i = j -> M)
  证明: by
  rw [Finset.prod_dite_eq]; rw [if_pos (mem_univ _)]

Depends on / 依赖: Finset, Finset.prod_dite_eq, if_pos, mem_univ, prod_dite_eq
-/
lemma prod_dite_eq (i : ι) (f : forall j, i = j -> M) :
    ∏ j, (if h : i = j then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq]; rw [if_pos (mem_univ _)]

/-- See also `Finset.prod_dite_eq'`. -/
@[to_additive /-- See also `Finset.sum_dite_eq'`. -/]
/--
lemma `prod_dite_eq'` / 引理 `prod_dite_eq'`

English:
lemma prod_dite_eq'
  given: (i : ι) (f : forall j, j = i -> M)
  proof: by
  rw [Finset.prod_dite_eq']; rw [if_pos (mem_univ _)]

中文:
引理 prod_dite_eq'
  条件: (i : ι) (f : 对任意 j, j = i -> M)
  证明: by
  rw [Finset.prod_dite_eq']; rw [if_pos (mem_univ _)]

Depends on / 依赖: Finset, Finset.prod_dite_eq, if_pos, mem_univ, prod_dite_eq
-/
lemma prod_dite_eq' (i : ι) (f : forall j, j = i -> M) :
    ∏ j, (if h : j = i then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq']; rw [if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq`. -/
@[to_additive /-- See also `Finset.sum_ite_eq`. -/]
/--
lemma `prod_ite_eq` / 引理 `prod_ite_eq`

English:
lemma prod_ite_eq
  given: (i : ι) (f : ι -> M)
  statement: ∏ j, (if i = j then f j else 1) = f i
  proof: by
  rw [Finset.prod_ite_eq]; rw [if_pos (mem_univ _)]

中文:
引理 prod_ite_eq
  条件: (i : ι) (f : ι -> M)
  结论: ∏ j, (if i = j then f j else 1) = f i
  证明: by
  rw [Finset.prod_ite_eq]; rw [if_pos (mem_univ _)]

Depends on / 依赖: Finset, Finset.prod_ite_eq, if_pos, mem_univ, prod_ite_eq
-/
lemma prod_ite_eq (i : ι) (f : ι -> M) : ∏ j, (if i = j then f j else 1) = f i := by
  rw [Finset.prod_ite_eq]; rw [if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq'`. -/
@[to_additive /-- See also `Finset.sum_ite_eq'`. -/]
/--
lemma `prod_ite_eq'` / 引理 `prod_ite_eq'`

English:
lemma prod_ite_eq'
  given: (i : ι) (f : ι -> M)
  statement: ∏ j, (if j = i then f j else 1) = f i
  proof: by
  rw [Finset.prod_ite_eq']; rw [if_pos (mem_univ _)]

中文:
引理 prod_ite_eq'
  条件: (i : ι) (f : ι -> M)
  结论: ∏ j, (if j = i then f j else 1) = f i
  证明: by
  rw [Finset.prod_ite_eq']; rw [if_pos (mem_univ _)]

Depends on / 依赖: Finset, Finset.prod_ite_eq, if_pos, mem_univ, prod_ite_eq
-/
lemma prod_ite_eq' (i : ι) (f : ι -> M) : ∏ j, (if j = i then f j else 1) = f i := by
  rw [Finset.prod_ite_eq']; rw [if_pos (mem_univ _)]

/-- See also `Finset.prod_pi_mulSingle`. -/
@[to_additive /-- See also `Finset.sum_pi_single`. -/]
/--
lemma `prod_pi_mulSingle` / 引理 `prod_pi_mulSingle`

English:
lemma prod_pi_mulSingle
  given: {M : ι -> Type*} [forall i, CommMonoid (M i)] (i : ι) (f : forall i, M i)
  proof: prod_dite_eq _ _

中文:
引理 prod_pi_mulSingle
  条件: {M : ι -> 类型} [对任意 i, CommMonoid (M i)] (i : ι) (f : 对任意 i, M i)
  证明: prod_dite_eq _ _

Depends on / 依赖: prod_dite_eq
-/
lemma prod_pi_mulSingle {M : ι -> Type*} [forall i, CommMonoid (M i)] (i : ι) (f : forall i, M i) :
    ∏ j, Pi.mulSingle j (f j) i = f i := prod_dite_eq _ _

/-- See also `Finset.prod_pi_mulSingle'`. -/
@[to_additive /-- See also `Finset.sum_pi_single'`. -/]
/--
lemma `prod_pi_mulSingle'` / 引理 `prod_pi_mulSingle'`

English:
lemma prod_pi_mulSingle'
  given: (i : ι) (a : M)
  statement: ∏ j, Pi.mulSingle i a j = a
  proof: prod_dite_eq' _ _

中文:
引理 prod_pi_mulSingle'
  条件: (i : ι) (a : M)
  结论: ∏ j, Pi.mulSingle i a j = a
  证明: prod_dite_eq' _ _

Depends on / 依赖: prod_dite_eq
-/
lemma prod_pi_mulSingle' (i : ι) (a : M) : ∏ j, Pi.mulSingle i a j = a := prod_dite_eq' _ _

end Fintype
