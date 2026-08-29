/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.GroupTheory.GroupAction.DomAct.Basic

/-!
# Translation operator

This file defines the translation of a function from a group by an element of that group.

## Notation

`τ a f` is notation for `translate a f`.

## See also

Generally, translation is the same as acting on the domain by subtraction. This setting is
abstracted by `DomAddAct` in such a way that `τ a f = DomAddAct.mk (-a) +ᵥ f` (see
`translate_eq_domAddActMk_vadd`). Using `DomAddAct` is irritating in applications because of this
negation appearing inside `DomAddAct.mk`. Although mathematically equivalent, the pen and paper
convention is that translating is an action by subtraction, not by addition.
-/

@[expose] public section

open Function Set
open scoped Pointwise

variable {ι α β M G H : Type*} [AddCommGroup G]

/--
Definition of `translate` / `translate` 的定义

English:
definition translate
  signature: (a : G) (f : G -> α)
  body: fun x => f (x - a)

@[inherit_doc] scoped[translate] notation "τ " => translate

中文:
定义 translate
  签名: (a : G) (f : G -> α)
  定义体: fun x => f (x - a)

@[inherit_doc] scoped[translate] notation "τ " => translate
-/
def translate (a : G) (f : G -> α) : G -> α := fun x => f (x - a)

@[inherit_doc] scoped[translate] notation "τ " => translate

open scoped translate

/--
lemma `translate_apply` / 引理 `translate_apply`

English:
lemma translate_apply
  given: (a : G) (f : G -> α) (x : G)
  statement: τ a f x = f (x - a)
  proof: rfl

中文:
引理 translate_apply
  条件: (a : G) (f : G -> α) (x : G)
  结论: τ a f x = f (x - a)
  证明: rfl
-/
@[simp] lemma translate_apply (a : G) (f : G -> α) (x : G) : τ a f x = f (x - a) := rfl
/--
lemma `translate_zero` / 引理 `translate_zero`

English:
lemma translate_zero
  given: (f : G -> α)
  statement: τ 0 f = f
  proof: by ext; simp

中文:
引理 translate_zero
  条件: (f : G -> α)
  结论: τ 0 f = f
  证明: by ext; simp
-/
@[simp] lemma translate_zero (f : G -> α) : τ 0 f = f := by ext; simp

/--
lemma `translate_translate` / 引理 `translate_translate`

English:
lemma translate_translate
  given: (a b : G) (f : G -> α)
  statement: τ a (τ b f) = τ (a + b) f
  proof: by
  ext; simp [sub_sub]

中文:
引理 translate_translate
  条件: (a b : G) (f : G -> α)
  结论: τ a (τ b f) = τ (a + b) f
  证明: by
  ext; simp [sub_sub]

Depends on / 依赖: sub_sub
-/
lemma translate_translate (a b : G) (f : G -> α) : τ a (τ b f) = τ (a + b) f := by
  ext; simp [sub_sub]

/--
lemma `translate_add` / 引理 `translate_add`

English:
lemma translate_add
  given: (a b : G) (f : G -> α)
  statement: τ (a + b) f = τ a (τ b f)
  proof: by ext; simp [sub_sub]

中文:
引理 translate_add
  条件: (a b : G) (f : G -> α)
  结论: τ (a + b) f = τ a (τ b f)
  证明: by ext; simp [sub_sub]

Depends on / 依赖: sub_sub
-/
lemma translate_add (a b : G) (f : G -> α) : τ (a + b) f = τ a (τ b f) := by ext; simp [sub_sub]

/--
lemma `translate_add'` / 引理 `translate_add'`

English:
lemma translate_add'
  given: (a b : G) (f : G -> α)
  statement: τ (a + b) f = τ b (τ a f)
  proof: by
  rw [add_comm]; rw [translate_add]

中文:
引理 translate_add'
  条件: (a b : G) (f : G -> α)
  结论: τ (a + b) f = τ b (τ a f)
  证明: by
  rw [add_comm]; rw [translate_add]

Depends on / 依赖: add_comm, translate_add
-/
lemma translate_add' (a b : G) (f : G -> α) : τ (a + b) f = τ b (τ a f) := by
  rw [add_comm]; rw [translate_add]

/--
lemma `translate_comm` / 引理 `translate_comm`

English:
lemma translate_comm
  given: (a b : G) (f : G -> α)
  statement: τ a (τ b f) = τ b (τ a f)
  proof: by
  rw [← translate_add]; rw [translate_add']

中文:
引理 translate_comm
  条件: (a b : G) (f : G -> α)
  结论: τ a (τ b f) = τ b (τ a f)
  证明: by
  rw [← translate_add]; rw [translate_add']

Depends on / 依赖: translate_add
-/
lemma translate_comm (a b : G) (f : G -> α) : τ a (τ b f) = τ b (τ a f) := by
  rw [← translate_add]; rw [translate_add']

-- We make `simp` push the `τ` outside
/--
lemma `comp_translate` / 引理 `comp_translate`

English:
lemma comp_translate
  given: (a : G) (f : G -> α) (g : α -> β)
  statement: g ∘ τ a f = τ a (g ∘ f)
  proof: rfl

中文:
引理 comp_translate
  条件: (a : G) (f : G -> α) (g : α -> β)
  结论: g ∘ τ a f = τ a (g ∘ f)
  证明: rfl
-/
@[simp] lemma comp_translate (a : G) (f : G -> α) (g : α -> β) : g ∘ τ a f = τ a (g ∘ f) := rfl

/--
lemma `translate_eq_domAddActMk_vadd` / 引理 `translate_eq_domAddActMk_vadd`

English:
lemma translate_eq_domAddActMk_vadd
  given: (a : G) (f : G -> α)
  statement: τ a f = DomAddAct.mk (-a) +ᵥ f
  proof: by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

@[simp]

中文:
引理 translate_eq_domAddActMk_vadd
  条件: (a : G) (f : G -> α)
  结论: τ a f = DomAddAct.mk (-a) +ᵥ f
  证明: by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

@[simp]

Depends on / 依赖: DomAddAct, DomAddAct.vadd_apply, sub_eq_neg_add, vadd_apply
-/
lemma translate_eq_domAddActMk_vadd (a : G) (f : G -> α) : τ a f = DomAddAct.mk (-a) +ᵥ f := by
  ext; simp [DomAddAct.vadd_apply, sub_eq_neg_add]

@[simp]
/--
lemma `translate_smul_right` / 引理 `translate_smul_right`

English:
lemma translate_smul_right
  given: [SMul H α] (a : G) (f : G -> α) (c : H)
  statement: τ a (c • f) = c • τ a f
  proof: rfl

中文:
引理 translate_smul_right
  条件: [SMul H α] (a : G) (f : G -> α) (c : H)
  结论: τ a (c • f) = c • τ a f
  证明: rfl
-/
lemma translate_smul_right [SMul H α] (a : G) (f : G -> α) (c : H) : τ a (c • f) = c • τ a f := rfl

/--
lemma `translate_zero_right` / 引理 `translate_zero_right`

English:
lemma translate_zero_right
  given: [Zero α] (a : G)
  statement: τ a (0 : G -> α) = 0
  proof: rfl

中文:
引理 translate_zero_right
  条件: [Zero α] (a : G)
  结论: τ a (0 : G -> α) = 0
  证明: rfl
-/
@[simp] lemma translate_zero_right [Zero α] (a : G) : τ a (0 : G -> α) = 0 := rfl
/--
lemma `translate_add_right` / 引理 `translate_add_right`

English:
lemma translate_add_right
  given: [Add α] (a : G) (f g : G -> α)
  statement: τ a (f + g) = τ a f + τ a g
  proof: rfl

中文:
引理 translate_add_right
  条件: [Add α] (a : G) (f g : G -> α)
  结论: τ a (f + g) = τ a f + τ a g
  证明: rfl
-/
lemma translate_add_right [Add α] (a : G) (f g : G -> α) : τ a (f + g) = τ a f + τ a g := rfl
/--
lemma `translate_sub_right` / 引理 `translate_sub_right`

English:
lemma translate_sub_right
  given: [Sub α] (a : G) (f g : G -> α)
  statement: τ a (f - g) = τ a f - τ a g
  proof: rfl

中文:
引理 translate_sub_right
  条件: [Sub α] (a : G) (f g : G -> α)
  结论: τ a (f - g) = τ a f - τ a g
  证明: rfl
-/
lemma translate_sub_right [Sub α] (a : G) (f g : G -> α) : τ a (f - g) = τ a f - τ a g := rfl
/--
lemma `translate_neg_right` / 引理 `translate_neg_right`

English:
lemma translate_neg_right
  given: [Neg α] (a : G) (f : G -> α)
  statement: τ a (-f) = -τ a f
  proof: rfl

中文:
引理 translate_neg_right
  条件: [Neg α] (a : G) (f : G -> α)
  结论: τ a (-f) = -τ a f
  证明: rfl
-/
lemma translate_neg_right [Neg α] (a : G) (f : G -> α) : τ a (-f) = -τ a f := rfl

section AddCommMonoid
variable [AddCommMonoid M]

/--
lemma `translate_sum_right` / 引理 `translate_sum_right`

English:
lemma translate_sum_right
  given: (a : G) (f : ι -> G -> M) (s : Finset ι)
  proof: by ext; simp

中文:
引理 translate_sum_right
  条件: (a : G) (f : ι -> G -> M) (s : Finset ι)
  证明: by ext; simp
-/
lemma translate_sum_right (a : G) (f : ι -> G -> M) (s : Finset ι) :
    τ a (∑ i in s, f i) = ∑ i in s, τ a (f i) := by ext; simp

/--
lemma `sum_translate` / 引理 `sum_translate`

English:
lemma sum_translate
  given: [Fintype G] (a : G) (f : G -> M)
  statement: ∑ b, τ a f b = ∑ b, f b
  proof: Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl

中文:
引理 sum_translate
  条件: [Fintype G] (a : G) (f : G -> M)
  结论: ∑ b, τ a f b = ∑ b, f b
  证明: Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl

Depends on / 依赖: Equiv.subRight, Fintype, Fintype.sum_equiv, subRight, sum_equiv
-/
lemma sum_translate [Fintype G] (a : G) (f : G -> M) : ∑ b, τ a f b = ∑ b, f b :=
  Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ => rfl

end AddCommMonoid

section AddCommGroup
variable [AddCommGroup H]

/--
lemma `support_translate` / 引理 `support_translate`

English:
lemma support_translate
  given: (a : G) (f : G -> H)
  statement: support (τ a f) = a +ᵥ support f
  proof: by
  ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

中文:
引理 support_translate
  条件: (a : G) (f : G -> H)
  结论: support (τ a f) = a +ᵥ support f
  证明: by
  ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]
-/
@[simp] lemma support_translate (a : G) (f : G -> H) : support (τ a f) = a +ᵥ support f := by
  ext; simp [mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end AddCommGroup

variable [CommMonoid M]

/--
lemma `translate_prod_right` / 引理 `translate_prod_right`

English:
lemma translate_prod_right
  given: (a : G) (f : ι -> G -> M) (s : Finset ι)
  proof: by ext; simp

中文:
引理 translate_prod_right
  条件: (a : G) (f : ι -> G -> M) (s : Finset ι)
  证明: by ext; simp
-/
lemma translate_prod_right (a : G) (f : ι -> G -> M) (s : Finset ι) :
    τ a (∏ i in s, f i) = ∏ i in s, τ a (f i) := by ext; simp
