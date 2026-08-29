/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Prod

/-!
# `Filter.atTop` and `Filter.atBot` filters on products
-/

public section

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

/--
theorem `prod_atTop_atTop_eq` / 定理 `prod_atTop_atTop_eq`

English:
theorem prod_atTop_atTop_eq
  given: [Preorder α] [Preorder β]
  proof: by
  cases isEmpty_or_nonempty α
  · subsingleton
  cases isEmpty_or_nonempty β
  · subsingleton
  simpa [atTop, prod_iInf_left, prod_iInf_right, iInf_prod] using iInf_comm

中文:
定理 prod_atTop_atTop_eq
  条件: [预序 α] [预序 β]
  证明: by
  cases isEmpty_or_nonempty α
  · subsingleton
  cases isEmpty_or_nonempty β
  · subsingleton
  simpa [atTop, prod_iInf_left, prod_iInf_right, iInf_prod] using iInf_comm

Depends on / 依赖: iInf_comm, iInf_prod, isEmpty_or_nonempty, prod_iInf_left, prod_iInf_right, subsingleton
-/
theorem prod_atTop_atTop_eq [Preorder α] [Preorder β] :
    (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β)) := by
  cases isEmpty_or_nonempty α
  · subsingleton
  cases isEmpty_or_nonempty β
  · subsingleton
  simpa [atTop, prod_iInf_left, prod_iInf_right, iInf_prod] using iInf_comm

/--
lemma `tendsto_finsetProd_atTop` / 引理 `tendsto_finsetProd_atTop`

English:
lemma tendsto_finsetProd_atTop
  proof: by
  classical
  apply Monotone.tendsto_atTop_atTop
  · intro p q hpq
    simpa using Finset.product_subset_product hpq.1 hpq.2
  · intro b
    use (Finset.image Prod.fst b, Finset.image Prod.snd b)
    exact Finset.subset_product

@[deprecated (since := "2026-04-08")] alias tendsto_finset_prod_atTop := tendsto_finsetProd_atTop

中文:
引理 tendsto_finsetProd_atTop
  证明: by
  classical
  apply Monotone.tendsto_atTop_atTop
  · intro p q hpq
    simpa using Finset.product_subset_product hpq.1 hpq.2
  · intro b
    use (Finset.image Prod.fst b, Finset.image Prod.snd b)
    exact Finset.subset_product

@[deprecated (since := "2026-04-08")] alias tendsto_finset_prod_atTop := tendsto_finsetProd_atTop

Depends on / 依赖: Finset, Finset.image, Finset.product_subset_product, Finset.subset_product, Monotone, Monotone.tendsto_atTop_atTop, Prod.fst, Prod.snd, classical, product_subset_product, subset_product, tendsto_atTop_atTop
-/
lemma tendsto_finsetProd_atTop :
    Tendsto (fun (p : Finset ι × Finset ι') => p.1 ×ˢ p.2) atTop atTop := by
  classical
  apply Monotone.tendsto_atTop_atTop
  · intro p q hpq
    simpa using Finset.product_subset_product hpq.1 hpq.2
  · intro b
    use (Finset.image Prod.fst b, Finset.image Prod.snd b)
    exact Finset.subset_product

@[deprecated (since := "2026-04-08")] alias tendsto_finset_prod_atTop := tendsto_finsetProd_atTop

/--
theorem `prod_atBot_atBot_eq` / 定理 `prod_atBot_atBot_eq`

English:
theorem prod_atBot_atBot_eq
  given: [Preorder α] [Preorder β]
  proof: @prod_atTop_atTop_eq αᵒᵈ βᵒᵈ _ _

中文:
定理 prod_atBot_atBot_eq
  条件: [预序 α] [预序 β]
  证明: @prod_atTop_atTop_eq αᵒᵈ βᵒᵈ _ _

Depends on / 依赖: prod_atTop_atTop_eq
-/
theorem prod_atBot_atBot_eq [Preorder α] [Preorder β] :
    (atBot : Filter α) ×ˢ (atBot : Filter β) = (atBot : Filter (α × β)) :=
  @prod_atTop_atTop_eq αᵒᵈ βᵒᵈ _ _

/--
theorem `prod_map_atTop_eq` / 定理 `prod_map_atTop_eq`

English:
theorem prod_map_atTop_eq
  statement: {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
  proof: by
  rw [prod_map_map_eq]; rw [prod_atTop_atTop_eq]; rw [Prod.map_def]

中文:
定理 prod_map_atTop_eq
  结论: {α₁ α₂ β₁ β₂ : 类型} [预序 β₁] [预序 β₂]
  证明: by
  rw [prod_map_map_eq]; rw [prod_atTop_atTop_eq]; rw [Prod.map_def]

Depends on / 依赖: Prod.map_def, map_def, prod_atTop_atTop_eq, prod_map_map_eq
-/
theorem prod_map_atTop_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
    (u₁ : β₁ -> α₁) (u₂ : β₂ -> α₂) : map u₁ atTop ×ˢ map u₂ atTop = map (Prod.map u₁ u₂) atTop := by
  rw [prod_map_map_eq]; rw [prod_atTop_atTop_eq]; rw [Prod.map_def]

/--
theorem `prod_map_atBot_eq` / 定理 `prod_map_atBot_eq`

English:
theorem prod_map_atBot_eq
  statement: {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
  proof: @prod_map_atTop_eq _ _ β₁ᵒᵈ β₂ᵒᵈ _ _ _ _

中文:
定理 prod_map_atBot_eq
  结论: {α₁ α₂ β₁ β₂ : 类型} [预序 β₁] [预序 β₂]
  证明: @prod_map_atTop_eq _ _ β₁ᵒᵈ β₂ᵒᵈ _ _ _ _

Depends on / 依赖: prod_map_atTop_eq
-/
theorem prod_map_atBot_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
    (u₁ : β₁ -> α₁) (u₂ : β₂ -> α₂) : map u₁ atBot ×ˢ map u₂ atBot = map (Prod.map u₁ u₂) atBot :=
  @prod_map_atTop_eq _ _ β₁ᵒᵈ β₂ᵒᵈ _ _ _ _

/--
theorem `tendsto_atBot_diagonal` / 定理 `tendsto_atBot_diagonal`

English:
theorem tendsto_atBot_diagonal
  given: [Preorder α]
  statement: Tendsto (fun a : α => (a, a)) atBot atBot
  proof: by
  rw [← prod_atBot_atBot_eq]
  exact tendsto_id.prodMk tendsto_id

中文:
定理 tendsto_atBot_diagonal
  条件: [预序 α]
  结论: 收敛 (fun a : α => (a, a)) atBot atBot
  证明: by
  rw [← prod_atBot_atBot_eq]
  exact tendsto_id.prodMk tendsto_id

Depends on / 依赖: prodMk, prod_atBot_atBot_eq, tendsto_id, tendsto_id.prodMk
-/
theorem tendsto_atBot_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atBot atBot := by
  rw [← prod_atBot_atBot_eq]
  exact tendsto_id.prodMk tendsto_id

/--
theorem `tendsto_atTop_diagonal` / 定理 `tendsto_atTop_diagonal`

English:
theorem tendsto_atTop_diagonal
  given: [Preorder α]
  statement: Tendsto (fun a : α => (a, a)) atTop atTop
  proof: by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_id.prodMk tendsto_id

中文:
定理 tendsto_atTop_diagonal
  条件: [预序 α]
  结论: 收敛 (fun a : α => (a, a)) atTop atTop
  证明: by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_id.prodMk tendsto_id

Depends on / 依赖: prodMk, prod_atTop_atTop_eq, tendsto_id, tendsto_id.prodMk
-/
theorem tendsto_atTop_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_id.prodMk tendsto_id

/--
theorem `Tendsto.prod_map_prod_atBot` / 定理 `Tendsto.prod_map_prod_atBot`

English:
theorem Tendsto.prod_map_prod_atBot
  statement: [Preorder γ] {F : Filter α} {G : Filter β} {f : α -> γ}
  proof: by
  rw [← prod_atBot_atBot_eq]
  exact hf.prodMap hg

中文:
定理 收敛.prod_map_prod_atBot
  结论: [预序 γ] {F : 滤子 α} {G : 滤子 β} {f : α -> γ}
  证明: by
  rw [← prod_atBot_atBot_eq]
  exact hf.prodMap hg

Depends on / 依赖: hf.prodMap, prodMap, prod_atBot_atBot_eq
-/
theorem Tendsto.prod_map_prod_atBot [Preorder γ] {F : Filter α} {G : Filter β} {f : α -> γ}
    {g : β -> γ} (hf : Tendsto f F atBot) (hg : Tendsto g G atBot) :
    Tendsto (Prod.map f g) (F ×ˢ G) atBot := by
  rw [← prod_atBot_atBot_eq]
  exact hf.prodMap hg

/--
theorem `Tendsto.prod_map_prod_atTop` / 定理 `Tendsto.prod_map_prod_atTop`

English:
theorem Tendsto.prod_map_prod_atTop
  statement: [Preorder γ] {F : Filter α} {G : Filter β} {f : α -> γ}
  proof: by
  rw [← prod_atTop_atTop_eq]
  exact hf.prodMap hg

中文:
定理 收敛.prod_map_prod_atTop
  结论: [预序 γ] {F : 滤子 α} {G : 滤子 β} {f : α -> γ}
  证明: by
  rw [← prod_atTop_atTop_eq]
  exact hf.prodMap hg

Depends on / 依赖: hf.prodMap, prodMap, prod_atTop_atTop_eq
-/
theorem Tendsto.prod_map_prod_atTop [Preorder γ] {F : Filter α} {G : Filter β} {f : α -> γ}
    {g : β -> γ} (hf : Tendsto f F atTop) (hg : Tendsto g G atTop) :
    Tendsto (Prod.map f g) (F ×ˢ G) atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prodMap hg

/--
theorem `Tendsto.prod_atBot` / 定理 `Tendsto.prod_atBot`

English:
theorem Tendsto.prod_atBot
  statement: [Preorder α] [Preorder γ] {f g : α -> γ}
  proof: by
  rw [← prod_atBot_atBot_eq]
  exact hf.prod_map_prod_atBot hg

中文:
定理 收敛.prod_atBot
  结论: [预序 α] [预序 γ] {f g : α -> γ}
  证明: by
  rw [← prod_atBot_atBot_eq]
  exact hf.prod_map_prod_atBot hg

Depends on / 依赖: hf.prod_map_prod_atBot, prod_atBot_atBot_eq, prod_map_prod_atBot
-/
theorem Tendsto.prod_atBot [Preorder α] [Preorder γ] {f g : α -> γ}
    (hf : Tendsto f atBot atBot) (hg : Tendsto g atBot atBot) :
    Tendsto (Prod.map f g) atBot atBot := by
  rw [← prod_atBot_atBot_eq]
  exact hf.prod_map_prod_atBot hg

/--
theorem `Tendsto.prod_atTop` / 定理 `Tendsto.prod_atTop`

English:
theorem Tendsto.prod_atTop
  statement: [Preorder α] [Preorder γ] {f g : α -> γ}
  proof: by
  rw [← prod_atTop_atTop_eq]
  exact hf.prod_map_prod_atTop hg

中文:
定理 收敛.prod_atTop
  结论: [预序 α] [预序 γ] {f g : α -> γ}
  证明: by
  rw [← prod_atTop_atTop_eq]
  exact hf.prod_map_prod_atTop hg

Depends on / 依赖: hf.prod_map_prod_atTop, prod_atTop_atTop_eq, prod_map_prod_atTop
-/
theorem Tendsto.prod_atTop [Preorder α] [Preorder γ] {f g : α -> γ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    Tendsto (Prod.map f g) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prod_map_prod_atTop hg

/--
theorem `eventually_atBot_prod_self` / 定理 `eventually_atBot_prod_self`

English:
theorem eventually_atBot_prod_self
  statement: [Nonempty α] [Preorder α] [IsCodirectedOrder α]
  proof: by
  simp [← prod_atBot_atBot_eq, (@atBot_basis α _ _).prod_self.eventually_iff]

中文:
定理 eventually_atBot_prod_self
  结论: [非空 α] [预序 α] [IsCodirectedOrder α]
  证明: by
  simp [← prod_atBot_atBot_eq, (@atBot_basis α _ _).prod_self.eventually_iff]

Depends on / 依赖: atBot_basis, eventually_iff, prod_atBot_atBot_eq, prod_self, prod_self.eventually_iff
-/
theorem eventually_atBot_prod_self [Nonempty α] [Preorder α] [IsCodirectedOrder α]
    {p : α × α -> Prop} : (forallᶠ x in atBot, p x) ↔ exists a, forall k l, k <= a -> l <= a -> p (k, l) := by
  simp [← prod_atBot_atBot_eq, (@atBot_basis α _ _).prod_self.eventually_iff]

/--
theorem `eventually_atTop_prod_self` / 定理 `eventually_atTop_prod_self`

English:
theorem eventually_atTop_prod_self
  statement: [Nonempty α] [Preorder α] [IsDirectedOrder α]
  proof: eventually_atBot_prod_self (α := αᵒᵈ)

中文:
定理 eventually_atTop_prod_self
  结论: [非空 α] [预序 α] [IsDirectedOrder α]
  证明: eventually_atBot_prod_self (α := αᵒᵈ)

Depends on / 依赖: eventually_atBot_prod_self
-/
theorem eventually_atTop_prod_self [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {p : α × α -> Prop} : (forallᶠ x in atTop, p x) ↔ exists a, forall k l, a <= k -> a <= l -> p (k, l) :=
  eventually_atBot_prod_self (α := αᵒᵈ)

/--
theorem `eventually_atBot_prod_self'` / 定理 `eventually_atBot_prod_self'`

English:
theorem eventually_atBot_prod_self'
  statement: [Nonempty α] [Preorder α] [IsCodirectedOrder α]
  proof: by
  simp only [eventually_atBot_prod_self, forall_cond_comm]

中文:
定理 eventually_atBot_prod_self'
  结论: [非空 α] [预序 α] [IsCodirectedOrder α]
  证明: by
  simp only [eventually_atBot_prod_self, forall_cond_comm]

Depends on / 依赖: eventually_atBot_prod_self, forall_cond_comm
-/
theorem eventually_atBot_prod_self' [Nonempty α] [Preorder α] [IsCodirectedOrder α]
    {p : α × α -> Prop} : (forallᶠ x in atBot, p x) ↔ exists a, forall k <= a, forall l <= a, p (k, l) := by
  simp only [eventually_atBot_prod_self, forall_cond_comm]

/--
theorem `eventually_atTop_prod_self'` / 定理 `eventually_atTop_prod_self'`

English:
theorem eventually_atTop_prod_self'
  statement: [Nonempty α] [Preorder α] [IsDirectedOrder α]
  proof: by
  simp only [eventually_atTop_prod_self, forall_cond_comm]

中文:
定理 eventually_atTop_prod_self'
  结论: [非空 α] [预序 α] [IsDirectedOrder α]
  证明: by
  simp only [eventually_atTop_prod_self, forall_cond_comm]

Depends on / 依赖: eventually_atTop_prod_self, forall_cond_comm
-/
theorem eventually_atTop_prod_self' [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {p : α × α -> Prop} : (forallᶠ x in atTop, p x) ↔ exists a, forall k >= a, forall l >= a, p (k, l) := by
  simp only [eventually_atTop_prod_self, forall_cond_comm]

/--
theorem `eventually_atTop_curry` / 定理 `eventually_atTop_curry`

English:
theorem eventually_atTop_curry
  statement: [Preorder α] [Preorder β] {p : α × β -> Prop}
  proof: by
  rw [← prod_atTop_atTop_eq] at hp
  exact hp.curry

中文:
定理 eventually_atTop_curry
  结论: [预序 α] [预序 β] {p : α × β -> 命题}
  证明: by
  rw [← prod_atTop_atTop_eq] at hp
  exact hp.curry

Depends on / 依赖: hp.curry, prod_atTop_atTop_eq
-/
theorem eventually_atTop_curry [Preorder α] [Preorder β] {p : α × β -> Prop}
    (hp : forallᶠ x : α × β in Filter.atTop, p x) : forallᶠ k in atTop, forallᶠ l in atTop, p (k, l) := by
  rw [← prod_atTop_atTop_eq] at hp
  exact hp.curry

/--
theorem `eventually_atBot_curry` / 定理 `eventually_atBot_curry`

English:
theorem eventually_atBot_curry
  statement: [Preorder α] [Preorder β] {p : α × β -> Prop}
  proof: @eventually_atTop_curry αᵒᵈ βᵒᵈ _ _ _ hp

中文:
定理 eventually_atBot_curry
  结论: [预序 α] [预序 β] {p : α × β -> 命题}
  证明: @eventually_atTop_curry αᵒᵈ βᵒᵈ _ _ _ hp

Depends on / 依赖: eventually_atTop_curry
-/
theorem eventually_atBot_curry [Preorder α] [Preorder β] {p : α × β -> Prop}
    (hp : forallᶠ x : α × β in Filter.atBot, p x) : forallᶠ k in atBot, forallᶠ l in atBot, p (k, l) :=
  @eventually_atTop_curry αᵒᵈ βᵒᵈ _ _ _ hp

end Filter
