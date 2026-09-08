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

/-
**Filter.prod_atTop_atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_atTop_atTop_eq [Preorder α] [Preorder β] : (atTop : Filter α) ×ˢ (atT
op : Filter β) = (atTop : Filter (α × β))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.prod_iInf_right`：prod_iInf_right [Nonempty ι] {f : Filter α} {g :
 ι -> Filter β} : (f ×ˢ ⨅ i, g i) = ⨅ i, f ×ˢ g i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.prod_iInf_left`：prod_iInf_left [Nonempty ι] {f : ι -> Filter α} {
g : Filter β} : (⨅ i, f i) ×ˢ g = ⨅ i, f i ×ˢ g
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `iInf_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comple
teLattice α] {f : β × γ → α}, ⨅ x, f x = ⨅ i, ⨅ j, f (i, j)
· 使用定理 `iInf_comm`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Compl
eteLattice α] {f : ι → ι' → α},   ⨅ i, ⨅ j, f i j = ⨅ j, ⨅ i, f i j
-/
theorem prod_atTop_atTop_eq [Preorder α] [Preorder β] :
    (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β)) := by
  cases isEmpty_or_nonempty α
  · subsingleton
  cases isEmpty_or_nonempty β
  · subsingleton
  simpa [atTop, prod_iInf_left, prod_iInf_right, iInf_prod] using iInf_comm
/-
**Filter.tendsto_finsetProd_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：tendsto_finsetProd_atTop : Tendsto (fun (p : Finset ι × Finset ι') => p.1 
×ˢ p.2) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Finset.product_subset_product`：product_subset_product (hs : s subseteq s
') (ht : t subseteq t') : s ×ˢ t subseteq s' ×ˢ t'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.subset_product`：subset_product [DecidableEq α] [DecidableEq β] {s
 : Finset (α × β)} : s subseteq s.image Prod.fst ×ˢ s.image Prod.snd
-/
lemma tendsto_finsetProd_atTop :
    Tendsto (fun (p : Finset ι × Finset ι') ↦ p.1 ×ˢ p.2) atTop atTop := by
  classical
  apply Monotone.tendsto_atTop_atTop
  · intro p q hpq
    simpa using Finset.product_subset_product hpq.1 hpq.2
  · intro b
    use (Finset.image Prod.fst b, Finset.image Prod.snd b)
    exact Finset.subset_product

@[deprecated (since := "2026-04-08")] alias tendsto_finset_prod_atTop := tendsto_finsetProd_atTop
/-
**Filter.prod_atBot_atBot_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_atBot_atBot_eq [Preorder α] [Preorder β] : (atBot : Filter α) ×ˢ (atB
ot : Filter β) = (atBot : Filter (α × β))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
-/
theorem prod_atBot_atBot_eq [Preorder α] [Preorder β] :
    (atBot : Filter α) ×ˢ (atBot : Filter β) = (atBot : Filter (α × β)) :=
  @prod_atTop_atTop_eq αᵒᵈ βᵒᵈ _ _
/-
**Filter.prod_map_atTop_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_map_atTop_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂] (u₁ : 
β₁ -> α₁) (u₂ : β₂ -> α₂) : map u₁ atTop ×ˢ map u₂ atTop = map (Prod.map u₁ u₂) 
atTop
参数：u₁ : β₁ -> α₁；u₂ : β₂ -> α₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_map_map_eq`：prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ :
 Type v} {β₁ : Type w} {β₂ : Type x} {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ 
-> β₁} {m₂ :…
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Prod.map_def`：map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p :
 α × β => (f p.1, g p.2)
-/
theorem prod_map_atTop_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
    (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) : map u₁ atTop ×ˢ map u₂ atTop = map (Prod.map u₁ u₂) atTop := by
  rw [prod_map_map_eq, prod_atTop_atTop_eq, Prod.map_def]
/-
**Filter.prod_map_atBot_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_map_atBot_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂] (u₁ : 
β₁ -> α₁) (u₂ : β₂ -> α₂) : map u₁ atBot ×ˢ map u₂ atBot = map (Prod.map u₁ u₂) 
atBot
参数：u₁ : β₁ -> α₁；u₂ : β₂ -> α₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_map_atTop_eq`：prod_map_atTop_eq {α₁ α₂ β₁ β₂ : Type*} [Preor
der β₁] [Preorder β₂] (u₁ : β₁ -> α₁) (u₂ : β₂ -> α₂) : map u₁ atTop ×ˢ map u₂ a
tTop = map (Pr…
-/
theorem prod_map_atBot_eq {α₁ α₂ β₁ β₂ : Type*} [Preorder β₁] [Preorder β₂]
    (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) : map u₁ atBot ×ˢ map u₂ atBot = map (Prod.map u₁ u₂) atBot :=
  @prod_map_atTop_eq _ _ β₁ᵒᵈ β₂ᵒᵈ _ _ _ _
/-
**Filter.tendsto_atBot_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atBot_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atBot 
atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atBot_atBot_eq`：prod_atBot_atBot_eq [Preorder α] [Preorder β
] : (atBot : Filter α) ×ˢ (atBot : Filter β) = (atBot : Filter (α × β))
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_atBot_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atBot atBot := by
  rw [← prod_atBot_atBot_eq]
  exact tendsto_id.prodMk tendsto_id
/-
**Filter.tendsto_atTop_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendsto_atTop_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atTop 
atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_atTop_diagonal [Preorder α] : Tendsto (fun a : α => (a, a)) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_id.prodMk tendsto_id
/-
**Filter.Tendsto.prod_map_prod_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : Preorder γ] {F : Fi
lter α} {G : Filter β} {f : α → γ}   {g : β → γ},   Filter.Tendsto f F Filter.at
Bot →     Filter.Tendsto g G Filter.atBot → Filter.Tendsto (Prod.map f g) (F ×ˢ 
G) Filter.atBot
参数：Prod.map f g；F ×ˢ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atBot_atBot_eq`：prod_atBot_atBot_eq [Preorder α] [Preorder β
] : (atBot : Filter α) ×ˢ (atBot : Filter β) = (atBot : Filter (α × β))
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
-/
theorem Tendsto.prod_map_prod_atBot [Preorder γ] {F : Filter α} {G : Filter β} {f : α → γ}
    {g : β → γ} (hf : Tendsto f F atBot) (hg : Tendsto g G atBot) :
    Tendsto (Prod.map f g) (F ×ˢ G) atBot := by
  rw [← prod_atBot_atBot_eq]
  exact hf.prodMap hg
/-
**Filter.Tendsto.prod_map_prod_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : Preorder γ] {F : Fi
lter α} {G : Filter β} {f : α → γ}   {g : β → γ},   Filter.Tendsto f F Filter.at
Top →     Filter.Tendsto g G Filter.atTop → Filter.Tendsto (Prod.map f g) (F ×ˢ 
G) Filter.atTop
参数：Prod.map f g；F ×ˢ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
-/
theorem Tendsto.prod_map_prod_atTop [Preorder γ] {F : Filter α} {G : Filter β} {f : α → γ}
    {g : β → γ} (hf : Tendsto f F atTop) (hg : Tendsto g G atTop) :
    Tendsto (Prod.map f g) (F ×ˢ G) atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prodMap hg
/-
**Filter.Tendsto.prod_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {γ : Type u_5} [inst : Preorder α] [inst_1 : Preorder γ] 
{f g : α → γ},   Filter.Tendsto f Filter.atBot Filter.atBot →     Filter.Tendsto
 g Filter.atBot Filter.atBot → Filter.Tendsto (Prod.map f g) Filter.atBot Filter
.atBot
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atBot_atBot_eq`：prod_atBot_atBot_eq [Preorder α] [Preorder β
] : (atBot : Filter α) ×ˢ (atBot : Filter β) = (atBot : Filter (α × β))
· 使用定理 `Filter.Tendsto.prod_map_prod_atBot`：∀ {α : Type u_3} {β : Type u_4} {γ :
 Type u_5} [inst : Preorder γ] {F : Filter α} {G : Filter β} {f : α → γ}   {g : 
β → γ},   Filter.Tendsto…
-/
theorem Tendsto.prod_atBot [Preorder α] [Preorder γ] {f g : α → γ}
    (hf : Tendsto f atBot atBot) (hg : Tendsto g atBot atBot) :
    Tendsto (Prod.map f g) atBot atBot := by
  rw [← prod_atBot_atBot_eq]
  exact hf.prod_map_prod_atBot hg
/-
**Filter.Tendsto.prod_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_3} {γ : Type u_5} [inst : Preorder α] [inst_1 : Preorder γ] 
{f g : α → γ},   Filter.Tendsto f Filter.atTop Filter.atTop →     Filter.Tendsto
 g Filter.atTop Filter.atTop → Filter.Tendsto (Prod.map f g) Filter.atTop Filter
.atTop
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Filter.Tendsto.prod_map_prod_atTop`：∀ {α : Type u_3} {β : Type u_4} {γ :
 Type u_5} [inst : Preorder γ] {F : Filter α} {G : Filter β} {f : α → γ}   {g : 
β → γ},   Filter.Tendsto…
-/
theorem Tendsto.prod_atTop [Preorder α] [Preorder γ] {f g : α → γ}
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    Tendsto (Prod.map f g) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact hf.prod_map_prod_atTop hg
/-
**Filter.eventually_atBot_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_atBot_prod_self [Nonempty α] [Preorder α] [IsCodirectedOrder α]
 {p : α × α -> Prop} : (forallᶠ x in atBot, p x) ↔ exists a, forall k l, k <= a 
-> l <= a -> p (k, l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用引理 `Filter.atBot_basis`：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOr
der α] [Nonempty α] : (@atBot α _).HasBasis (fun _ => True) Iic
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_atBot_prod_self [Nonempty α] [Preorder α] [IsCodirectedOrder α]
    {p : α × α → Prop} : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ k l, k ≤ a → l ≤ a → p (k, l) := by
  simp [← prod_atBot_atBot_eq, (@atBot_basis α _ _).prod_self.eventually_iff]
/-
**Filter.eventually_atTop_prod_self** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_atTop_prod_self [Nonempty α] [Preorder α] [IsDirectedOrder α] {
p : α × α -> Prop} : (forallᶠ x in atTop, p x) ↔ exists a, forall k l, a <= k ->
 a <= l -> p (k, l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_atBot_prod_self`：eventually_atBot_prod_self [Nonempty 
α] [Preorder α] [IsCodirectedOrder α] {p : α × α -> Prop} : (forallᶠ x in atBot,
 p x) ↔ exists a, foral…
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
-/
theorem eventually_atTop_prod_self [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k l, a ≤ k → a ≤ l → p (k, l) :=
  eventually_atBot_prod_self (α := αᵒᵈ)
/-
**Filter.eventually_atBot_prod_self'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_atBot_prod_self' [Nonempty α] [Preorder α] [IsCodirectedOrder α
] {p : α × α -> Prop} : (forallᶠ x in atBot, p x) ↔ exists a, forall k <= a, for
all l <= a, p (k, l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_atBot_prod_self' [Nonempty α] [Preorder α] [IsCodirectedOrder α]
    {p : α × α → Prop} : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ k ≤ a, ∀ l ≤ a, p (k, l) := by
  simp only [eventually_atBot_prod_self, forall_cond_comm]
/-
**Filter.eventually_atTop_prod_self'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_atTop_prod_self' [Nonempty α] [Preorder α] [IsDirectedOrder α] 
{p : α × α -> Prop} : (forallᶠ x in atTop, p x) ↔ exists a, forall k >= a, foral
l l >= a, p (k, l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_atTop_prod_self' [Nonempty α] [Preorder α] [IsDirectedOrder α]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k ≥ a, ∀ l ≥ a, p (k, l) := by
  simp only [eventually_atTop_prod_self, forall_cond_comm]
/-
**Filter.eventually_atTop_curry** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_atTop_curry [Preorder α] [Preorder β] {p : α × β -> Prop} (hp :
 forallᶠ x : α × β in Filter.atTop, p x) : forallᶠ k in atTop, forallᶠ l in atTo
p, p (k, l)
参数：hp : forallᶠ x : α × β in Filter.atTop, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
-/
theorem eventually_atTop_curry [Preorder α] [Preorder β] {p : α × β → Prop}
    (hp : ∀ᶠ x : α × β in Filter.atTop, p x) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, p (k, l) := by
  rw [← prod_atTop_atTop_eq] at hp
  exact hp.curry
/-
**Filter.eventually_atBot_curry** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_atBot_curry [Preorder α] [Preorder β] {p : α × β -> Prop} (hp :
 forallᶠ x : α × β in Filter.atBot, p x) : forallᶠ k in atBot, forallᶠ l in atBo
t, p (k, l)
参数：hp : forallᶠ x : α × β in Filter.atBot, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_atTop_curry`：eventually_atTop_curry [Preorder α] [Preo
rder β] {p : α × β -> Prop} (hp : forallᶠ x : α × β in Filter.atTop, p x) : fora
llᶠ k in atTop, for…
-/
theorem eventually_atBot_curry [Preorder α] [Preorder β] {p : α × β → Prop}
    (hp : ∀ᶠ x : α × β in Filter.atBot, p x) : ∀ᶠ k in atBot, ∀ᶠ l in atBot, p (k, l) :=
  @eventually_atTop_curry αᵒᵈ βᵒᵈ _ _ _ hp

end Filter

