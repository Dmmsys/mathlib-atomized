/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sums and products over preimages of finite sets.
-/

public section

assert_not_exists MonoidWithZero MulAction IsOrderedMonoid

variable {ι κ β : Type*}

open Fin Function

namespace Finset

variable [CommMonoid β]

@[to_additive]
/-
**Finset.prod_preimage'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_preimage' (f : ι -> κ) [DecidablePred (· in Set.range f)] (s : Finset
 κ) (hf) (g : κ -> β) : ∏ x in s.preimage f hf, g (f x) = ∏ x in s with x in Set
.range f, g x
参数：f : ι -> κ；· in Set.range f；s : Finset κ；hf；g : κ -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Finset.image_preimage`：image_preimage [DecidableEq β] (f : α -> β) (s : 
Finset β) [forall x, Decidable (x in Set.range f)] (hf : Set.InjOn f (f ⁻¹' ↑s))
 : image f …
-/
lemma prod_preimage' (f : ι → κ) [DecidablePred (· ∈ Set.range f)] (s : Finset κ) (hf) (g : κ → β) :
    ∏ x ∈ s.preimage f hf, g (f x) = ∏ x ∈ s with x ∈ Set.range f, g x := by
  classical
  calc
    ∏ x ∈ preimage s f hf, g (f x) = ∏ x ∈ image f (preimage s f hf), g x :=
      Eq.symm <| prod_image <| by simpa [mem_preimage, Set.InjOn] using hf
    _ = ∏ x ∈ s with x ∈ Set.range f, g x := by rw [image_preimage]

@[to_additive]
/-
**Finset.prod_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_preimage (f : ι -> κ) (s : Finset κ) (hf) (g : κ -> β) (hg : forall x
 in s, x ∉ Set.range f -> g x = 1) : ∏ x in s.preimage f hf, g (f x) = ∏ x in s,
 g x
参数：f : ι -> κ；s : Finset κ；hf；g : κ -> β；hg : forall x in s, x ∉ Set.range f -> 
g x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_preimage'`：prod_preimage' (f : ι -> κ) [DecidablePred (· in 
Set.range f)] (s : Finset κ) (hf) (g : κ -> β) : ∏ x in s.preimage f hf, g (f x)
 = ∏ x in s…
· 使用定理 `Finset.prod_filter_of_ne`：prod_filter_of_ne {p : ι -> Prop} [DecidablePr
ed p] (hp : forall x in s, f x != 1 -> p x) : ∏ x in s with p x, f x = ∏ x in s,
 f x
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
-/
lemma prod_preimage (f : ι → κ) (s : Finset κ) (hf) (g : κ → β)
    (hg : ∀ x ∈ s, x ∉ Set.range f → g x = 1) :
    ∏ x ∈ s.preimage f hf, g (f x) = ∏ x ∈ s, g x := by
  classical rw [prod_preimage', prod_filter_of_ne]; exact fun x hx ↦ Not.imp_symm (hg x hx)

@[to_additive]
/-
**Finset.prod_preimage_of_bij** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_preimage_of_bij (f : ι -> κ) (s : Finset κ) (hf : Set.BijOn f (f ⁻¹' 
↑s) ↑s) (g : κ -> β) : ∏ x in s.preimage f hf.injOn, g (f x) = ∏ x in s, g x
参数：f : ι -> κ；s : Finset κ；hf : Set.BijOn f (f ⁻¹' ↑s) ↑s；g : κ -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_preimage`：prod_preimage (f : ι -> κ) (s : Finset κ) (hf) (g 
: κ -> β) (hg : forall x in s, x ∉ Set.range f -> g x = 1) : ∏ x in s.preimage f
 hf, g (f …
· 使用定理 `Set.BijOn.injOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β}
 {f : α → β}, Set.BijOn f s t → Set.InjOn f s
· 使用定理 `Set.BijOn.subset_range`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t :
 Set β} {f : α → β}, Set.BijOn f s t → t ⊆ Set.range f
-/
lemma prod_preimage_of_bij (f : ι → κ) (s : Finset κ) (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) (g : κ → β) :
    ∏ x ∈ s.preimage f hf.injOn, g (f x) = ∏ x ∈ s, g x :=
  prod_preimage _ _ hf.injOn g fun _ hs h_f ↦ (h_f <| hf.subset_range hs).elim

end Finset

