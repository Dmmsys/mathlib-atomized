/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Basic
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.ExistsUnique
public import Mathlib.Logic.Nonempty
public import Mathlib.Logic.Nontrivial.Defs
public import Batteries.Tactic.Init
public import Mathlib.Order.Defs.Unbundled

import Mathlib.Tactic.Attr.Register

/-!
# Miscellaneous function constructions and lemmas
-/

@[expose] public section

open Function

universe u v w x

namespace Function

section

variable {α β γ : Sort*} {f : α -> β}

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: {β : α -> Sort*} (x : α) (f : forall x, β x)
  body: f x

中文:
定义 eval
  签名: {β : α -> 类型层*} (x : α) (f : 对任意 x, β x)
  定义体: f x
-/
@[reducible, simp] def eval {β : α -> Sort*} (x : α) (f : forall x, β x) : β x := f x

/--
theorem `eval_apply` / 定理 `eval_apply`

English:
theorem eval_apply
  given: {β : α -> Sort*} (x : α) (f : forall x, β x)
  statement: eval x f = f x
  proof: rfl

中文:
定理 eval_apply
  条件: {β : α -> 类型层*} (x : α) (f : 对任意 x, β x)
  结论: eval x f = f x
  证明: rfl
-/
theorem eval_apply {β : α -> Sort*} (x : α) (f : forall x, β x) : eval x f = f x :=
  rfl

/--
theorem `const_def` / 定理 `const_def`

English:
theorem const_def
  given: {y : β}
  statement: (fun _ : α => y) = const α y
  proof: rfl

中文:
定理 const_def
  条件: {y : β}
  结论: (fun _ : α => y) = const α y
  证明: rfl
-/
theorem const_def {y : β} : (fun _ : α => y) = const α y :=
  rfl

/--
theorem `const_injective` / 定理 `const_injective`

English:
theorem const_injective
  given: [Nonempty α]
  statement: Injective (const α : β -> α -> β)
  proof: fun _ _ h =>
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp]

中文:
定理 const_injective
  条件: [非空 α]
  结论: 单射 (const α : β -> α -> β)
  证明: fun _ _ h =>
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp]
-/
theorem const_injective [Nonempty α] : Injective (const α : β -> α -> β) := fun _ _ h =>
  let ⟨x⟩ := ‹Nonempty α›
  congr_fun h x

@[simp]
/--
theorem `const_inj` / 定理 `const_inj`

English:
theorem const_inj
  given: [Nonempty α] {y₁ y₂ : β}
  statement: const α y₁ = const α y₂ ↔ y₁ = y₂
  proof: ⟨fun h => const_injective h, fun h => h ▸ rfl⟩

中文:
定理 const_inj
  条件: [非空 α] {y₁ y₂ : β}
  结论: const α y₁ = const α y₂ ↔ y₁ = y₂
  证明: ⟨fun h => const_injective h, fun h => h ▸ rfl⟩

Depends on / 依赖: const_injective
-/
theorem const_inj [Nonempty α] {y₁ y₂ : β} : const α y₁ = const α y₂ ↔ y₁ = y₂ :=
  ⟨fun h => const_injective h, fun h => h ▸ rfl⟩

section onFun

/--
theorem `onFun_apply` / 定理 `onFun_apply`

English:
theorem onFun_apply
  given: (f : β -> β -> γ) (g : α -> β) (a b : α)
  statement: onFun f g a b = f (g a) (g b)
  proof: rfl

中文:
定理 onFun_apply
  条件: (f : β -> β -> γ) (g : α -> β) (a b : α)
  结论: onFun f g a b = f (g a) (g b)
  证明: rfl
-/
theorem onFun_apply (f : β -> β -> γ) (g : α -> β) (a b : α) : onFun f g a b = f (g a) (g b) :=
  rfl

/--
theorem `onFun_onFun_eq` / 定理 `onFun_onFun_eq`

English:
theorem onFun_onFun_eq
  given: {δ : Sort*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β)
  proof: rfl

中文:
定理 onFun_onFun_eq
  条件: {δ : 类型层*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β)
  证明: rfl
-/
theorem onFun_onFun_eq {δ : Sort*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β) :
    (f.onFun g).onFun h = f.onFun (g ∘ h) := rfl

/--
theorem `onFun_comp_eq` / 定理 `onFun_comp_eq`

English:
theorem onFun_comp_eq
  given: {δ : Sort*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β)
  proof: rfl

中文:
定理 onFun_comp_eq
  条件: {δ : 类型层*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β)
  证明: rfl
-/
theorem onFun_comp_eq {δ : Sort*} (f : α -> α -> γ) (g : β -> α) (h : δ -> β) :
    f.onFun (g ∘ h) = (f.onFun g).onFun h := rfl

variable (r : β -> β -> Prop) (f : α -> β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] : Std.Refl (r on f) where
  body: refl_of r _

中文:
实例 [Std.Refl
  签名: r] : Std.Refl (r on f) where
  定义体: refl_of r _

Depends on / 依赖: refl_of
-/
instance [Std.Refl r] : Std.Refl (r on f) where
  refl _ := refl_of r _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Irrefl
  signature: r] : Std.Irrefl (r on f) where
  body: irrefl_of r _

中文:
实例 [Std.Irrefl
  签名: r] : Std.Irrefl (r on f) where
  定义体: irrefl_of r _

Depends on / 依赖: irrefl_of
-/
instance [Std.Irrefl r] : Std.Irrefl (r on f) where
  irrefl _ := irrefl_of r _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Symm
  signature: r] : Std.Symm (r on f) where
  body: symm_of r

中文:
实例 [Std.Symm
  签名: r] : Std.Symm (r on f) where
  定义体: symm_of r

Depends on / 依赖: symm_of
-/
instance [Std.Symm r] : Std.Symm (r on f) where
  symm _ _ := symm_of r

variable {f} in
/--
theorem `Injective.antisymm_onFun` / 定理 `Injective.antisymm_onFun`

English:
theorem Injective.antisymm_onFun
  given: (hinj : f.Injective) [Std.Antisymm r]
  statement: Std.Antisymm (r on f) where
  proof: hinj antisymm_of r hab hba

中文:
定理 单射.antisymm_onFun
  条件: (hinj : f.单射) [Std.反对称 r]
  结论: Std.反对称 (r on f) where
  证明: hinj antisymm_of r hab hba

Depends on / 依赖: Coprime, Ico_union_Ico_eq_Ico, a.Coprime, antisymm_of, card_union_le, coprime_comm, coprime_of_lt_prime, count_eq_card_filter_range, filter_union, h1.trans_le, le_self_add, p.Prime, primeCounting, range_eq_Ico, trans_le, zero_le
-/
theorem Injective.antisymm_onFun (hinj : f.Injective) [Std.Antisymm r] : Std.Antisymm (r on f) where
antisymm _ _ hab hba := hinj antisymm_of r hab hba

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Asymm
  signature: r] : Std.Asymm (r on f) where
  body: asymm_of r

中文:
实例 [Std.Asymm
  签名: r] : Std.Asymm (r on f) where
  定义体: asymm_of r

Depends on / 依赖: asymm_of
-/
instance [Std.Asymm r] : Std.Asymm (r on f) where
  asymm _ _ := asymm_of r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTrans
  signature: β r] : IsTrans α (r on f) where
  body: trans_of r

中文:
实例 [是Trans
  签名: β r] : 是Trans α (r on f) where
  定义体: trans_of r

Depends on / 依赖: trans_of
-/
instance [IsTrans β r] : IsTrans α (r on f) where
  trans _ _ _ := trans_of r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Total
  signature: r] : Std.Total (r on f) where
  body: total_of r _ _

中文:
实例 [Std.全
  签名: r] : Std.全 (r on f) where
  定义体: total_of r _ _

Depends on / 依赖: total_of
-/
instance [Std.Total r] : Std.Total (r on f) where
  total _ _ := total_of r _ _

variable {f} in
/--
theorem `Injective.trichotomous_onFun` / 定理 `Injective.trichotomous_onFun`

English:
theorem Injective.trichotomous_onFun
  given: (hinj : f.Injective) [Std.Trichotomous r]
  proof: hinj Std.Trichotomous.trichotomous (f a) (f b) hab hba

中文:
定理 单射.trichotomous_onFun
  条件: (hinj : f.单射) [Std.三歧 r]
  证明: hinj Std.Trichotomous.trichotomous (f a) (f b) hab hba

Depends on / 依赖: Std.Trichotomous.trichotomous, Trichotomous, trichotomous
-/
theorem Injective.trichotomous_onFun (hinj : f.Injective) [Std.Trichotomous r] :
    Std.Trichotomous (r on f) where
trichotomous a b hab hba := hinj Std.Trichotomous.trichotomous (f a) (f b) hab hba

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEquiv
  signature: β r] : IsEquiv α (r on f) where

中文:
实例 [Is等价
  签名: β r] : Is等价 α (r on f) where
-/
instance [IsEquiv β r] : IsEquiv α (r on f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPreorder
  signature: β r] : IsPreorder α (r on f) where

中文:
实例 [是预序
  签名: β r] : 是预序 α (r on f) where
-/
instance [IsPreorder β r] : IsPreorder α (r on f) where

variable {f} in
/--
theorem `Injective.isPartialOrder_onFun` / 定理 `Injective.isPartialOrder_onFun`

English:
theorem Injective.isPartialOrder_onFun
  given: (hinj : f.Injective) [IsPartialOrder β r]
  proof: { hinj.antisymm_onFun r with }

中文:
定理 单射.isPartialOrder_onFun
  条件: (hinj : f.单射) [是偏序 β r]
  证明: { hinj.antisymm_onFun r with }

Depends on / 依赖: antisymm_onFun, hinj.antisymm_onFun
-/
theorem Injective.isPartialOrder_onFun (hinj : f.Injective) [IsPartialOrder β r] :
    IsPartialOrder α (r on f) :=
  { hinj.antisymm_onFun r with }

variable {f} in
/--
theorem `Injective.isLinearOrder_onFun` / 定理 `Injective.isLinearOrder_onFun`

English:
theorem Injective.isLinearOrder_onFun
  given: (hinj : f.Injective) [IsLinearOrder β r]
  proof: { hinj.isPartialOrder_onFun r with }

中文:
定理 单射.isLinearOrder_onFun
  条件: (hinj : f.单射) [是线性序 β r]
  证明: { hinj.isPartialOrder_onFun r with }

Depends on / 依赖: hinj.isPartialOrder_onFun, isPartialOrder_onFun
-/
theorem Injective.isLinearOrder_onFun (hinj : f.Injective) [IsLinearOrder β r] :
    IsLinearOrder α (r on f) :=
  { hinj.isPartialOrder_onFun r with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStrictOrder
  signature: β r] : IsStrictOrder α (r on f) where

中文:
实例 [是Strict序
  签名: β r] : 是Strict序 α (r on f) where
-/
instance [IsStrictOrder β r] : IsStrictOrder α (r on f) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStrictWeakOrder
  signature: β r] : IsStrictWeakOrder α (r on f) where
  body: IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

中文:
实例 [是StrictWeak序
  签名: β r] : 是StrictWeak序 α (r on f) where
  定义体: IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

Depends on / 依赖: IsStrictWeakOrder, IsStrictWeakOrder.incomp_trans, incomp_trans
-/
instance [IsStrictWeakOrder β r] : IsStrictWeakOrder α (r on f) where
  incomp_trans _ _ _ := IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

variable {f} in
/--
theorem `Injective.isStrictTotalOrder_onFun` / 定理 `Injective.isStrictTotalOrder_onFun`

English:
theorem Injective.isStrictTotalOrder_onFun
  given: (hinj : f.Injective) [IsStrictTotalOrder β r]
  proof: { hinj.trichotomous_onFun r with }

中文:
定理 单射.isStrictTotalOrder_onFun
  条件: (hinj : f.单射) [是StrictTotal序 β r]
  证明: { hinj.trichotomous_onFun r with }

Depends on / 依赖: hinj.trichotomous_onFun, trichotomous_onFun
-/
theorem Injective.isStrictTotalOrder_onFun (hinj : f.Injective) [IsStrictTotalOrder β r] :
    IsStrictTotalOrder α (r on f) :=
  { hinj.trichotomous_onFun r with }

end onFun

/--
lemma `hfunext` / 引理 `hfunext`

English:
lemma hfunext
  statement: {α α' : Sort u} {β : α -> Sort v} {β' : α' -> Sort v} {f : forall a, β a} {f' : forall a, β' a}
  proof: by
  subst hα
  have : forall a, f a ≍ f' a := fun a => h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  grind

中文:
引理 hfunext
  结论: {α α' : 类型层 u} {β : α -> 类型层 v} {β' : α' -> 类型层 v} {f : 对任意 a, β a} {f' : 对任意 a, β' a}
  证明: by
  subst hα
  have : forall a, f a ≍ f' a := fun a => h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  grind

Depends on / 依赖: HEq.refl, type_eq_of_heq
-/
lemma hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> Sort v} {f : forall a, β a} {f' : forall a, β' a}
    (hα : α = α') (h : forall a a', a ≍ a' -> f a ≍ f' a') : f ≍ f' := by
  subst hα
  have : forall a, f a ≍ f' a := fun a => h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  grind

/--
theorem `ne_iff` / 定理 `ne_iff`

English:
theorem ne_iff
  given: {β : α -> Sort*} {f₁ f₂ : forall a, β a}
  statement: f₁ != f₂ ↔ exists a, f₁ a != f₂ a
  proof: funext_iff.not.trans not_forall

中文:
定理 ne_iff
  条件: {β : α -> 类型层*} {f₁ f₂ : 对任意 a, β a}
  结论: f₁ != f₂ ↔ 存在 a, f₁ a != f₂ a
  证明: funext_iff.not.trans not_forall

Depends on / 依赖: funext_iff, funext_iff.not.trans, not_forall
-/
theorem ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ != f₂ ↔ exists a, f₁ a != f₂ a :=
  funext_iff.not.trans not_forall

/--
lemma `funext_iff_of_subsingleton` / 引理 `funext_iff_of_subsingleton`

English:
lemma funext_iff_of_subsingleton
  given: [Subsingleton α] {g : α -> β} (x y : α)
  proof: by
  refine ⟨fun h => funext fun z => ?_, fun h => ?_⟩
  · rwa [Subsingleton.elim x z, Subsingleton.elim y z] at h
  · rw [h, Subsingleton.elim x y]

中文:
引理 funext_iff_of_subsingleton
  条件: [子单例 α] {g : α -> β} (x y : α)
  证明: by
  refine ⟨fun h => funext fun z => ?_, fun h => ?_⟩
  · rwa [Subsingleton.elim x z, Subsingleton.elim y z] at h
  · rw [h, Subsingleton.elim x y]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma funext_iff_of_subsingleton [Subsingleton α] {g : α -> β} (x y : α) :
    f x = g y ↔ f = g := by
  refine ⟨fun h => funext fun z => ?_, fun h => ?_⟩
  · rwa [Subsingleton.elim x z, Subsingleton.elim y z] at h
  · rw [h, Subsingleton.elim x y]

section swap

/--
theorem `swap_lt` / 定理 `swap_lt`

English:
theorem swap_lt
  given: {α} [LT α]
  statement: swap (· < · : α -> α -> _) = (· > ·)
  proof: rfl

中文:
定理 swap_lt
  条件: {α} [LT α]
  结论: swap (· < · : α -> α -> _) = (· > ·)
  证明: rfl
-/
theorem swap_lt {α} [LT α] : swap (· < · : α -> α -> _) = (· > ·) := rfl
/--
theorem `swap_le` / 定理 `swap_le`

English:
theorem swap_le
  given: {α} [LE α]
  statement: swap (· <= · : α -> α -> _) = (· >= ·)
  proof: rfl

中文:
定理 swap_le
  条件: {α} [LE α]
  结论: swap (· <= · : α -> α -> _) = (· >= ·)
  证明: rfl
-/
theorem swap_le {α} [LE α] : swap (· <= · : α -> α -> _) = (· >= ·) := rfl
/--
theorem `swap_gt` / 定理 `swap_gt`

English:
theorem swap_gt
  given: {α} [LT α]
  statement: swap (· > · : α -> α -> _) = (· < ·)
  proof: rfl

中文:
定理 swap_gt
  条件: {α} [LT α]
  结论: swap (· > · : α -> α -> _) = (· < ·)
  证明: rfl
-/
theorem swap_gt {α} [LT α] : swap (· > · : α -> α -> _) = (· < ·) := rfl
/--
theorem `swap_ge` / 定理 `swap_ge`

English:
theorem swap_ge
  given: {α} [LE α]
  statement: swap (· >= · : α -> α -> _) = (· <= ·)
  proof: rfl

中文:
定理 swap_ge
  条件: {α} [LE α]
  结论: swap (· >= · : α -> α -> _) = (· <= ·)
  证明: rfl
-/
theorem swap_ge {α} [LE α] : swap (· >= · : α -> α -> _) = (· <= ·) := rfl

variable (r : α -> α -> Prop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] : Std.Refl (swap r) where
  body: refl_of r

中文:
实例 [Std.Refl
  签名: r] : Std.Refl (swap r) where
  定义体: refl_of r

Depends on / 依赖: refl_of
-/
instance [Std.Refl r] : Std.Refl (swap r) where
  refl := refl_of r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Irrefl
  signature: r] : Std.Irrefl (swap r) where
  body: irrefl_of r

中文:
实例 [Std.Irrefl
  签名: r] : Std.Irrefl (swap r) where
  定义体: irrefl_of r

Depends on / 依赖: irrefl_of
-/
instance [Std.Irrefl r] : Std.Irrefl (swap r) where
  irrefl := irrefl_of r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Symm
  signature: r] : Std.Symm (swap r) where
  body: symm_of r

中文:
实例 [Std.Symm
  签名: r] : Std.Symm (swap r) where
  定义体: symm_of r

Depends on / 依赖: symm_of
-/
instance [Std.Symm r] : Std.Symm (swap r) where
  symm _ _ := symm_of r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Antisymm
  signature: r] : Std.Antisymm (swap r) where
  body: antisymm_of r hab hba

中文:
实例 [Std.反对称
  签名: r] : Std.反对称 (swap r) where
  定义体: antisymm_of r hab hba

Depends on / 依赖: antisymm_of
-/
instance [Std.Antisymm r] : Std.Antisymm (swap r) where
.symm antisymm _ _ hab hba := antisymm_of r hab hba

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Asymm
  signature: r] : Std.Asymm (swap r) where
  body: asymm_of r

中文:
实例 [Std.Asymm
  签名: r] : Std.Asymm (swap r) where
  定义体: asymm_of r

Depends on / 依赖: asymm_of
-/
instance [Std.Asymm r] : Std.Asymm (swap r) where
  asymm _ _ := asymm_of r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTrans
  signature: α r] : IsTrans α (swap r) where
  body: trans_of r hbc hab

中文:
实例 [是Trans
  签名: α r] : 是Trans α (swap r) where
  定义体: trans_of r hbc hab

Depends on / 依赖: trans_of
-/
instance [IsTrans α r] : IsTrans α (swap r) where
  trans _ _ _ hab hbc := trans_of r hbc hab

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Total
  signature: r] : Std.Total (swap r) where
  body: total_of r _ _

中文:
实例 [Std.全
  签名: r] : Std.全 (swap r) where
  定义体: total_of r _ _

Depends on / 依赖: total_of
-/
instance [Std.Total r] : Std.Total (swap r) where
  total _ _ := total_of r _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Trichotomous
  signature: r] : Std.Trichotomous (swap r) where
  body: Std.Trichotomous.trichotomous a b hba hab

中文:
实例 [Std.三歧
  签名: r] : Std.三歧 (swap r) where
  定义体: Std.Trichotomous.trichotomous a b hba hab

Depends on / 依赖: Std.Trichotomous.trichotomous, Trichotomous, trichotomous
-/
instance [Std.Trichotomous r] : Std.Trichotomous (swap r) where
  trichotomous a b hab hba := Std.Trichotomous.trichotomous a b hba hab

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEquiv
  signature: α r] : IsEquiv α (swap r) where

中文:
实例 [Is等价
  签名: α r] : Is等价 α (swap r) where
-/
instance [IsEquiv α r] : IsEquiv α (swap r) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPreorder
  signature: α r] : IsPreorder α (swap r) where

中文:
实例 [是预序
  签名: α r] : 是预序 α (swap r) where
-/
instance [IsPreorder α r] : IsPreorder α (swap r) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsPartialOrder
  signature: α r] : IsPartialOrder α (swap r) where

中文:
实例 [是偏序
  签名: α r] : 是偏序 α (swap r) where
-/
instance [IsPartialOrder α r] : IsPartialOrder α (swap r) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLinearOrder
  signature: α r] : IsLinearOrder α (swap r) where

中文:
实例 [是线性序
  签名: α r] : 是线性序 α (swap r) where
-/
instance [IsLinearOrder α r] : IsLinearOrder α (swap r) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStrictOrder
  signature: α r] : IsStrictOrder α (swap r) where

中文:
实例 [是Strict序
  签名: α r] : 是Strict序 α (swap r) where
-/
instance [IsStrictOrder α r] : IsStrictOrder α (swap r) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStrictWeakOrder
  signature: α r] : IsStrictWeakOrder α (swap r) where
  body: IsStrictWeakOrder.incomp_trans a b c hab.symm hbc.symm

中文:
实例 [是StrictWeak序
  签名: α r] : 是StrictWeak序 α (swap r) where
  定义体: IsStrictWeakOrder.incomp_trans a b c hab.symm hbc.symm

Depends on / 依赖: IsStrictWeakOrder, IsStrictWeakOrder.incomp_trans, hab.symm, hbc.symm, incomp_trans
-/
instance [IsStrictWeakOrder α r] : IsStrictWeakOrder α (swap r) where
.symm incomp_trans a b c hab hbc := IsStrictWeakOrder.incomp_trans a b c hab.symm hbc.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStrictTotalOrder
  signature: α r] : IsStrictTotalOrder α (swap r) where

中文:
实例 [是StrictTotal序
  签名: α r] : 是StrictTotal序 α (swap r) where
-/
instance [IsStrictTotalOrder α r] : IsStrictTotalOrder α (swap r) where

end swap

/--
theorem `Bijective.injective` / 定理 `Bijective.injective`

English:
theorem Bijective.injective
  given: {f : α -> β} (hf : Bijective f)
  statement: Injective f
  proof: hf.1

中文:
定理 双射.injective
  条件: {f : α -> β} (hf : 双射 f)
  结论: 单射 f
  证明: hf.1
-/
protected theorem Bijective.injective {f : α -> β} (hf : Bijective f) : Injective f := hf.1
/--
theorem `Bijective.surjective` / 定理 `Bijective.surjective`

English:
theorem Bijective.surjective
  given: {f : α -> β} (hf : Bijective f)
  statement: Surjective f
  proof: hf.2

中文:
定理 双射.surjective
  条件: {f : α -> β} (hf : 双射 f)
  结论: 满射 f
  证明: hf.2
-/
protected theorem Bijective.surjective {f : α -> β} (hf : Bijective f) : Surjective f := hf.2

/--
theorem `not_injective_iff` / 定理 `not_injective_iff`

English:
theorem not_injective_iff
  statement: ¬ Injective f ↔ exists a b, f a = f b ∧ a != b
  proof: by
  simp only [Injective, not_forall, exists_prop]

中文:
定理 not_injective_iff
  结论: ¬ 单射 f ↔ 存在 a b, f a = f b ∧ a != b
  证明: by
  simp only [Injective, not_forall, exists_prop]

Depends on / 依赖: Injective, exists_prop, not_forall
-/
theorem not_injective_iff : ¬ Injective f ↔ exists a b, f a = f b ∧ a != b := by
  simp only [Injective, not_forall, exists_prop]

/--
lemma `not_injective_const` / 引理 `not_injective_const`

English:
lemma not_injective_const
  given: {α β : Type*} [Nontrivial α] {b : β}
  proof: by
  rw [not_injective_iff]
  obtain ⟨a₁, a₂, h⟩ := exists_pair_ne α
  exact ⟨a₁, a₂, rfl, h⟩

中文:
引理 not_injective_const
  条件: {α β : 类型} [非平凡 α] {b : β}
  证明: by
  rw [not_injective_iff]
  obtain ⟨a₁, a₂, h⟩ := exists_pair_ne α
  exact ⟨a₁, a₂, rfl, h⟩
-/
@[simp] lemma not_injective_const {α β : Type*} [Nontrivial α] {b : β} :
    ¬ Injective (fun _ : α => b) := by
  rw [not_injective_iff]
  obtain ⟨a₁, a₂, h⟩ := exists_pair_ne α
  exact ⟨a₁, a₂, rfl, h⟩

/--
Definition of `Injective.decidableEq` / `Injective.decidableEq` 的定义

English:
definition Injective.decidableEq
  signature: [DecidableEq β] (I : Injective f)
  body: fun _ _ => decidable_of_iff _ I.eq_iff

中文:
定义 单射.decidableEq
  签名: [DecidableEq β] (I : 单射 f)
  定义体: fun _ _ => decidable_of_iff _ I.eq_iff
-/
protected def Injective.decidableEq [DecidableEq β] (I : Injective f) : DecidableEq α :=
  fun _ _ => decidable_of_iff _ I.eq_iff

/--
theorem `Injective.of_comp` / 定理 `Injective.of_comp`

English:
theorem Injective.of_comp
  given: {g : γ -> α} (I : Injective (f ∘ g))
  statement: Injective g
  proof: fun _ _ h => I congr_arg f h

@[simp]

中文:
定理 单射.of_comp
  条件: {g : γ -> α} (I : 单射 (f ∘ g))
  结论: 单射 g
  证明: fun _ _ h => I congr_arg f h

@[simp]

Depends on / 依赖: congr_arg
-/
theorem Injective.of_comp {g : γ -> α} (I : Injective (f ∘ g)) : Injective g :=
fun _ _ h => I congr_arg f h

@[simp]
/--
theorem `Injective.of_comp_iff` / 定理 `Injective.of_comp_iff`

English:
theorem Injective.of_comp_iff
  given: (hf : Injective f) (g : γ -> α)
  proof: ⟨Injective.of_comp, hf.comp⟩

中文:
定理 单射.of_comp_iff
  条件: (hf : 单射 f) (g : γ -> α)
  证明: ⟨Injective.of_comp, hf.comp⟩

Depends on / 依赖: Injective, Injective.of_comp, hf.comp, of_comp
-/
theorem Injective.of_comp_iff (hf : Injective f) (g : γ -> α) :
    Injective (f ∘ g) ↔ Injective g :=
  ⟨Injective.of_comp, hf.comp⟩

/--
theorem `Injective.of_comp_right` / 定理 `Injective.of_comp_right`

English:
theorem Injective.of_comp_right
  given: {g : γ -> α} (I : Injective (f ∘ g)) (hg : Surjective g)
  proof: fun x y h => by
  obtain ⟨x, rfl⟩ := hg x
  obtain ⟨y, rfl⟩ := hg y
  exact congr_arg g (I h)

中文:
定理 单射.of_comp_right
  条件: {g : γ -> α} (I : 单射 (f ∘ g)) (hg : 满射 g)
  证明: fun x y h => by
  obtain ⟨x, rfl⟩ := hg x
  obtain ⟨y, rfl⟩ := hg y
  exact congr_arg g (I h)

Depends on / 依赖: congr_arg
-/
theorem Injective.of_comp_right {g : γ -> α} (I : Injective (f ∘ g)) (hg : Surjective g) :
    Injective f := fun x y h => by
  obtain ⟨x, rfl⟩ := hg x
  obtain ⟨y, rfl⟩ := hg y
  exact congr_arg g (I h)

/--
theorem `Surjective.bijective₂_of_injective` / 定理 `Surjective.bijective₂_of_injective`

English:
theorem Surjective.bijective₂_of_injective
  statement: {g : γ -> α} (hf : Surjective f) (hg : Surjective g)
  proof: ⟨⟨I.of_comp_right hg, hf⟩, I.of_comp, hg⟩

@[simp]

中文:
定理 满射.bijective₂_of_injective
  结论: {g : γ -> α} (hf : 满射 f) (hg : 满射 g)
  证明: ⟨⟨I.of_comp_right hg, hf⟩, I.of_comp, hg⟩

@[simp]

Depends on / 依赖: I.of_comp, I.of_comp_right, of_comp, of_comp_right
-/
theorem Surjective.bijective₂_of_injective {g : γ -> α} (hf : Surjective f) (hg : Surjective g)
    (I : Injective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨I.of_comp_right hg, hf⟩, I.of_comp, hg⟩

@[simp]
/--
theorem `Injective.of_comp_iff'` / 定理 `Injective.of_comp_iff'`

English:
theorem Injective.of_comp_iff'
  given: (f : α -> β) {g : γ -> α} (hg : Bijective g)
  proof: ⟨fun I => I.of_comp_right hg.2, fun h => h.comp hg.injective⟩

中文:
定理 单射.of_comp_iff'
  条件: (f : α -> β) {g : γ -> α} (hg : 双射 g)
  证明: ⟨fun I => I.of_comp_right hg.2, fun h => h.comp hg.injective⟩

Depends on / 依赖: I.of_comp_right, h.comp, hg.injective, injective, of_comp_right
-/
theorem Injective.of_comp_iff' (f : α -> β) {g : γ -> α} (hg : Bijective g) :
    Injective (f ∘ g) ↔ Injective f :=
  ⟨fun I => I.of_comp_right hg.2, fun h => h.comp hg.injective⟩

/--
theorem `Injective.piMap` / 定理 `Injective.piMap`

English:
theorem Injective.piMap
  statement: {ι : Sort*} {α β : ι -> Sort*} {f : forall i, α i -> β i}
  proof: fun _ _ h =>
funext fun i => hf i congrFun h _

中文:
定理 单射.piMap
  结论: {ι : 类型层*} {α β : ι -> 类型层*} {f : 对任意 i, α i -> β i}
  证明: fun _ _ h =>
funext fun i => hf i congrFun h _
-/
theorem Injective.piMap {ι : Sort*} {α β : ι -> Sort*} {f : forall i, α i -> β i}
    (hf : forall i, Injective (f i)) : Injective (Pi.map f) := fun _ _ h =>
funext fun i => hf i congrFun h _

/--
theorem `Injective.comp_left` / 定理 `Injective.comp_left`

English:
theorem Injective.comp_left
  given: {g : β -> γ} (hg : Injective g)
  statement: Injective (g ∘ · : (α -> β) -> α -> γ)
  proof: .piMap fun _ => hg

中文:
定理 单射.comp_left
  条件: {g : β -> γ} (hg : 单射 g)
  结论: 单射 (g ∘ · : (α -> β) -> α -> γ)
  证明: .piMap fun _ => hg
-/
theorem Injective.comp_left {g : β -> γ} (hg : Injective g) : Injective (g ∘ · : (α -> β) -> α -> γ) :=
  .piMap fun _ => hg

/--
theorem `injective_comp_left_iff` / 定理 `injective_comp_left_iff`

English:
theorem injective_comp_left_iff
  given: [Nonempty α] {g : β -> γ}
  proof: ⟨fun h b₁ b₂ eq => Nonempty.elim ‹_›
    (congr_fun <| h (a₁ := fun _ => b₁) (a₂ := fun _ => b₂) <| funext fun _ => eq), (·.comp_left)⟩

中文:
定理 injective_comp_left_iff
  条件: [非空 α] {g : β -> γ}
  证明: ⟨fun h b₁ b₂ eq => Nonempty.elim ‹_›
    (congr_fun <| h (a₁ := fun _ => b₁) (a₂ := fun _ => b₂) <| funext fun _ => eq), (·.comp_left)⟩

Depends on / 依赖: Nonempty, Nonempty.elim, comp_left, congr_fun
-/
theorem injective_comp_left_iff [Nonempty α] {g : β -> γ} :
    Injective (g ∘ · : (α -> β) -> α -> γ) ↔ Injective g :=
  ⟨fun h b₁ b₂ eq => Nonempty.elim ‹_›
    (congr_fun <| h (a₁ := fun _ => b₁) (a₂ := fun _ => b₂) <| funext fun _ => eq), (·.comp_left)⟩

/--
theorem `injective_of_subsingleton` / 定理 `injective_of_subsingleton`

English:
theorem injective_of_subsingleton
  given: [Subsingleton α] (f : α -> β)
  statement: Injective f
  proof: fun _ _ _ => Subsingleton.elim _ _

中文:
定理 injective_of_subsingleton
  条件: [子单例 α] (f : α -> β)
  结论: 单射 f
  证明: fun _ _ _ => Subsingleton.elim _ _
-/
@[nontriviality] theorem injective_of_subsingleton [Subsingleton α] (f : α -> β) : Injective f :=
  fun _ _ _ => Subsingleton.elim _ _

/--
theorem `bijective_of_subsingleton` / 定理 `bijective_of_subsingleton`

English:
theorem bijective_of_subsingleton
  given: [Subsingleton α] (f : α -> α)
  statement: Bijective f
  proof: ⟨injective_of_subsingleton f, fun a => ⟨a, Subsingleton.elim ..⟩⟩

中文:
定理 bijective_of_subsingleton
  条件: [子单例 α] (f : α -> α)
  结论: 双射 f
  证明: ⟨injective_of_subsingleton f, fun a => ⟨a, Subsingleton.elim ..⟩⟩
-/
@[nontriviality] theorem bijective_of_subsingleton [Subsingleton α] (f : α -> α) : Bijective f :=
  ⟨injective_of_subsingleton f, fun a => ⟨a, Subsingleton.elim ..⟩⟩

/--
lemma `Injective.dite` / 引理 `Injective.dite`

English:
lemma Injective.dite
  statement: (p : α -> Prop) [DecidablePred p]
  proof: fun x₁ x₂ h => by
  grind

中文:
引理 单射.dite
  结论: (p : α -> 命题) [DecidablePred p]
  证明: fun x₁ x₂ h => by
  grind
-/
lemma Injective.dite (p : α -> Prop) [DecidablePred p]
    {f : {a : α // p a} -> β} {f' : {a : α // ¬ p a} -> β}
    (hf : Injective f) (hf' : Injective f')
    (im_disj : forall {x x' : α} {hx : p x} {hx' : ¬ p x'}, f ⟨x, hx⟩ != f' ⟨x', hx'⟩) :
    Function.Injective (fun x => if h : p x then f ⟨x, h⟩ else f' ⟨x, h⟩) := fun x₁ x₂ h => by
  grind

/--
theorem `Surjective.of_comp` / 定理 `Surjective.of_comp`

English:
theorem Surjective.of_comp
  given: {g : γ -> α} (S : Surjective (f ∘ g))
  statement: Surjective f
  proof: fun y =>
  let ⟨x, h⟩ := S y
  ⟨g x, h⟩

@[simp]

中文:
定理 满射.of_comp
  条件: {g : γ -> α} (S : 满射 (f ∘ g))
  结论: 满射 f
  证明: fun y =>
  let ⟨x, h⟩ := S y
  ⟨g x, h⟩

@[simp]
-/
theorem Surjective.of_comp {g : γ -> α} (S : Surjective (f ∘ g)) : Surjective f := fun y =>
  let ⟨x, h⟩ := S y
  ⟨g x, h⟩

@[simp]
/--
theorem `Surjective.of_comp_iff` / 定理 `Surjective.of_comp_iff`

English:
theorem Surjective.of_comp_iff
  given: (f : α -> β) {g : γ -> α} (hg : Surjective g)
  proof: ⟨Surjective.of_comp, fun h => h.comp hg⟩

中文:
定理 满射.of_comp_iff
  条件: (f : α -> β) {g : γ -> α} (hg : 满射 g)
  证明: ⟨Surjective.of_comp, fun h => h.comp hg⟩

Depends on / 依赖: Surjective, Surjective.of_comp, h.comp, of_comp
-/
theorem Surjective.of_comp_iff (f : α -> β) {g : γ -> α} (hg : Surjective g) :
    Surjective (f ∘ g) ↔ Surjective f :=
  ⟨Surjective.of_comp, fun h => h.comp hg⟩

/--
theorem `Surjective.of_comp_left` / 定理 `Surjective.of_comp_left`

English:
theorem Surjective.of_comp_left
  given: {g : γ -> α} (S : Surjective (f ∘ g)) (hf : Injective f)
  proof: fun a => let ⟨c, hc⟩ := S (f a); ⟨c, hf hc⟩

中文:
定理 满射.of_comp_left
  条件: {g : γ -> α} (S : 满射 (f ∘ g)) (hf : 单射 f)
  证明: fun a => let ⟨c, hc⟩ := S (f a); ⟨c, hf hc⟩
-/
theorem Surjective.of_comp_left {g : γ -> α} (S : Surjective (f ∘ g)) (hf : Injective f) :
    Surjective g := fun a => let ⟨c, hc⟩ := S (f a); ⟨c, hf hc⟩

/--
theorem `Injective.bijective₂_of_surjective` / 定理 `Injective.bijective₂_of_surjective`

English:
theorem Injective.bijective₂_of_surjective
  statement: {g : γ -> α} (hf : Injective f) (hg : Injective g)
  proof: ⟨⟨hf, S.of_comp⟩, hg, S.of_comp_left hf⟩

@[simp]

中文:
定理 单射.bijective₂_of_surjective
  结论: {g : γ -> α} (hf : 单射 f) (hg : 单射 g)
  证明: ⟨⟨hf, S.of_comp⟩, hg, S.of_comp_left hf⟩

@[simp]

Depends on / 依赖: S.of_comp, S.of_comp_left, of_comp, of_comp_left
-/
theorem Injective.bijective₂_of_surjective {g : γ -> α} (hf : Injective f) (hg : Injective g)
    (S : Surjective (f ∘ g)) : Bijective f ∧ Bijective g :=
  ⟨⟨hf, S.of_comp⟩, hg, S.of_comp_left hf⟩

@[simp]
/--
theorem `Surjective.of_comp_iff'` / 定理 `Surjective.of_comp_iff'`

English:
theorem Surjective.of_comp_iff'
  given: (hf : Bijective f) (g : γ -> α)
  proof: ⟨fun S => S.of_comp_left hf.1, hf.surjective.comp⟩

中文:
定理 满射.of_comp_iff'
  条件: (hf : 双射 f) (g : γ -> α)
  证明: ⟨fun S => S.of_comp_left hf.1, hf.surjective.comp⟩

Depends on / 依赖: S.of_comp_left, hf.surjective.comp, of_comp_left, surjective
-/
theorem Surjective.of_comp_iff' (hf : Bijective f) (g : γ -> α) :
    Surjective (f ∘ g) ↔ Surjective g :=
  ⟨fun S => S.of_comp_left hf.1, hf.surjective.comp⟩

/--
Instance `decidableEqPFun` / 实例 `decidableEqPFun`

English:
instance decidableEqPFun
  signature: (p : Prop) [Decidable p] (α : p -> Type*) [forall hp, DecidableEq (α hp)]

中文:
实例 decidableEqPFun
  签名: (p : 命题) [可判定 p] (α : p -> 类型) [对任意 hp, DecidableEq (α hp)]
-/
instance decidableEqPFun (p : Prop) [Decidable p] (α : p -> Type*) [forall hp, DecidableEq (α hp)] :
    DecidableEq (forall hp, α hp)
  | f, g => decidable_of_iff (forall hp, f hp = g hp) funext_iff.symm

/--
theorem `Surjective.forall` / 定理 `Surjective.forall`

English:
theorem Surjective.forall
  given: (hf : Surjective f) {p : β -> Prop}
  proof: ⟨fun h x => h (f x), fun h y =>
    let ⟨x, hx⟩ := hf y
    hx ▸ h x⟩

中文:
定理 满射.对任意
  条件: (hf : 满射 f) {p : β -> 命题}
  证明: ⟨fun h x => h (f x), fun h y =>
    let ⟨x, hx⟩ := hf y
    hx ▸ h x⟩
-/
protected theorem Surjective.forall (hf : Surjective f) {p : β -> Prop} :
    (forall y, p y) ↔ forall x, p (f x) :=
  ⟨fun h x => h (f x), fun h y =>
    let ⟨x, hx⟩ := hf y
    hx ▸ h x⟩

/--
theorem `Surjective.forall₂` / 定理 `Surjective.forall₂`

English:
theorem Surjective.forall₂
  given: (hf : Surjective f) {p : β -> β -> Prop}
  proof: hf.forall.trans forall_congr' fun _ => hf.forall

中文:
定理 满射.对任意₂
  条件: (hf : 满射 f) {p : β -> β -> 命题}
  证明: hf.forall.trans forall_congr' fun _ => hf.forall
-/
protected theorem Surjective.forall₂ (hf : Surjective f) {p : β -> β -> Prop} :
    (forall y₁ y₂, p y₁ y₂) ↔ forall x₁ x₂, p (f x₁) (f x₂) :=
hf.forall.trans forall_congr' fun _ => hf.forall

/--
theorem `Surjective.forall₃` / 定理 `Surjective.forall₃`

English:
theorem Surjective.forall₃
  given: (hf : Surjective f) {p : β -> β -> β -> Prop}
  proof: hf.forall.trans forall_congr' fun _ => hf.forall₂

中文:
定理 满射.对任意₃
  条件: (hf : 满射 f) {p : β -> β -> β -> 命题}
  证明: hf.forall.trans forall_congr' fun _ => hf.forall₂
-/
protected theorem Surjective.forall₃ (hf : Surjective f) {p : β -> β -> β -> Prop} :
    (forall y₁ y₂ y₃, p y₁ y₂ y₃) ↔ forall x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.forall.trans forall_congr' fun _ => hf.forall₂

/--
theorem `Surjective.exists` / 定理 `Surjective.exists`

English:
theorem Surjective.exists
  given: (hf : Surjective f) {p : β -> Prop}
  proof: ⟨fun ⟨y, hy⟩ =>
    let ⟨x, hx⟩ := hf y
    ⟨x, hx.symm ▸ hy⟩,
    fun ⟨x, hx⟩ => ⟨f x, hx⟩⟩

中文:
定理 满射.存在
  条件: (hf : 满射 f) {p : β -> 命题}
  证明: ⟨fun ⟨y, hy⟩ =>
    let ⟨x, hx⟩ := hf y
    ⟨x, hx.symm ▸ hy⟩,
    fun ⟨x, hx⟩ => ⟨f x, hx⟩⟩
-/
protected theorem Surjective.exists (hf : Surjective f) {p : β -> Prop} :
    (exists y, p y) ↔ exists x, p (f x) :=
  ⟨fun ⟨y, hy⟩ =>
    let ⟨x, hx⟩ := hf y
    ⟨x, hx.symm ▸ hy⟩,
    fun ⟨x, hx⟩ => ⟨f x, hx⟩⟩

/--
theorem `Surjective.exists₂` / 定理 `Surjective.exists₂`

English:
theorem Surjective.exists₂
  given: (hf : Surjective f) {p : β -> β -> Prop}
  proof: hf.exists.trans exists_congr fun _ => hf.exists

中文:
定理 满射.存在₂
  条件: (hf : 满射 f) {p : β -> β -> 命题}
  证明: hf.exists.trans exists_congr fun _ => hf.exists
-/
protected theorem Surjective.exists₂ (hf : Surjective f) {p : β -> β -> Prop} :
    (exists y₁ y₂, p y₁ y₂) ↔ exists x₁ x₂, p (f x₁) (f x₂) :=
hf.exists.trans exists_congr fun _ => hf.exists

/--
theorem `Surjective.exists₃` / 定理 `Surjective.exists₃`

English:
theorem Surjective.exists₃
  given: (hf : Surjective f) {p : β -> β -> β -> Prop}
  proof: hf.exists.trans exists_congr fun _ => hf.exists₂

中文:
定理 满射.存在₃
  条件: (hf : 满射 f) {p : β -> β -> β -> 命题}
  证明: hf.exists.trans exists_congr fun _ => hf.exists₂

Depends on / 依赖: _pos, beattySeq_symmDiff_beattySeq, hrs.symm, symmDiff_comm
-/
protected theorem Surjective.exists₃ (hf : Surjective f) {p : β -> β -> β -> Prop} :
    (exists y₁ y₂ y₃, p y₁ y₂ y₃) ↔ exists x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.exists.trans exists_congr fun _ => hf.exists₂

/--
theorem `Surjective.injective_comp_right` / 定理 `Surjective.injective_comp_right`

English:
theorem Surjective.injective_comp_right
  given: (hf : Surjective f)
  statement: Injective fun g : β -> γ => g ∘ f
  proof: fun _ _ h => funext hf.forall.2 congr_fun h

中文:
定理 满射.injective_comp_right
  条件: (hf : 满射 f)
  结论: 单射 fun g : β -> γ => g ∘ f
  证明: fun _ _ h => funext hf.forall.2 congr_fun h

Depends on / 依赖: congr_fun, hf.forall
-/
theorem Surjective.injective_comp_right (hf : Surjective f) : Injective fun g : β -> γ => g ∘ f :=
fun _ _ h => funext hf.forall.2 congr_fun h

/--
theorem `injective_comp_right_iff_surjective` / 定理 `injective_comp_right_iff_surjective`

English:
theorem injective_comp_right_iff_surjective
  given: {γ : Type*} [Nontrivial γ]
  proof: by
  refine ⟨not_imp_not.mp fun not_surj inj => not_subsingleton γ ⟨fun c c' => ?_⟩,
    (·.injective_comp_right)⟩
  have ⟨b₀, hb⟩ := not_forall.mp not_surj
  classical have := inj (a₁ := fun _ => c) (a₂ := (if · = b₀ then c' else c)) ?_
  · simpa using congr_fun this b₀
  ext a; simp only [comp_app

中文:
定理 injective_comp_right_iff_surjective
  条件: {γ : 类型} [非平凡 γ]
  证明: by
  refine ⟨not_imp_not.mp fun not_surj inj => not_subsingleton γ ⟨fun c c' => ?_⟩,
    (·.injective_comp_right)⟩
  have ⟨b₀, hb⟩ := not_forall.mp not_surj
  classical have := inj (a₁ := fun _ => c) (a₂ := (if · = b₀ then c' else c)) ?_
  · simpa using congr_fun this b₀
  ext a; simp only [comp_app

Depends on / 依赖: classical, comp_apply, congr_fun, if_neg, injective_comp_right, not_forall, not_forall.mp, not_imp_not, not_imp_not.mp, not_subsingleton, not_surj
-/
theorem injective_comp_right_iff_surjective {γ : Type*} [Nontrivial γ] :
    Injective (fun g : β -> γ => g ∘ f) ↔ Surjective f := by
  refine ⟨not_imp_not.mp fun not_surj inj => not_subsingleton γ ⟨fun c c' => ?_⟩,
    (·.injective_comp_right)⟩
  have ⟨b₀, hb⟩ := not_forall.mp not_surj
  classical have := inj (a₁ := fun _ => c) (a₂ := (if · = b₀ then c' else c)) ?_
  · simpa using congr_fun this b₀
  ext a; simp only [comp_apply, if_neg fun h => hb ⟨a, h⟩]

/--
theorem `Surjective.right_cancellable` / 定理 `Surjective.right_cancellable`

English:
theorem Surjective.right_cancellable
  given: (hf : Surjective f) {g₁ g₂ : β -> γ}
  proof: hf.injective_comp_right.eq_iff

中文:
定理 满射.right_cancellable
  条件: (hf : 满射 f) {g₁ g₂ : β -> γ}
  证明: hf.injective_comp_right.eq_iff
-/
protected theorem Surjective.right_cancellable (hf : Surjective f) {g₁ g₂ : β -> γ} :
    g₁ ∘ f = g₂ ∘ f ↔ g₁ = g₂ :=
  hf.injective_comp_right.eq_iff

/--
theorem `surjective_of_right_cancellable_Prop` / 定理 `surjective_of_right_cancellable_Prop`

English:
theorem surjective_of_right_cancellable_Prop
  given: (h : forall g₁ g₂ : β -> Prop, g₁ ∘ f = g₂ ∘ f -> g₁ = g₂)
  proof: injective_comp_right_iff_surjective.mp h

中文:
定理 surjective_of_right_cancellable_Prop
  条件: (h : 对任意 g₁ g₂ : β -> 命题, g₁ ∘ f = g₂ ∘ f -> g₁ = g₂)
  证明: injective_comp_right_iff_surjective.mp h

Depends on / 依赖: injective_comp_right_iff_surjective, injective_comp_right_iff_surjective.mp
-/
theorem surjective_of_right_cancellable_Prop (h : forall g₁ g₂ : β -> Prop, g₁ ∘ f = g₂ ∘ f -> g₁ = g₂) :
    Surjective f :=
  injective_comp_right_iff_surjective.mp h

/--
theorem `bijective_iff_existsUnique` / 定理 `bijective_iff_existsUnique`

English:
theorem bijective_iff_existsUnique
  given: (f : α -> β)
  statement: Bijective f ↔ forall b : β, exists! a : α, f a = b
  proof: ⟨fun hf b =>
      let ⟨a, ha⟩ := hf.surjective b
      ⟨a, ha, fun _ ha' => hf.injective (ha'.trans ha.symm)⟩,
    fun he => ⟨fun {_a a'} h => (he (f a')).unique h rfl, fun b => (he b).exists⟩⟩

中文:
定理 bijective_iff_存在Unique
  条件: (f : α -> β)
  结论: 双射 f ↔ 对任意 b : β, 存在! a : α, f a = b
  证明: ⟨fun hf b =>
      let ⟨a, ha⟩ := hf.surjective b
      ⟨a, ha, fun _ ha' => hf.injective (ha'.trans ha.symm)⟩,
    fun he => ⟨fun {_a a'} h => (he (f a')).unique h rfl, fun b => (he b).exists⟩⟩

Depends on / 依赖: ha.symm, hf.injective, hf.surjective, injective, surjective, unique
-/
theorem bijective_iff_existsUnique (f : α -> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b :=
  ⟨fun hf b =>
      let ⟨a, ha⟩ := hf.surjective b
      ⟨a, ha, fun _ ha' => hf.injective (ha'.trans ha.symm)⟩,
    fun he => ⟨fun {_a a'} h => (he (f a')).unique h rfl, fun b => (he b).exists⟩⟩

/--
theorem `Bijective.existsUnique` / 定理 `Bijective.existsUnique`

English:
theorem Bijective.existsUnique
  given: {f : α -> β} (hf : Bijective f) (b : β)
  proof: (bijective_iff_existsUnique f).mp hf b

中文:
定理 双射.存在Unique
  条件: {f : α -> β} (hf : 双射 f) (b : β)
  证明: (bijective_iff_existsUnique f).mp hf b
-/
protected theorem Bijective.existsUnique {f : α -> β} (hf : Bijective f) (b : β) :
    exists! a : α, f a = b :=
  (bijective_iff_existsUnique f).mp hf b

/--
theorem `Bijective.existsUnique_iff` / 定理 `Bijective.existsUnique_iff`

English:
theorem Bijective.existsUnique_iff
  given: {f : α -> β} (hf : Bijective f) {p : β -> Prop}
  proof: ⟨fun ⟨y, hpy, hy⟩ =>
    let ⟨x, hx⟩ := hf.surjective y
⟨x, by simpa [hx], fun z (hz : p (f z)) => hf.injective hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ =>
    ⟨f x, hpx, fun y hy =>
      let ⟨z, hz⟩ := hf.surjective y
      hz ▸ congr_arg f (hx _ (by simpa [hz]))⟩⟩

中文:
定理 双射.存在Unique_iff
  条件: {f : α -> β} (hf : 双射 f) {p : β -> 命题}
  证明: ⟨fun ⟨y, hpy, hy⟩ =>
    let ⟨x, hx⟩ := hf.surjective y
⟨x, by simpa [hx], fun z (hz : p (f z)) => hf.injective hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ =>
    ⟨f x, hpx, fun y hy =>
      let ⟨z, hz⟩ := hf.surjective y
      hz ▸ congr_arg f (hx _ (by simpa [hz]))⟩⟩

Depends on / 依赖: congr_arg, hf.injective, hf.surjective, hx.symm, injective, surjective
-/
theorem Bijective.existsUnique_iff {f : α -> β} (hf : Bijective f) {p : β -> Prop} :
    (exists! y, p y) ↔ exists! x, p (f x) :=
  ⟨fun ⟨y, hpy, hy⟩ =>
    let ⟨x, hx⟩ := hf.surjective y
⟨x, by simpa [hx], fun z (hz : p (f z)) => hf.injective hx.symm ▸ hy _ hz⟩,
    fun ⟨x, hpx, hx⟩ =>
    ⟨f x, hpx, fun y hy =>
      let ⟨z, hz⟩ := hf.surjective y
      hz ▸ congr_arg f (hx _ (by simpa [hz]))⟩⟩

/--
theorem `Bijective.of_comp_iff` / 定理 `Bijective.of_comp_iff`

English:
theorem Bijective.of_comp_iff
  given: (f : α -> β) {g : γ -> α} (hg : Bijective g)
  proof: and_congr (Injective.of_comp_iff' _ hg) (Surjective.of_comp_iff _ hg.surjective)

中文:
定理 双射.of_comp_iff
  条件: (f : α -> β) {g : γ -> α} (hg : 双射 g)
  证明: and_congr (Injective.of_comp_iff' _ hg) (Surjective.of_comp_iff _ hg.surjective)

Depends on / 依赖: Injective, Injective.of_comp_iff, Surjective, Surjective.of_comp_iff, and_congr, hg.surjective, of_comp_iff, surjective
-/
theorem Bijective.of_comp_iff (f : α -> β) {g : γ -> α} (hg : Bijective g) :
    Bijective (f ∘ g) ↔ Bijective f :=
  and_congr (Injective.of_comp_iff' _ hg) (Surjective.of_comp_iff _ hg.surjective)

/--
theorem `Bijective.of_comp_iff'` / 定理 `Bijective.of_comp_iff'`

English:
theorem Bijective.of_comp_iff'
  given: {f : α -> β} (hf : Bijective f) (g : γ -> α)
  proof: and_congr (Injective.of_comp_iff hf.injective _) (Surjective.of_comp_iff' hf _)

中文:
定理 双射.of_comp_iff'
  条件: {f : α -> β} (hf : 双射 f) (g : γ -> α)
  证明: and_congr (Injective.of_comp_iff hf.injective _) (Surjective.of_comp_iff' hf _)

Depends on / 依赖: Injective, Injective.of_comp_iff, Surjective, Surjective.of_comp_iff, and_congr, hf.injective, injective, of_comp_iff
-/
theorem Bijective.of_comp_iff' {f : α -> β} (hf : Bijective f) (g : γ -> α) :
    Function.Bijective (f ∘ g) ↔ Function.Bijective g :=
  and_congr (Injective.of_comp_iff hf.injective _) (Surjective.of_comp_iff' hf _)

/--
theorem `Bijective.of_comp_left` / 定理 `Bijective.of_comp_left`

English:
theorem Bijective.of_comp_left
  statement: {f : α -> β} {g : γ -> α} (hfg : Function.Bijective (f ∘ g))
  proof: ⟨hfg.1.of_comp, hfg.2.of_comp_left hf⟩

中文:
定理 双射.of_comp_left
  结论: {f : α -> β} {g : γ -> α} (hfg : 函数.双射 (f ∘ g))
  证明: ⟨hfg.1.of_comp, hfg.2.of_comp_left hf⟩

Depends on / 依赖: of_comp, of_comp_left
-/
theorem Bijective.of_comp_left {f : α -> β} {g : γ -> α} (hfg : Function.Bijective (f ∘ g))
    (hf : Function.Injective f) : Function.Bijective g :=
  ⟨hfg.1.of_comp, hfg.2.of_comp_left hf⟩

/--
theorem `exists_fixed_point_of_surjective` / 定理 `exists_fixed_point_of_surjective`

English:
theorem exists_fixed_point_of_surjective
  statement: {α β : Type*} (f : α -> α -> β)
  proof: let ⟨a, ha⟩ := hf fun a => g (f a a)
  ⟨f a a, (congr_fun ha a).symm⟩

中文:
定理 存在_fixed_point_of_surjective
  结论: {α β : 类型} (f : α -> α -> β)
  证明: let ⟨a, ha⟩ := hf fun a => g (f a a)
  ⟨f a a, (congr_fun ha a).symm⟩

Depends on / 依赖: congr_fun
-/
theorem exists_fixed_point_of_surjective {α β : Type*} (f : α -> α -> β)
    (hf : Surjective f) (g : β -> β) : exists x, g x = x :=
  let ⟨a, ha⟩ := hf fun a => g (f a a)
  ⟨f a a, (congr_fun ha a).symm⟩

/--
theorem `cantor_surjective` / 定理 `cantor_surjective`

English:
theorem cantor_surjective
  given: {α} (f : α -> Set α)
  statement: ¬Surjective f
  proof: fun hf =>
  let ⟨a, ha⟩ := hf {a | a ∉ f a}
iff_not_self .of_eq congrArg (a in ·) ha

中文:
定理 cantor_surjective
  条件: {α} (f : α -> 集合 α)
  结论: ¬满射 f
  证明: fun hf =>
  let ⟨a, ha⟩ := hf {a | a ∉ f a}
iff_not_self .of_eq congrArg (a in ·) ha
-/
theorem cantor_surjective {α} (f : α -> Set α) : ¬Surjective f := fun hf =>
  let ⟨a, ha⟩ := hf {a | a ∉ f a}
iff_not_self .of_eq congrArg (a in ·) ha

/--
theorem `cantor_injective` / 定理 `cantor_injective`

English:
theorem cantor_injective
  given: {α : Type*} (f : Set α -> α)
  statement: ¬Injective f

中文:
定理 cantor_injective
  条件: {α : 类型} (f : 集合 α -> α)
  结论: ¬单射 f
-/
theorem cantor_injective {α : Type*} (f : Set α -> α) : ¬Injective f
| i => cantor_surjective (fun a => {b | forall U, a = f U -> b in U})
         RightInverse.surjective (fun U => Set.ext fun _ => ⟨fun h => h U rfl, fun h _ e => i e ▸ h⟩)

/--
theorem `not_surjective_Type` / 定理 `not_surjective_Type`

English:
theorem not_surjective_Type
  given: {α : Type u} (f : α -> Type max u v)
  statement: ¬Surjective f
  proof: by
  intro hf
  let T : Type max u v := Sigma f
  cases hf (Set T) with | intro U hU =>
  let g : Set T -> T := fun s => ⟨U, cast hU.symm s⟩
  have hg : Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      simp only [g, cast_cast, cast_eq] at this
      assumptio

中文:
定理 not_surjective_Type
  条件: {α : 类型u} (f : α -> 类型 最大值 u v)
  结论: ¬满射 f
  证明: by
  intro hf
  let T : Type max u v := Sigma f
  cases hf (Set T) with | intro U hU =>
  let g : Set T -> T := fun s => ⟨U, cast hU.symm s⟩
  have hg : Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      simp only [g, cast_cast, cast_eq] at this
      assumptio

Depends on / 依赖: Injective, cantor_injective, cast_cast, cast_eq, hU.symm
-/
theorem not_surjective_Type {α : Type u} (f : α -> Type max u v) : ¬Surjective f := by
  intro hf
  let T : Type max u v := Sigma f
  cases hf (Set T) with | intro U hU =>
  let g : Set T -> T := fun s => ⟨U, cast hU.symm s⟩
  have hg : Injective g := by
    intro s t h
    suffices cast hU (g s).2 = cast hU (g t).2 by
      simp only [g, cast_cast, cast_eq] at this
      assumption
    · congr
  exact cantor_injective g hg

/--
Definition of `IsPartialInv` / `IsPartialInv` 的定义

English:
definition IsPartialInv
  signature: {α β} (f : α -> β) (g : β -> Option α)
  body: forall x y, g y = some x ↔ f x = y

中文:
定义 IsPartialInv
  签名: {α β} (f : α -> β) (g : β -> 选项类型 α)
  定义体: forall x y, g y = some x ↔ f x = y
-/
def IsPartialInv {α β} (f : α -> β) (g : β -> Option α) : Prop :=
  forall x y, g y = some x ↔ f x = y

/--
theorem `IsPartialInv.eq` / 定理 `IsPartialInv.eq`

English:
theorem IsPartialInv.eq
  given: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x)
  statement: g (f x) = some x
  proof: (H _ _).2 rfl

中文:
定理 IsPartialInv.eq
  条件: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x)
  结论: g (f x) = some x
  证明: (H _ _).2 rfl
-/
theorem IsPartialInv.eq {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x) : g (f x) = some x :=
  (H _ _).2 rfl

/--
theorem `IsPartialInv.get_eq` / 定理 `IsPartialInv.get_eq`

English:
theorem IsPartialInv.get_eq
  given: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x) (h : g x |>.isSome)
  proof: (H _ _).1 (Option.eq_some_of_isSome h)

中文:
定理 IsPartialInv.get_eq
  条件: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x) (h : g x |>.isSome)
  证明: (H _ _).1 (Option.eq_some_of_isSome h)

Depends on / 依赖: Option.eq_some_of_isSome, eq_some_of_isSome
-/
theorem IsPartialInv.get_eq {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x) (h : g x |>.isSome) :
    f (g x |>.get h) = x :=
  (H _ _).1 (Option.eq_some_of_isSome h)

/--
theorem `IsPartialInv.surjective_getD` / 定理 `IsPartialInv.surjective_getD`

English:
theorem IsPartialInv.surjective_getD
  given: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x)
  proof: fun y => ⟨f y, by simp [H.eq]⟩

@[deprecated (since := "2026-03-11")] alias isPartialInv_left := IsPartialInv.eq

中文:
定理 IsPartialInv.surjective_getD
  条件: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x)
  证明: fun y => ⟨f y, by simp [H.eq]⟩

@[deprecated (since := "2026-03-11")] alias isPartialInv_left := IsPartialInv.eq

Depends on / 依赖: H.eq
-/
theorem IsPartialInv.surjective_getD {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x) :
    Function.Surjective (g · |>.getD x) :=
  fun y => ⟨f y, by simp [H.eq]⟩

@[deprecated (since := "2026-03-11")] alias isPartialInv_left := IsPartialInv.eq

/--
theorem `IsPartialInv.injective` / 定理 `IsPartialInv.injective`

English:
theorem IsPartialInv.injective
  given: {α β} {f : α -> β} {g} (H : IsPartialInv f g)
  proof: fun _ _ h =>
Option.some.inj ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

@[deprecated (since := "2026-03-11")] alias injective_of_isPartialInv := IsPartialInv.injective

中文:
定理 IsPartialInv.injective
  条件: {α β} {f : α -> β} {g} (H : IsPartialInv f g)
  证明: fun _ _ h =>
Option.some.inj ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

@[deprecated (since := "2026-03-11")] alias injective_of_isPartialInv := IsPartialInv.injective
-/
theorem IsPartialInv.injective {α β} {f : α -> β} {g} (H : IsPartialInv f g) :
    Injective f := fun _ _ h =>
Option.some.inj ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

@[deprecated (since := "2026-03-11")] alias injective_of_isPartialInv := IsPartialInv.injective

/--
theorem `injective_of_isPartialInv_right` / 定理 `injective_of_isPartialInv_right`

English:
theorem injective_of_isPartialInv_right
  statement: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x y b)
  proof: ((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

中文:
定理 injective_of_isPartialInv_right
  结论: {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x y b)
  证明: ((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

Depends on / 依赖: symm.trans
-/
theorem injective_of_isPartialInv_right {α β} {f : α -> β} {g} (H : IsPartialInv f g) (x y b)
    (h₁ : b in g x) (h₂ : b in g y) : x = y :=
  ((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

/--
theorem `IsPartialInv.comp` / 定理 `IsPartialInv.comp`

English:
theorem IsPartialInv.comp
  statement: {α β γ} {f : α -> β} {g : β -> Option α} {h : β -> γ} {i : γ -> Option β}
  proof: by
  intros a b
  simp [Option.bind_eq_some_iff, hh _, hf _]

中文:
定理 IsPartialInv.comp
  结论: {α β γ} {f : α -> β} {g : β -> 选项类型 α} {h : β -> γ} {i : γ -> 选项类型 β}
  证明: by
  intros a b
  simp [Option.bind_eq_some_iff, hh _, hf _]

Depends on / 依赖: Option.bind_eq_some_iff, bind_eq_some_iff, intros
-/
theorem IsPartialInv.comp {α β γ} {f : α -> β} {g : β -> Option α} {h : β -> γ} {i : γ -> Option β}
    (hf : IsPartialInv f g) (hh : IsPartialInv h i) :
    IsPartialInv (h ∘ f) (i · |>.bind g) := by
  intros a b
  simp [Option.bind_eq_some_iff, hh _, hf _]

/--
lemma `LeftInverse.eq` / 引理 `LeftInverse.eq`

English:
lemma LeftInverse.eq
  given: {g : β -> α} {f : α -> β} (h : LeftInverse g f) (x : α)
  statement: g (f x) = x
  proof: h x

中文:
引理 左逆.eq
  条件: {g : β -> α} {f : α -> β} (h : 左逆 g f) (x : α)
  结论: g (f x) = x
  证明: h x
-/
lemma LeftInverse.eq {g : β -> α} {f : α -> β} (h : LeftInverse g f) (x : α) : g (f x) = x := h x

/--
lemma `RightInverse.eq` / 引理 `RightInverse.eq`

English:
lemma RightInverse.eq
  given: {g : β -> α} {f : α -> β} (h : RightInverse g f) (x : β)
  statement: f (g x) = x
  proof: h x

中文:
引理 右逆.eq
  条件: {g : β -> α} {f : α -> β} (h : 右逆 g f) (x : β)
  结论: f (g x) = x
  证明: h x
-/
lemma RightInverse.eq {g : β -> α} {f : α -> β} (h : RightInverse g f) (x : β) : f (g x) = x := h x

/--
theorem `LeftInverse.comp_eq_id` / 定理 `LeftInverse.comp_eq_id`

English:
theorem LeftInverse.comp_eq_id
  given: {f : α -> β} {g : β -> α} (h : LeftInverse f g)
  statement: f ∘ g = id
  proof: funext h

中文:
定理 左逆.comp_eq_id
  条件: {f : α -> β} {g : β -> α} (h : 左逆 f g)
  结论: f ∘ g = id
  证明: funext h
-/
theorem LeftInverse.comp_eq_id {f : α -> β} {g : β -> α} (h : LeftInverse f g) : f ∘ g = id :=
  funext h

/--
theorem `leftInverse_iff_comp` / 定理 `leftInverse_iff_comp`

English:
theorem leftInverse_iff_comp
  given: {f : α -> β} {g : β -> α}
  statement: LeftInverse f g ↔ f ∘ g = id
  proof: ⟨LeftInverse.comp_eq_id, congr_fun⟩

中文:
定理 leftInverse_iff_comp
  条件: {f : α -> β} {g : β -> α}
  结论: 左逆 f g ↔ f ∘ g = id
  证明: ⟨LeftInverse.comp_eq_id, congr_fun⟩

Depends on / 依赖: LeftInverse, LeftInverse.comp_eq_id, comp_eq_id, congr_fun
-/
theorem leftInverse_iff_comp {f : α -> β} {g : β -> α} : LeftInverse f g ↔ f ∘ g = id :=
  ⟨LeftInverse.comp_eq_id, congr_fun⟩

/--
theorem `RightInverse.comp_eq_id` / 定理 `RightInverse.comp_eq_id`

English:
theorem RightInverse.comp_eq_id
  given: {f : α -> β} {g : β -> α} (h : RightInverse f g)
  statement: g ∘ f = id
  proof: funext h

中文:
定理 右逆.comp_eq_id
  条件: {f : α -> β} {g : β -> α} (h : 右逆 f g)
  结论: g ∘ f = id
  证明: funext h
-/
theorem RightInverse.comp_eq_id {f : α -> β} {g : β -> α} (h : RightInverse f g) : g ∘ f = id :=
  funext h

/--
theorem `rightInverse_iff_comp` / 定理 `rightInverse_iff_comp`

English:
theorem rightInverse_iff_comp
  given: {f : α -> β} {g : β -> α}
  statement: RightInverse f g ↔ g ∘ f = id
  proof: ⟨RightInverse.comp_eq_id, congr_fun⟩

中文:
定理 rightInverse_iff_comp
  条件: {f : α -> β} {g : β -> α}
  结论: 右逆 f g ↔ g ∘ f = id
  证明: ⟨RightInverse.comp_eq_id, congr_fun⟩

Depends on / 依赖: RightInverse, RightInverse.comp_eq_id, comp_eq_id, congr_fun
-/
theorem rightInverse_iff_comp {f : α -> β} {g : β -> α} : RightInverse f g ↔ g ∘ f = id :=
  ⟨RightInverse.comp_eq_id, congr_fun⟩

/--
theorem `LeftInverse.comp` / 定理 `LeftInverse.comp`

English:
theorem LeftInverse.comp
  statement: {f : α -> β} {g : β -> α} {h : β -> γ} {i : γ -> β} (hf : LeftInverse f g)
  proof: fun a => show h (f (g (i a))) = a by rw [hf (i a), hh a]

中文:
定理 左逆.comp
  结论: {f : α -> β} {g : β -> α} {h : β -> γ} {i : γ -> β} (hf : 左逆 f g)
  证明: fun a => show h (f (g (i a))) = a by rw [hf (i a), hh a]
-/
theorem LeftInverse.comp {f : α -> β} {g : β -> α} {h : β -> γ} {i : γ -> β} (hf : LeftInverse f g)
    (hh : LeftInverse h i) : LeftInverse (h ∘ f) (g ∘ i) :=
  fun a => show h (f (g (i a))) = a by rw [hf (i a), hh a]

/--
theorem `RightInverse.comp` / 定理 `RightInverse.comp`

English:
theorem RightInverse.comp
  statement: {f : α -> β} {g : β -> α} {h : β -> γ} {i : γ -> β} (hf : RightInverse f g)
  proof: LeftInverse.comp hh hf

中文:
定理 右逆.comp
  结论: {f : α -> β} {g : β -> α} {h : β -> γ} {i : γ -> β} (hf : 右逆 f g)
  证明: LeftInverse.comp hh hf

Depends on / 依赖: LeftInverse, LeftInverse.comp
-/
theorem RightInverse.comp {f : α -> β} {g : β -> α} {h : β -> γ} {i : γ -> β} (hf : RightInverse f g)
    (hh : RightInverse h i) : RightInverse (h ∘ f) (g ∘ i) :=
  LeftInverse.comp hh hf

/--
theorem `LeftInverse.rightInverse` / 定理 `LeftInverse.rightInverse`

English:
theorem LeftInverse.rightInverse
  given: {f : α -> β} {g : β -> α} (h : LeftInverse g f)
  statement: RightInverse f g
  proof: h

中文:
定理 左逆.rightInverse
  条件: {f : α -> β} {g : β -> α} (h : 左逆 g f)
  结论: 右逆 f g
  证明: h
-/
theorem LeftInverse.rightInverse {f : α -> β} {g : β -> α} (h : LeftInverse g f) : RightInverse f g :=
  h

/--
theorem `RightInverse.leftInverse` / 定理 `RightInverse.leftInverse`

English:
theorem RightInverse.leftInverse
  given: {f : α -> β} {g : β -> α} (h : RightInverse g f)
  statement: LeftInverse f g
  proof: h

中文:
定理 右逆.leftInverse
  条件: {f : α -> β} {g : β -> α} (h : 右逆 g f)
  结论: 左逆 f g
  证明: h
-/
theorem RightInverse.leftInverse {f : α -> β} {g : β -> α} (h : RightInverse g f) : LeftInverse f g :=
  h

/--
theorem `LeftInverse.surjective` / 定理 `LeftInverse.surjective`

English:
theorem LeftInverse.surjective
  given: {f : α -> β} {g : β -> α} (h : LeftInverse f g)
  statement: Surjective f
  proof: h.rightInverse.surjective

中文:
定理 左逆.surjective
  条件: {f : α -> β} {g : β -> α} (h : 左逆 f g)
  结论: 满射 f
  证明: h.rightInverse.surjective

Depends on / 依赖: h.rightInverse.surjective, rightInverse, surjective
-/
theorem LeftInverse.surjective {f : α -> β} {g : β -> α} (h : LeftInverse f g) : Surjective f :=
  h.rightInverse.surjective

/--
theorem `RightInverse.injective` / 定理 `RightInverse.injective`

English:
theorem RightInverse.injective
  given: {f : α -> β} {g : β -> α} (h : RightInverse f g)
  statement: Injective f
  proof: h.leftInverse.injective

中文:
定理 右逆.injective
  条件: {f : α -> β} {g : β -> α} (h : 右逆 f g)
  结论: 单射 f
  证明: h.leftInverse.injective

Depends on / 依赖: h.leftInverse.injective, injective, leftInverse
-/
theorem RightInverse.injective {f : α -> β} {g : β -> α} (h : RightInverse f g) : Injective f :=
  h.leftInverse.injective

/--
theorem `LeftInverse.rightInverse_of_injective` / 定理 `LeftInverse.rightInverse_of_injective`

English:
theorem LeftInverse.rightInverse_of_injective
  statement: {f : α -> β} {g : β -> α} (h : LeftInverse f g)
  proof: fun x => hf h (f x)

中文:
定理 左逆.rightInverse_of_injective
  结论: {f : α -> β} {g : β -> α} (h : 左逆 f g)
  证明: fun x => hf h (f x)
-/
theorem LeftInverse.rightInverse_of_injective {f : α -> β} {g : β -> α} (h : LeftInverse f g)
    (hf : Injective f) : RightInverse f g :=
fun x => hf h (f x)

/--
theorem `LeftInverse.rightInverse_of_surjective` / 定理 `LeftInverse.rightInverse_of_surjective`

English:
theorem LeftInverse.rightInverse_of_surjective
  statement: {f : α -> β} {g : β -> α} (h : LeftInverse f g)
  proof: fun x => let ⟨y, hy⟩ := hg x; hy ▸ congr_arg g (h y)

中文:
定理 左逆.rightInverse_of_surjective
  结论: {f : α -> β} {g : β -> α} (h : 左逆 f g)
  证明: fun x => let ⟨y, hy⟩ := hg x; hy ▸ congr_arg g (h y)

Depends on / 依赖: congr_arg
-/
theorem LeftInverse.rightInverse_of_surjective {f : α -> β} {g : β -> α} (h : LeftInverse f g)
    (hg : Surjective g) : RightInverse f g :=
  fun x => let ⟨y, hy⟩ := hg x; hy ▸ congr_arg g (h y)

/--
theorem `RightInverse.leftInverse_of_surjective` / 定理 `RightInverse.leftInverse_of_surjective`

English:
theorem RightInverse.leftInverse_of_surjective
  given: {f : α -> β} {g : β -> α}
  proof: LeftInverse.rightInverse_of_surjective

中文:
定理 右逆.leftInverse_of_surjective
  条件: {f : α -> β} {g : β -> α}
  证明: LeftInverse.rightInverse_of_surjective

Depends on / 依赖: LeftInverse, LeftInverse.rightInverse_of_surjective, rightInverse_of_surjective
-/
theorem RightInverse.leftInverse_of_surjective {f : α -> β} {g : β -> α} :
    RightInverse f g -> Surjective f -> LeftInverse f g :=
  LeftInverse.rightInverse_of_surjective

/--
theorem `RightInverse.leftInverse_of_injective` / 定理 `RightInverse.leftInverse_of_injective`

English:
theorem RightInverse.leftInverse_of_injective
  given: {f : α -> β} {g : β -> α}
  proof: LeftInverse.rightInverse_of_injective

中文:
定理 右逆.leftInverse_of_injective
  条件: {f : α -> β} {g : β -> α}
  证明: LeftInverse.rightInverse_of_injective

Depends on / 依赖: DecidablePred, LeftInverse, LeftInverse.rightInverse_of_injective, primeFactorsList, rightInverse_of_injective
-/
theorem RightInverse.leftInverse_of_injective {f : α -> β} {g : β -> α} :
    RightInverse f g -> Injective g -> LeftInverse f g :=
  LeftInverse.rightInverse_of_injective

/--
theorem `LeftInverse.eq_rightInverse` / 定理 `LeftInverse.eq_rightInverse`

English:
theorem LeftInverse.eq_rightInverse
  statement: {f : α -> β} {g₁ g₂ : β -> α} (h₁ : LeftInverse g₁ f)
  proof: calc
    g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp_id]
     _ = g₂ := by rw [← comp_assoc, h₁.comp_eq_id, id_comp]

中文:
定理 左逆.eq_rightInverse
  结论: {f : α -> β} {g₁ g₂ : β -> α} (h₁ : 左逆 g₁ f)
  证明: calc
    g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp_id]
     _ = g₂ := by rw [← comp_assoc, h₁.comp_eq_id, id_comp]

Depends on / 依赖: comp_assoc, comp_eq_id, comp_id, id_comp
-/
theorem LeftInverse.eq_rightInverse {f : α -> β} {g₁ g₂ : β -> α} (h₁ : LeftInverse g₁ f)
    (h₂ : RightInverse g₂ f) : g₁ = g₂ :=
  calc
    g₁ = g₁ ∘ f ∘ g₂ := by rw [h₂.comp_eq_id, comp_id]
     _ = g₂ := by rw [← comp_assoc, h₁.comp_eq_id, id_comp]

/--
Definition of `partialInv` / `partialInv` 的定义

English:
definition partialInv
  signature: {α β} (f : α -> β) (b : β)
  body: open scoped Classical in
  if h : exists a, f a = b then some (Classical.choose h) else none

中文:
定义 partialInv
  签名: {α β} (f : α -> β) (b : β)
  定义体: open scoped Classical in
  if h : exists a, f a = b then some (Classical.choose h) else none

Depends on / 依赖: Classical, Classical.choose, scoped
-/
noncomputable def partialInv {α β} (f : α -> β) (b : β) : Option α :=
  open scoped Classical in
  if h : exists a, f a = b then some (Classical.choose h) else none

/--
theorem `Injective.isPartialInv` / 定理 `Injective.isPartialInv`

English:
theorem Injective.isPartialInv
  given: {α β} {f : α -> β} (I : Injective f)
  statement: IsPartialInv f (partialInv f)
  proof: rfl
    if h' : exists a, f a = b
    then by rw [hpi, dif_pos h'] at h
            injection h with h
            subst h
            apply Classical.choose_spec h'
    else by rw [hpi, dif_neg h'] at h; contradiction,
  fun e => e ▸ have h : exists a', f a' = f a := ⟨_, rfl⟩
              (dif_pos

中文:
定理 单射.isPartialInv
  条件: {α β} {f : α -> β} (I : 单射 f)
  结论: IsPartialInv f (partialInv f)
  证明: rfl
    if h' : exists a, f a = b
    then by rw [hpi, dif_pos h'] at h
            injection h with h
            subst h
            apply Classical.choose_spec h'
    else by rw [hpi, dif_neg h'] at h; contradiction,
  fun e => e ▸ have h : exists a', f a' = f a := ⟨_, rfl⟩
              (dif_pos

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, congr_arg, dif_neg, dif_pos, injection
-/
theorem Injective.isPartialInv {α β} {f : α -> β} (I : Injective f) : IsPartialInv f (partialInv f)
  | a, b =>
  ⟨fun h =>
    open scoped Classical in
    have hpi : partialInv f b = if h : exists a, f a = b then some (Classical.choose h) else none :=
      rfl
    if h' : exists a, f a = b
    then by rw [hpi, dif_pos h'] at h
            injection h with h
            subst h
            apply Classical.choose_spec h'
    else by rw [hpi, dif_neg h'] at h; contradiction,
  fun e => e ▸ have h : exists a', f a' = f a := ⟨_, rfl⟩
              (dif_pos h).trans (congr_arg _ (I <| Classical.choose_spec h))⟩

@[deprecated (since := "2026-03-11")] alias partialInv_of_injective := Injective.isPartialInv

/--
theorem `partialInv_left` / 定理 `partialInv_left`

English:
theorem partialInv_left
  given: {α β} {f : α -> β} (I : Injective f)
  statement: forall x, partialInv f (f x) = some x
  proof: I.isPartialInv.eq

中文:
定理 partialInv_left
  条件: {α β} {f : α -> β} (I : 单射 f)
  结论: 对任意 x, partialInv f (f x) = some x
  证明: I.isPartialInv.eq

Depends on / 依赖: I.isPartialInv.eq, isPartialInv
-/
theorem partialInv_left {α β} {f : α -> β} (I : Injective f) : forall x, partialInv f (f x) = some x :=
  I.isPartialInv.eq

end

section InvFun

variable {α β : Sort*} [Nonempty α] {f : α -> β} {b : β}

-- Explicit Sort so that `α` isn't inferred to be Prop via `exists_prop_decidable`
/--
Definition of `invFun` / `invFun` 的定义

English:
definition invFun
  signature: {α : Sort u} {β} [Nonempty α] (f : α -> β)
  body: open scoped Classical in
  fun y => if h : (exists x, f x = y) then h.choose else Classical.arbitrary α

中文:
定义 invFun
  签名: {α : 类型层 u} {β} [非空 α] (f : α -> β)
  定义体: open scoped Classical in
  fun y => if h : (exists x, f x = y) then h.choose else Classical.arbitrary α

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, h.choose, scoped
-/
noncomputable def invFun {α : Sort u} {β} [Nonempty α] (f : α -> β) : β -> α :=
  open scoped Classical in
  fun y => if h : (exists x, f x = y) then h.choose else Classical.arbitrary α

/--
theorem `invFun_eq` / 定理 `invFun_eq`

English:
theorem invFun_eq
  given: (h : exists a, f a = b)
  statement: f (invFun f b) = b
  proof: by
  simp only [invFun, dif_pos h, h.choose_spec]

中文:
定理 invFun_eq
  条件: (h : 存在 a, f a = b)
  结论: f (invFun f b) = b
  证明: by
  simp only [invFun, dif_pos h, h.choose_spec]

Depends on / 依赖: choose_spec, dif_pos, h.choose_spec, invFun
-/
theorem invFun_eq (h : exists a, f a = b) : f (invFun f b) = b := by
  simp only [invFun, dif_pos h, h.choose_spec]

/--
theorem `apply_invFun_apply` / 定理 `apply_invFun_apply`

English:
theorem apply_invFun_apply
  given: {α β : Type*} {f : α -> β} {a : α}
  proof: @invFun_eq _ _ ⟨a⟩ _ _ ⟨_, rfl⟩

中文:
定理 apply_invFun_apply
  条件: {α β : 类型} {f : α -> β} {a : α}
  证明: @invFun_eq _ _ ⟨a⟩ _ _ ⟨_, rfl⟩

Depends on / 依赖: invFun_eq
-/
theorem apply_invFun_apply {α β : Type*} {f : α -> β} {a : α} :
    f (@invFun _ _ ⟨a⟩ f (f a)) = f a :=
  @invFun_eq _ _ ⟨a⟩ _ _ ⟨_, rfl⟩

/--
theorem `invFun_neg` / 定理 `invFun_neg`

English:
theorem invFun_neg
  given: (h : ¬exists a, f a = b)
  statement: invFun f b = Classical.choice ‹_›
  proof: dif_neg h

中文:
定理 invFun_neg
  条件: (h : ¬存在 a, f a = b)
  结论: invFun f b = 经典.choice ‹_›
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem invFun_neg (h : ¬exists a, f a = b) : invFun f b = Classical.choice ‹_› :=
  dif_neg h

/--
theorem `invFun_eq_of_injective_of_rightInverse` / 定理 `invFun_eq_of_injective_of_rightInverse`

English:
theorem invFun_eq_of_injective_of_rightInverse
  statement: {g : β -> α} (hf : Injective f)
  proof: funext fun b =>
    hf
      (by
        rw [hg b]
        exact invFun_eq ⟨g b, hg b⟩)

中文:
定理 invFun_eq_of_injective_of_rightInverse
  结论: {g : β -> α} (hf : 单射 f)
  证明: funext fun b =>
    hf
      (by
        rw [hg b]
        exact invFun_eq ⟨g b, hg b⟩)

Depends on / 依赖: invFun_eq
-/
theorem invFun_eq_of_injective_of_rightInverse {g : β -> α} (hf : Injective f)
    (hg : RightInverse g f) : invFun f = g :=
  funext fun b =>
    hf
      (by
        rw [hg b]
        exact invFun_eq ⟨g b, hg b⟩)

/--
theorem `rightInverse_invFun` / 定理 `rightInverse_invFun`

English:
theorem rightInverse_invFun
  given: (hf : Surjective f)
  statement: RightInverse (invFun f) f
  proof: fun b => invFun_eq hf b

中文:
定理 rightInverse_invFun
  条件: (hf : 满射 f)
  结论: 右逆 (invFun f) f
  证明: fun b => invFun_eq hf b

Depends on / 依赖: invFun_eq
-/
theorem rightInverse_invFun (hf : Surjective f) : RightInverse (invFun f) f :=
fun b => invFun_eq hf b

/--
theorem `leftInverse_invFun` / 定理 `leftInverse_invFun`

English:
theorem leftInverse_invFun
  given: (hf : Injective f)
  statement: LeftInverse (invFun f) f
  proof: fun b => hf invFun_eq ⟨b, rfl⟩

中文:
定理 leftInverse_invFun
  条件: (hf : 单射 f)
  结论: 左逆 (invFun f) f
  证明: fun b => hf invFun_eq ⟨b, rfl⟩

Depends on / 依赖: invFun_eq
-/
theorem leftInverse_invFun (hf : Injective f) : LeftInverse (invFun f) f :=
fun b => hf invFun_eq ⟨b, rfl⟩

/--
theorem `invFun_surjective` / 定理 `invFun_surjective`

English:
theorem invFun_surjective
  given: (hf : Injective f)
  statement: Surjective (invFun f)
  proof: (leftInverse_invFun hf).surjective

中文:
定理 invFun_surjective
  条件: (hf : 单射 f)
  结论: 满射 (invFun f)
  证明: (leftInverse_invFun hf).surjective

Depends on / 依赖: leftInverse_invFun, surjective
-/
theorem invFun_surjective (hf : Injective f) : Surjective (invFun f) :=
  (leftInverse_invFun hf).surjective

/--
theorem `invFun_comp` / 定理 `invFun_comp`

English:
theorem invFun_comp
  given: (hf : Injective f)
  statement: invFun f ∘ f = id
  proof: funext leftInverse_invFun hf

中文:
定理 invFun_comp
  条件: (hf : 单射 f)
  结论: invFun f ∘ f = id
  证明: funext leftInverse_invFun hf

Depends on / 依赖: leftInverse_invFun
-/
theorem invFun_comp (hf : Injective f) : invFun f ∘ f = id :=
funext leftInverse_invFun hf

/--
theorem `Injective.hasLeftInverse` / 定理 `Injective.hasLeftInverse`

English:
theorem Injective.hasLeftInverse
  given: (hf : Injective f)
  statement: HasLeftInverse f
  proof: ⟨invFun f, leftInverse_invFun hf⟩

中文:
定理 单射.hasLeftInverse
  条件: (hf : 单射 f)
  结论: HasLeftInverse f
  证明: ⟨invFun f, leftInverse_invFun hf⟩

Depends on / 依赖: invFun, leftInverse_invFun
-/
theorem Injective.hasLeftInverse (hf : Injective f) : HasLeftInverse f :=
  ⟨invFun f, leftInverse_invFun hf⟩

/--
theorem `injective_iff_hasLeftInverse` / 定理 `injective_iff_hasLeftInverse`

English:
theorem injective_iff_hasLeftInverse
  statement: Injective f ↔ HasLeftInverse f
  proof: ⟨Injective.hasLeftInverse, HasLeftInverse.injective⟩

中文:
定理 injective_iff_hasLeftInverse
  结论: 单射 f ↔ HasLeftInverse f
  证明: ⟨Injective.hasLeftInverse, HasLeftInverse.injective⟩

Depends on / 依赖: HasLeftInverse, HasLeftInverse.injective, Injective, Injective.hasLeftInverse, hasLeftInverse, injective
-/
theorem injective_iff_hasLeftInverse : Injective f ↔ HasLeftInverse f :=
  ⟨Injective.hasLeftInverse, HasLeftInverse.injective⟩

end InvFun

section SurjInv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {f : α -> β}

/--
Definition of `surjInv` / `surjInv` 的定义

English:
definition surjInv
  signature: {f : α -> β} (h : Surjective f) (b : β)
  body: Classical.choose (h b)

中文:
定义 surjInv
  签名: {f : α -> β} (h : 满射 f) (b : β)
  定义体: Classical.choose (h b)

Depends on / 依赖: Classical, Classical.choose
-/
noncomputable def surjInv {f : α -> β} (h : Surjective f) (b : β) : α :=
  Classical.choose (h b)

/--
theorem `surjInv_eq` / 定理 `surjInv_eq`

English:
theorem surjInv_eq
  given: (h : Surjective f) (b)
  statement: f (surjInv h b) = b
  proof: Classical.choose_spec (h b)

@[simp]

中文:
定理 surjInv_eq
  条件: (h : 满射 f) (b)
  结论: f (surjInv h b) = b
  证明: Classical.choose_spec (h b)

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
theorem surjInv_eq (h : Surjective f) (b) : f (surjInv h b) = b :=
  Classical.choose_spec (h b)

@[simp]
/--
lemma `comp_surjInv` / 引理 `comp_surjInv`

English:
lemma comp_surjInv
  given: (hf : f.Surjective)
  statement: f ∘ f.surjInv hf = id
  proof: funext (Function.surjInv_eq _)

中文:
引理 comp_surjInv
  条件: (hf : f.满射)
  结论: f ∘ f.surjInv hf = id
  证明: funext (Function.surjInv_eq _)

Depends on / 依赖: Function, Function.surjInv_eq, surjInv_eq
-/
lemma comp_surjInv (hf : f.Surjective) : f ∘ f.surjInv hf = id :=
  funext (Function.surjInv_eq _)

/--
theorem `rightInverse_surjInv` / 定理 `rightInverse_surjInv`

English:
theorem rightInverse_surjInv
  given: (hf : Surjective f)
  statement: RightInverse (surjInv hf) f
  proof: surjInv_eq hf

中文:
定理 rightInverse_surjInv
  条件: (hf : 满射 f)
  结论: 右逆 (surjInv hf) f
  证明: surjInv_eq hf

Depends on / 依赖: surjInv_eq
-/
theorem rightInverse_surjInv (hf : Surjective f) : RightInverse (surjInv hf) f :=
  surjInv_eq hf

/--
theorem `leftInverse_surjInv` / 定理 `leftInverse_surjInv`

English:
theorem leftInverse_surjInv
  given: (hf : Bijective f)
  statement: LeftInverse (surjInv hf.2) f
  proof: rightInverse_of_injective_of_leftInverse hf.1 (rightInverse_surjInv hf.2)

中文:
定理 leftInverse_surjInv
  条件: (hf : 双射 f)
  结论: 左逆 (surjInv hf.2) f
  证明: rightInverse_of_injective_of_leftInverse hf.1 (rightInverse_surjInv hf.2)

Depends on / 依赖: rightInverse_of_injective_of_leftInverse, rightInverse_surjInv
-/
theorem leftInverse_surjInv (hf : Bijective f) : LeftInverse (surjInv hf.2) f :=
  rightInverse_of_injective_of_leftInverse hf.1 (rightInverse_surjInv hf.2)

/--
theorem `Surjective.hasRightInverse` / 定理 `Surjective.hasRightInverse`

English:
theorem Surjective.hasRightInverse
  given: (hf : Surjective f)
  statement: HasRightInverse f
  proof: ⟨_, rightInverse_surjInv hf⟩

中文:
定理 满射.hasRightInverse
  条件: (hf : 满射 f)
  结论: HasRightInverse f
  证明: ⟨_, rightInverse_surjInv hf⟩

Depends on / 依赖: rightInverse_surjInv
-/
theorem Surjective.hasRightInverse (hf : Surjective f) : HasRightInverse f :=
  ⟨_, rightInverse_surjInv hf⟩

/--
theorem `surjective_iff_hasRightInverse` / 定理 `surjective_iff_hasRightInverse`

English:
theorem surjective_iff_hasRightInverse
  statement: Surjective f ↔ HasRightInverse f
  proof: ⟨Surjective.hasRightInverse, HasRightInverse.surjective⟩

中文:
定理 surjective_iff_hasRightInverse
  结论: 满射 f ↔ HasRightInverse f
  证明: ⟨Surjective.hasRightInverse, HasRightInverse.surjective⟩

Depends on / 依赖: HasRightInverse, HasRightInverse.surjective, Surjective, Surjective.hasRightInverse, hasRightInverse, surjective
-/
theorem surjective_iff_hasRightInverse : Surjective f ↔ HasRightInverse f :=
  ⟨Surjective.hasRightInverse, HasRightInverse.surjective⟩

/--
theorem `bijective_iff_has_inverse` / 定理 `bijective_iff_has_inverse`

English:
theorem bijective_iff_has_inverse
  statement: Bijective f ↔ exists g, LeftInverse g f ∧ RightInverse g f
  proof: ⟨fun hf => ⟨_, leftInverse_surjInv hf, rightInverse_surjInv hf.2⟩, fun ⟨_, gl, gr⟩ =>
    ⟨gl.injective, gr.surjective⟩⟩

中文:
定理 bijective_iff_has_inverse
  结论: 双射 f ↔ 存在 g, 左逆 g f ∧ 右逆 g f
  证明: ⟨fun hf => ⟨_, leftInverse_surjInv hf, rightInverse_surjInv hf.2⟩, fun ⟨_, gl, gr⟩ =>
    ⟨gl.injective, gr.surjective⟩⟩

Depends on / 依赖: DecidablePred, gl.injective, gr.surjective, injective, leftInverse_surjInv, primeFactorsList, rightInverse_surjInv, surjective
-/
theorem bijective_iff_has_inverse : Bijective f ↔ exists g, LeftInverse g f ∧ RightInverse g f :=
  ⟨fun hf => ⟨_, leftInverse_surjInv hf, rightInverse_surjInv hf.2⟩, fun ⟨_, gl, gr⟩ =>
    ⟨gl.injective, gr.surjective⟩⟩

/--
theorem `injective_surjInv` / 定理 `injective_surjInv`

English:
theorem injective_surjInv
  given: (h : Surjective f)
  statement: Injective (surjInv h)
  proof: (rightInverse_surjInv h).injective

中文:
定理 injective_surjInv
  条件: (h : 满射 f)
  结论: 单射 (surjInv h)
  证明: (rightInverse_surjInv h).injective

Depends on / 依赖: injective, rightInverse_surjInv
-/
theorem injective_surjInv (h : Surjective f) : Injective (surjInv h) :=
  (rightInverse_surjInv h).injective

/--
theorem `surjective_to_subsingleton` / 定理 `surjective_to_subsingleton`

English:
theorem surjective_to_subsingleton
  given: [na : Nonempty α] [Subsingleton β] (f : α -> β)
  proof: fun _ => let ⟨a⟩ := na; ⟨a, Subsingleton.elim _ _⟩

中文:
定理 surjective_to_subsingleton
  条件: [na : 非空 α] [子单例 β] (f : α -> β)
  证明: fun _ => let ⟨a⟩ := na; ⟨a, Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem surjective_to_subsingleton [na : Nonempty α] [Subsingleton β] (f : α -> β) :
    Surjective f :=
  fun _ => let ⟨a⟩ := na; ⟨a, Subsingleton.elim _ _⟩

/--
theorem `Surjective.piMap` / 定理 `Surjective.piMap`

English:
theorem Surjective.piMap
  statement: {ι : Sort*} {α β : ι -> Sort*} {f : forall i, α i -> β i}
  proof: fun g =>
  ⟨fun i => surjInv (hf i) (g i), funext fun _ => rightInverse_surjInv _ _⟩

中文:
定理 满射.piMap
  结论: {ι : 类型层*} {α β : ι -> 类型层*} {f : 对任意 i, α i -> β i}
  证明: fun g =>
  ⟨fun i => surjInv (hf i) (g i), funext fun _ => rightInverse_surjInv _ _⟩
-/
theorem Surjective.piMap {ι : Sort*} {α β : ι -> Sort*} {f : forall i, α i -> β i}
    (hf : forall i, Surjective (f i)) : Surjective (Pi.map f) := fun g =>
  ⟨fun i => surjInv (hf i) (g i), funext fun _ => rightInverse_surjInv _ _⟩

/--
theorem `Surjective.comp_left` / 定理 `Surjective.comp_left`

English:
theorem Surjective.comp_left
  given: {g : β -> γ} (hg : Surjective g)
  proof: .piMap fun _ => hg

中文:
定理 满射.comp_left
  条件: {g : β -> γ} (hg : 满射 g)
  证明: .piMap fun _ => hg
-/
theorem Surjective.comp_left {g : β -> γ} (hg : Surjective g) :
    Surjective (g ∘ · : (α -> β) -> α -> γ) :=
  .piMap fun _ => hg

/--
theorem `surjective_comp_left_iff` / 定理 `surjective_comp_left_iff`

English:
theorem surjective_comp_left_iff
  given: [Nonempty α] {g : β -> γ}
  proof: by
  refine ⟨fun h c => Nonempty.elim ‹_› fun a => ?_, (·.comp_left)⟩
  have ⟨f, hf⟩ := h fun _ => c
  exact ⟨f a, congr_fun hf _⟩

中文:
定理 surjective_comp_left_iff
  条件: [非空 α] {g : β -> γ}
  证明: by
  refine ⟨fun h c => Nonempty.elim ‹_› fun a => ?_, (·.comp_left)⟩
  have ⟨f, hf⟩ := h fun _ => c
  exact ⟨f a, congr_fun hf _⟩

Depends on / 依赖: Nonempty, Nonempty.elim, comp_left, congr_fun
-/
theorem surjective_comp_left_iff [Nonempty α] {g : β -> γ} :
    Surjective (g ∘ · : (α -> β) -> α -> γ) ↔ Surjective g := by
  refine ⟨fun h c => Nonempty.elim ‹_› fun a => ?_, (·.comp_left)⟩
  have ⟨f, hf⟩ := h fun _ => c
  exact ⟨f a, congr_fun hf _⟩

/--
theorem `Bijective.piMap` / 定理 `Bijective.piMap`

English:
theorem Bijective.piMap
  statement: {ι : Sort*} {α β : ι -> Sort*} {f : forall i, α i -> β i}
  proof: ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2⟩

中文:
定理 双射.piMap
  结论: {ι : 类型层*} {α β : ι -> 类型层*} {f : 对任意 i, α i -> β i}
  证明: ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2⟩
-/
theorem Bijective.piMap {ι : Sort*} {α β : ι -> Sort*} {f : forall i, α i -> β i}
    (hf : forall i, Bijective (f i)) : Bijective (Pi.map f) :=
  ⟨.piMap fun i => (hf i).1, .piMap fun i => (hf i).2⟩

/--
theorem `Bijective.comp_left` / 定理 `Bijective.comp_left`

English:
theorem Bijective.comp_left
  given: {g : β -> γ} (hg : Bijective g)
  proof: ⟨hg.injective.comp_left, hg.surjective.comp_left⟩

中文:
定理 双射.comp_left
  条件: {g : β -> γ} (hg : 双射 g)
  证明: ⟨hg.injective.comp_left, hg.surjective.comp_left⟩

Depends on / 依赖: comp_left, hg.injective.comp_left, hg.surjective.comp_left, injective, surjective
-/
theorem Bijective.comp_left {g : β -> γ} (hg : Bijective g) :
    Bijective (g ∘ · : (α -> β) -> α -> γ) :=
  ⟨hg.injective.comp_left, hg.surjective.comp_left⟩

end SurjInv

section Update

variable {α : Sort u} {β : α -> Sort v} {α' : Sort w} [DecidableEq α]
  {f : (a : α) -> β a} {a : α} {b : β a}


/-- Replacing the value of a function at a given point by a given value. -/
@[grind]
/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: (f : forall a, β a) (a' : α) (v : β a') (a : α)
  body: if h : a = a' then Eq.ndrec v h.symm else f a

@[simp]

中文:
定义 update
  签名: (f : 对任意 a, β a) (a' : α) (v : β a') (a : α)
  定义体: if h : a = a' then Eq.ndrec v h.symm else f a

@[simp]

Depends on / 依赖: Eq.ndrec, h.symm
-/
def update (f : forall a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

@[simp]
/--
theorem `update_self` / 定理 `update_self`

English:
theorem update_self
  given: (a : α) (v : β a) (f : forall a, β a)
  statement: update f a v a = v
  proof: dif_pos rfl

@[simp]

中文:
定理 update_self
  条件: (a : α) (v : β a) (f : 对任意 a, β a)
  结论: update f a v a = v
  证明: dif_pos rfl

@[simp]

Depends on / 依赖: dif_pos
-/
theorem update_self (a : α) (v : β a) (f : forall a, β a) : update f a v a = v :=
  dif_pos rfl

@[simp]
/--
theorem `update_of_ne` / 定理 `update_of_ne`

English:
theorem update_of_ne
  given: {a a' : α} (h : a != a') (v : β a') (f : forall a, β a)
  statement: update f a' v a = f a
  proof: dif_neg h

中文:
定理 update_of_ne
  条件: {a a' : α} (h : a != a') (v : β a') (f : 对任意 a, β a)
  结论: update f a' v a = f a
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem update_of_ne {a a' : α} (h : a != a') (v : β a') (f : forall a, β a) : update f a' v a = f a :=
  dif_neg h

/--
A congruence lemma for `Function.update`, specialized for the non-dependent case. Without this,
`simp` can't rewrite in the fourth argument `a` because the result type depends on `a`.
See also https://github.com/leanprover/lean4/issues/12478.
-/
@[congr]
/--
lemma `update_congr` / 引理 `update_congr`

English:
lemma update_congr
  statement: {β : Sort*}
  proof: by
  subst hf; subst ha'; subst hv; subst ha; rfl

中文:
引理 update_congr
  结论: {β : 类型层*}
  证明: by
  subst hf; subst ha'; subst hv; subst ha; rfl
-/
lemma update_congr {β : Sort*}
    {f₁ f₂ : α -> β} (hf : f₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂)
    {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (ha : a₁ = a₂) :
    Function.update f₁ a'₁ v₁ a₁ = Function.update f₂ a'₂ v₂ a₂ := by
  subst hf; subst ha'; subst hv; subst ha; rfl

/--
theorem `update_apply` / 定理 `update_apply`

English:
theorem update_apply
  given: {β : Sort*} (f : α -> β) (a' : α) (b : β) (a : α)
  proof: by
  rcases Decidable.eq_or_ne a a' with rfl | hne <;> simp [*]

@[nontriviality]

中文:
定理 update_apply
  条件: {β : 类型层*} (f : α -> β) (a' : α) (b : β) (a : α)
  证明: by
  rcases Decidable.eq_or_ne a a' with rfl | hne <;> simp [*]

@[nontriviality]

Depends on / 依赖: Decidable, Decidable.eq_or_ne, eq_or_ne
-/
theorem update_apply {β : Sort*} (f : α -> β) (a' : α) (b : β) (a : α) :
    update f a' b a = if a = a' then b else f a := by
  rcases Decidable.eq_or_ne a a' with rfl | hne <;> simp [*]

@[nontriviality]
/--
theorem `update_eq_const_of_subsingleton` / 定理 `update_eq_const_of_subsingleton`

English:
theorem update_eq_const_of_subsingleton
  given: [Subsingleton α] (a : α) (v : α') (f : α -> α')
  proof: funext fun a' => Subsingleton.elim a a' ▸ update_self ..

中文:
定理 update_eq_const_of_subsingleton
  条件: [子单例 α] (a : α) (v : α') (f : α -> α')
  证明: funext fun a' => Subsingleton.elim a a' ▸ update_self ..

Depends on / 依赖: Subsingleton, Subsingleton.elim, update_self
-/
theorem update_eq_const_of_subsingleton [Subsingleton α] (a : α) (v : α') (f : α -> α') :
    update f a v = const α v :=
  funext fun a' => Subsingleton.elim a a' ▸ update_self ..

/--
theorem `surjective_eval` / 定理 `surjective_eval`

English:
theorem surjective_eval
  given: {α : Sort u} {β : α -> Sort v} [h : forall a, Nonempty (β a)] (a : α)
  proof: fun b =>
  ⟨@update _ _ (Classical.decEq α) (fun a => (h a).some) a b,
   @update_self _ _ (Classical.decEq α) _ _ _⟩

中文:
定理 surjective_eval
  条件: {α : 类型层 u} {β : α -> 类型层 v} [h : 对任意 a, 非空 (β a)] (a : α)
  证明: fun b =>
  ⟨@update _ _ (Classical.decEq α) (fun a => (h a).some) a b,
   @update_self _ _ (Classical.decEq α) _ _ _⟩
-/
theorem surjective_eval {α : Sort u} {β : α -> Sort v} [h : forall a, Nonempty (β a)] (a : α) :
    Surjective (eval a : (forall a, β a) -> β a) := fun b =>
  ⟨@update _ _ (Classical.decEq α) (fun a => (h a).some) a b,
   @update_self _ _ (Classical.decEq α) _ _ _⟩

/--
theorem `update_injective` / 定理 `update_injective`

English:
theorem update_injective
  given: (f : forall a, β a) (a' : α)
  statement: Injective (update f a')
  proof: fun v v' h => by
  have := congr_fun h a'
  rwa [update_self, update_self] at this

中文:
定理 update_injective
  条件: (f : 对任意 a, β a) (a' : α)
  结论: 单射 (update f a')
  证明: fun v v' h => by
  have := congr_fun h a'
  rwa [update_self, update_self] at this

Depends on / 依赖: congr_fun, update_self
-/
theorem update_injective (f : forall a, β a) (a' : α) : Injective (update f a') := fun v v' h => by
  have := congr_fun h a'
  rwa [update_self, update_self] at this

/--
lemma `forall_update_iff` / 引理 `forall_update_iff`

English:
lemma forall_update_iff
  given: (f : forall a, β a) {a : α} {b : β a} (p : forall a, β a -> Prop)
  proof: by
  rw [← and_forall_ne a]; rw [update_self]
  simp +contextual

中文:
引理 对任意_update_iff
  条件: (f : 对任意 a, β a) {a : α} {b : β a} (p : 对任意 a, β a -> 命题)
  证明: by
  rw [← and_forall_ne a]; rw [update_self]
  simp +contextual

Depends on / 依赖: and_forall_ne, contextual, update_self
-/
lemma forall_update_iff (f : forall a, β a) {a : α} {b : β a} (p : forall a, β a -> Prop) :
    (forall x, p x (update f a b x)) ↔ p a b ∧ forall x, x != a -> p x (f x) := by
  rw [← and_forall_ne a]; rw [update_self]
  simp +contextual

/--
theorem `exists_update_iff` / 定理 `exists_update_iff`

English:
theorem exists_update_iff
  given: (f : forall a, β a) {a : α} {b : β a} (p : forall a, β a -> Prop)
  proof: by
  rw [← not_forall_not]; rw [forall_update_iff f fun a b => ¬p a b]
  simp [-not_and, not_and_or]

中文:
定理 存在_update_iff
  条件: (f : 对任意 a, β a) {a : α} {b : β a} (p : 对任意 a, β a -> 命题)
  证明: by
  rw [← not_forall_not]; rw [forall_update_iff f fun a b => ¬p a b]
  simp [-not_and, not_and_or]

Depends on / 依赖: forall_update_iff, not_and, not_and_or, not_forall_not
-/
theorem exists_update_iff (f : forall a, β a) {a : α} {b : β a} (p : forall a, β a -> Prop) :
    (exists x, p x (update f a b x)) ↔ p a b ∨ exists x != a, p x (f x) := by
  rw [← not_forall_not]; rw [forall_update_iff f fun a b => ¬p a b]
  simp [-not_and, not_and_or]

/--
theorem `update_eq_iff` / 定理 `update_eq_iff`

English:
theorem update_eq_iff
  given: {a : α} {b : β a} {f g : forall a, β a}
  proof: funext_iff.trans forall_update_iff _ fun x y => y = g x

中文:
定理 update_eq_iff
  条件: {a : α} {b : β a} {f g : 对任意 a, β a}
  证明: funext_iff.trans forall_update_iff _ fun x y => y = g x

Depends on / 依赖: forall_update_iff, funext_iff, funext_iff.trans
-/
theorem update_eq_iff {a : α} {b : β a} {f g : forall a, β a} :
    update f a b = g ↔ b = g a ∧ forall x != a, f x = g x :=
funext_iff.trans forall_update_iff _ fun x y => y = g x

/--
theorem `eq_update_iff` / 定理 `eq_update_iff`

English:
theorem eq_update_iff
  given: {a : α} {b : β a} {f g : forall a, β a}
  proof: funext_iff.trans forall_update_iff _ fun x y => g x = y

中文:
定理 eq_update_iff
  条件: {a : α} {b : β a} {f g : 对任意 a, β a}
  证明: funext_iff.trans forall_update_iff _ fun x y => g x = y

Depends on / 依赖: forall_update_iff, funext_iff, funext_iff.trans
-/
theorem eq_update_iff {a : α} {b : β a} {f g : forall a, β a} :
    g = update f a b ↔ g a = b ∧ forall x != a, g x = f x :=
funext_iff.trans forall_update_iff _ fun x y => g x = y

/--
lemma `update_eq_self_iff` / 引理 `update_eq_self_iff`

English:
lemma update_eq_self_iff
  statement: update f a b = f ↔ b = f a
  proof: by simp [update_eq_iff]

中文:
引理 update_eq_self_iff
  结论: update f a b = f ↔ b = f a
  证明: by simp [update_eq_iff]
-/
@[simp] lemma update_eq_self_iff : update f a b = f ↔ b = f a := by simp [update_eq_iff]

/--
lemma `eq_update_self_iff` / 引理 `eq_update_self_iff`

English:
lemma eq_update_self_iff
  statement: f = update f a b ↔ f a = b
  proof: by simp [eqComm]

中文:
引理 eq_update_self_iff
  结论: f = update f a b ↔ f a = b
  证明: by simp [eqComm]
-/
@[simp] lemma eq_update_self_iff : f = update f a b ↔ f a = b := by simp [eqComm]

/--
lemma `ne_update_self_iff` / 引理 `ne_update_self_iff`

English:
lemma ne_update_self_iff
  statement: f != update f a b ↔ f a != b
  proof: eq_update_self_iff.not

中文:
引理 ne_update_self_iff
  结论: f != update f a b ↔ f a != b
  证明: eq_update_self_iff.not

Depends on / 依赖: eq_update_self_iff, eq_update_self_iff.not
-/
lemma ne_update_self_iff : f != update f a b ↔ f a != b := eq_update_self_iff.not

/--
lemma `update_ne_self_iff` / 引理 `update_ne_self_iff`

English:
lemma update_ne_self_iff
  statement: update f a b != f ↔ b != f a
  proof: update_eq_self_iff.not

@[simp]

中文:
引理 update_ne_self_iff
  结论: update f a b != f ↔ b != f a
  证明: update_eq_self_iff.not

@[simp]

Depends on / 依赖: update_eq_self_iff, update_eq_self_iff.not
-/
lemma update_ne_self_iff : update f a b != f ↔ b != f a := update_eq_self_iff.not

@[simp]
/--
theorem `update_eq_self` / 定理 `update_eq_self`

English:
theorem update_eq_self
  given: (a : α) (f : forall a, β a)
  statement: update f a (f a) = f
  proof: update_eq_iff.2 ⟨rfl, fun _ _ => rfl⟩

中文:
定理 update_eq_self
  条件: (a : α) (f : 对任意 a, β a)
  结论: update f a (f a) = f
  证明: update_eq_iff.2 ⟨rfl, fun _ _ => rfl⟩

Depends on / 依赖: update_eq_iff
-/
theorem update_eq_self (a : α) (f : forall a, β a) : update f a (f a) = f :=
  update_eq_iff.2 ⟨rfl, fun _ _ => rfl⟩

/--
theorem `update_comp_eq_of_forall_ne'` / 定理 `update_comp_eq_of_forall_ne'`

English:
theorem update_comp_eq_of_forall_ne'
  statement: {α'} (g : forall a, β a) {f : α' -> α} {i : α} (a : β i)
  proof: funext fun _ => update_of_ne (h _) _ _

中文:
定理 update_comp_eq_of_对任意_ne'
  结论: {α'} (g : 对任意 a, β a) {f : α' -> α} {i : α} (a : β i)
  证明: funext fun _ => update_of_ne (h _) _ _

Depends on / 依赖: update_of_ne
-/
theorem update_comp_eq_of_forall_ne' {α'} (g : forall a, β a) {f : α' -> α} {i : α} (a : β i)
    (h : forall x, f x != i) : (fun j => (update g i a) (f j)) = fun j => g (f j) :=
  funext fun _ => update_of_ne (h _) _ _

variable [DecidableEq α']

/--
theorem `update_comp_eq_of_forall_ne` / 定理 `update_comp_eq_of_forall_ne`

English:
theorem update_comp_eq_of_forall_ne
  statement: {α β : Sort*} (g : α' -> β) {f : α -> α'} {i : α'} (a : β)
  proof: update_comp_eq_of_forall_ne' g a h

中文:
定理 update_comp_eq_of_对任意_ne
  结论: {α β : 类型层*} (g : α' -> β) {f : α -> α'} {i : α'} (a : β)
  证明: update_comp_eq_of_forall_ne' g a h

Depends on / 依赖: update_comp_eq_of_forall_ne
-/
theorem update_comp_eq_of_forall_ne {α β : Sort*} (g : α' -> β) {f : α -> α'} {i : α'} (a : β)
    (h : forall x, f x != i) : update g i a ∘ f = g ∘ f :=
  update_comp_eq_of_forall_ne' g a h

/--
theorem `update_comp_eq_of_injective'` / 定理 `update_comp_eq_of_injective'`

English:
theorem update_comp_eq_of_injective'
  statement: (g : forall a, β a) {f : α' -> α} (hf : Function.Injective f)
  proof: eq_update_iff.2 ⟨update_self .., fun _ hj => update_of_ne (hf.ne hj) _ _⟩

中文:
定理 update_comp_eq_of_injective'
  结论: (g : 对任意 a, β a) {f : α' -> α} (hf : 函数.单射 f)
  证明: eq_update_iff.2 ⟨update_self .., fun _ hj => update_of_ne (hf.ne hj) _ _⟩

Depends on / 依赖: eq_update_iff, hf.ne, update_of_ne, update_self
-/
theorem update_comp_eq_of_injective' (g : forall a, β a) {f : α' -> α} (hf : Function.Injective f)
    (i : α') (a : β (f i)) : (fun j => update g (f i) a (f j)) = update (fun i => g (f i)) i a :=
  eq_update_iff.2 ⟨update_self .., fun _ hj => update_of_ne (hf.ne hj) _ _⟩

/--
theorem `update_apply_of_injective` / 定理 `update_apply_of_injective`

English:
theorem update_apply_of_injective
  proof: congr_fun (update_comp_eq_of_injective' g hf i a) j

中文:
定理 update_apply_of_injective
  证明: congr_fun (update_comp_eq_of_injective' g hf i a) j

Depends on / 依赖: congr_fun, update_comp_eq_of_injective
-/
theorem update_apply_of_injective
    (g : forall a, β a) {f : α' -> α} (hf : Function.Injective f)
    (i : α') (a : β (f i)) (j : α') :
    update g (f i) a (f j) = update (fun i => g (f i)) i a j :=
  congr_fun (update_comp_eq_of_injective' g hf i a) j

/--
theorem `update_comp_eq_of_injective` / 定理 `update_comp_eq_of_injective`

English:
theorem update_comp_eq_of_injective
  statement: {β : Sort*} (g : α' -> β) {f : α -> α'}
  proof: update_comp_eq_of_injective' g hf i a

中文:
定理 update_comp_eq_of_injective
  结论: {β : 类型层*} (g : α' -> β) {f : α -> α'}
  证明: update_comp_eq_of_injective' g hf i a

Depends on / 依赖: update_comp_eq_of_injective
-/
theorem update_comp_eq_of_injective {β : Sort*} (g : α' -> β) {f : α -> α'}
    (hf : Function.Injective f) (i : α) (a : β) :
    Function.update g (f i) a ∘ f = Function.update (g ∘ f) i a :=
  update_comp_eq_of_injective' g hf i a

/-- Recursors can be pushed inside `Function.update`.

The `ctor` argument should be a one-argument constructor like `Sum.inl`,
and `recursor` should be an inductive recursor partially applied in all but that constructor,
such as `(Sum.rec · g)`.

In future, we should build some automation to generate applications like `Option.rec_update` for all
inductive types. -/
@[nolint unusedArguments]
/--
lemma `rec_update` / 引理 `rec_update`

English:
lemma rec_update
  statement: {ι κ : Sort*} {α : κ -> Sort*} [DecidableEq ι] [DecidableEq κ]
  proof: by
  grind

@[simp]

中文:
引理 rec_update
  结论: {ι κ : 类型层*} {α : κ -> 类型层*} [DecidableEq ι] [DecidableEq κ]
  证明: by
  grind

@[simp]
-/
lemma rec_update {ι κ : Sort*} {α : κ -> Sort*} [DecidableEq ι] [DecidableEq κ]
    {ctor : ι -> κ} (_ : Function.Injective ctor)
    (recursor : ((i : ι) -> α (ctor i)) -> ((i : κ) -> α i))
    (h : forall f i, recursor f (ctor i) = f i)
    (h2 : forall f₁ f₂ k, (forall i, ctor i != k) -> recursor f₁ k = recursor f₂ k)
    (f : (i : ι) -> α (ctor i)) (i : ι) (x : α (ctor i)) :
    recursor (update f i x) = update (recursor f) (ctor i) x := by
  grind

@[simp]
/--
lemma `_root_.Option.rec_update` / 引理 `_root_.Option.rec_update`

English:
lemma _root_.Option.rec_update
  statement: {α : Type*} {β : Option α -> Sort*} [DecidableEq α]
  proof: Function.rec_update (@Option.some.inj _) (Option.rec f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _

中文:
引理 _root_.选项类型.rec_update
  结论: {α : 类型} {β : 选项类型 α -> 类型层*} [DecidableEq α]
  证明: Function.rec_update (@Option.some.inj _) (Option.rec f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _

Depends on / 依赖: Function, Function.rec_update, Option.rec, Option.some.inj, rec_update
-/
lemma _root_.Option.rec_update {α : Type*} {β : Option α -> Sort*} [DecidableEq α]
    (f : β none) (g : forall a, β (.some a)) (a : α) (x : β (.some a)) :
    Option.rec f (update g a x) = update (Option.rec f g) (.some a) x :=
  Function.rec_update (@Option.some.inj _) (Option.rec f) (fun _ _ => rfl) (fun
    | _, _, some _, h => (h _ rfl).elim
    | _, _, none, _ => rfl) _ _ _

/--
theorem `apply_update` / 定理 `apply_update`

English:
theorem apply_update
  statement: {ι : Sort*} [DecidableEq ι] {α β : ι -> Sort*} (f : forall i, α i -> β i)
  proof: by
  grind

中文:
定理 apply_update
  结论: {ι : 类型层*} [DecidableEq ι] {α β : ι -> 类型层*} (f : 对任意 i, α i -> β i)
  证明: by
  grind
-/
theorem apply_update {ι : Sort*} [DecidableEq ι] {α β : ι -> Sort*} (f : forall i, α i -> β i)
    (g : forall i, α i) (i : ι) (v : α i) (j : ι) :
    f j (update g i v j) = update (fun k => f k (g k)) i (f i v) j := by
  grind

/--
theorem `apply_update₂` / 定理 `apply_update₂`

English:
theorem apply_update₂
  statement: {ι : Sort*} [DecidableEq ι] {α β γ : ι -> Sort*} (f : forall i, α i -> β i -> γ i)
  proof: by
  grind

中文:
定理 apply_update₂
  结论: {ι : 类型层*} [DecidableEq ι] {α β γ : ι -> 类型层*} (f : 对任意 i, α i -> β i -> γ i)
  证明: by
  grind
-/
theorem apply_update₂ {ι : Sort*} [DecidableEq ι] {α β γ : ι -> Sort*} (f : forall i, α i -> β i -> γ i)
    (g : forall i, α i) (h : forall i, β i) (i : ι) (v : α i) (w : β i) (j : ι) :
    f j (update g i v j) (update h i w j) = update (fun k => f k (g k) (h k)) i (f i v w) j := by
  grind

/--
theorem `pred_update` / 定理 `pred_update`

English:
theorem pred_update
  given: (P : forall ⦃a⦄, β a -> Prop) (f : forall a, β a) (a' : α) (v : β a') (a : α)
  proof: by
  grind

中文:
定理 pred_update
  条件: (P : 对任意 ⦃a⦄, β a -> 命题) (f : 对任意 a, β a) (a' : α) (v : β a') (a : α)
  证明: by
  grind
-/
theorem pred_update (P : forall ⦃a⦄, β a -> Prop) (f : forall a, β a) (a' : α) (v : β a') (a : α) :
    P (update f a' v a) ↔ a = a' ∧ P v ∨ a != a' ∧ P (f a) := by
  grind

/--
theorem `comp_update` / 定理 `comp_update`

English:
theorem comp_update
  given: {α' : Sort*} {β : Sort*} (f : α' -> β) (g : α -> α') (i : α) (v : α')
  proof: funext apply_update _ _ _ _

中文:
定理 comp_update
  条件: {α' : 类型层*} {β : 类型层*} (f : α' -> β) (g : α -> α') (i : α) (v : α')
  证明: funext apply_update _ _ _ _

Depends on / 依赖: apply_update
-/
theorem comp_update {α' : Sort*} {β : Sort*} (f : α' -> β) (g : α -> α') (i : α) (v : α') :
    f ∘ update g i v = update (f ∘ g) i (f v) :=
funext apply_update _ _ _ _

/--
theorem `update_comm` / 定理 `update_comm`

English:
theorem update_comm
  statement: {α} [DecidableEq α] {β : α -> Sort*} {a b : α} (h : a != b) (v : β a) (w : β b)
  proof: by
  grind

@[simp]

中文:
定理 update_comm
  结论: {α} [DecidableEq α] {β : α -> 类型层*} {a b : α} (h : a != b) (v : β a) (w : β b)
  证明: by
  grind

@[simp]
-/
theorem update_comm {α} [DecidableEq α] {β : α -> Sort*} {a b : α} (h : a != b) (v : β a) (w : β b)
    (f : forall a, β a) : update (update f a v) b w = update (update f b w) a v := by
  grind

@[simp]
/--
theorem `update_idem` / 定理 `update_idem`

English:
theorem update_idem
  given: {α} [DecidableEq α] {β : α -> Sort*} {a : α} (v w : β a) (f : forall a, β a)
  proof: by
  grind

@[simp]

中文:
定理 update_idem
  条件: {α} [DecidableEq α] {β : α -> 类型层*} {a : α} (v w : β a) (f : 对任意 a, β a)
  证明: by
  grind

@[simp]
-/
theorem update_idem {α} [DecidableEq α] {β : α -> Sort*} {a : α} (v w : β a) (f : forall a, β a) :
    update (update f a v) a w = update f a w := by
  grind

@[simp]
/--
theorem `_root_.Pi.map_update` / 定理 `_root_.Pi.map_update`

English:
theorem _root_.Pi.map_update
  statement: {ι : Sort*} [DecidableEq ι] {α β : ι -> Sort*}
  proof: by
  ext j
  obtain rfl | hij := eq_or_ne j i <;> simp [*]

@[simp]

中文:
定理 _root_.依赖函数类型.map_update
  结论: {ι : 类型层*} [DecidableEq ι] {α β : ι -> 类型层*}
  证明: by
  ext j
  obtain rfl | hij := eq_or_ne j i <;> simp [*]

@[simp]

Depends on / 依赖: eq_or_ne
-/
theorem _root_.Pi.map_update {ι : Sort*} [DecidableEq ι] {α β : ι -> Sort*}
    {f : forall i, α i -> β i}
    (g : forall i, α i) (i : ι) (a : α i) :
    Pi.map f (Function.update g i a) = Function.update (Pi.map f g) i (f i a) := by
  ext j
  obtain rfl | hij := eq_or_ne j i <;> simp [*]

@[simp]
/--
theorem `_root_.Pi.map_injective` / 定理 `_root_.Pi.map_injective`

English:
theorem _root_.Pi.map_injective
  proof: by
    classical
    have : Inhabited (forall i, α i) := ⟨fun _ => Classical.choice inferInstance⟩
    replace h := @h (Function.update default i x) (Function.update default i y) ?_
    · simpa using congrFun h i
    rw [Pi.map_update]; rw [Pi.map_update]; rw [hxy]
  mpr := .piMap

中文:
定理 _root_.依赖函数类型.map_injective
  证明: by
    classical
    have : Inhabited (forall i, α i) := ⟨fun _ => Classical.choice inferInstance⟩
    replace h := @h (Function.update default i x) (Function.update default i y) ?_
    · simpa using congrFun h i
    rw [Pi.map_update]; rw [Pi.map_update]; rw [hxy]
  mpr := .piMap

Depends on / 依赖: Classical, Classical.choice, Function, Function.update, Inhabited, Pi.map_update, choice, classical, map_update, replace, update
-/
theorem _root_.Pi.map_injective
    {ι : Sort*} {α β : ι -> Sort*} [forall i, Nonempty (α i)] {f : forall i, α i -> β i} :
    Injective (Pi.map f) ↔ forall i, Injective (f i) where
  mp h i x y hxy := by
    classical
    have : Inhabited (forall i, α i) := ⟨fun _ => Classical.choice inferInstance⟩
    replace h := @h (Function.update default i x) (Function.update default i y) ?_
    · simpa using congrFun h i
    rw [Pi.map_update]; rw [Pi.map_update]; rw [hxy]
  mpr := .piMap

end Update

noncomputable section Extend

variable {α β γ : Sort*} {f : α -> β}

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (f : α -> β) (g : α -> γ) (j : β -> γ)
  body: fun b =>
  open scoped Classical in
  if h : exists a, f a = b then g (Classical.choose h) else j b

中文:
定义 extend
  签名: (f : α -> β) (g : α -> γ) (j : β -> γ)
  定义体: fun b =>
  open scoped Classical in
  if h : exists a, f a = b then g (Classical.choose h) else j b
-/
def extend (f : α -> β) (g : α -> γ) (j : β -> γ) : β -> γ := fun b =>
  open scoped Classical in
  if h : exists a, f a = b then g (Classical.choose h) else j b

/--
Definition of `FactorsThrough` / `FactorsThrough` 的定义

English:
definition FactorsThrough
  signature: (g : α -> γ) (f : α -> β)
  body: forall ⦃a b⦄, f a = f b -> g a = g b

中文:
定义 FactorsThrough
  签名: (g : α -> γ) (f : α -> β)
  定义体: forall ⦃a b⦄, f a = f b -> g a = g b
-/
def FactorsThrough (g : α -> γ) (f : α -> β) : Prop :=
  forall ⦃a b⦄, f a = f b -> g a = g b

/--
theorem `extend_def` / 定理 `extend_def`

English:
theorem extend_def
  given: (f : α -> β) (g : α -> γ) (e' : β -> γ) (b : β) [Decidable (exists a, f a = b)]
  proof: by
  unfold extend
  congr

中文:
定理 extend_def
  条件: (f : α -> β) (g : α -> γ) (e' : β -> γ) (b : β) [可判定 (存在 a, f a = b)]
  证明: by
  unfold extend
  congr

Depends on / 依赖: extend
-/
theorem extend_def (f : α -> β) (g : α -> γ) (e' : β -> γ) (b : β) [Decidable (exists a, f a = b)] :
    extend f g e' b = if h : exists a, f a = b then g (Classical.choose h) else e' b := by
  unfold extend
  congr

/--
lemma `Injective.factorsThrough` / 引理 `Injective.factorsThrough`

English:
lemma Injective.factorsThrough
  given: (hf : Injective f) (g : α -> γ)
  statement: g.FactorsThrough f
  proof: fun _ _ h => congr_arg g (hf h)

中文:
引理 单射.factorsThrough
  条件: (hf : 单射 f) (g : α -> γ)
  结论: g.FactorsThrough f
  证明: fun _ _ h => congr_arg g (hf h)

Depends on / 依赖: congr_arg
-/
lemma Injective.factorsThrough (hf : Injective f) (g : α -> γ) : g.FactorsThrough f :=
  fun _ _ h => congr_arg g (hf h)

/--
lemma `FactorsThrough.extend_apply` / 引理 `FactorsThrough.extend_apply`

English:
lemma FactorsThrough.extend_apply
  given: {g : α -> γ} (hf : g.FactorsThrough f) (e' : β -> γ) (a : α)
  proof: by
  classical
  simp only [extend_def, dif_pos, exists_apply_eq_apply]
  exact hf (Classical.choose_spec (exists_apply_eq_apply f a))

@[simp]

中文:
引理 FactorsThrough.extend_apply
  条件: {g : α -> γ} (hf : g.FactorsThrough f) (e' : β -> γ) (a : α)
  证明: by
  classical
  simp only [extend_def, dif_pos, exists_apply_eq_apply]
  exact hf (Classical.choose_spec (exists_apply_eq_apply f a))

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, classical, dif_pos, exists_apply_eq_apply, extend_def
-/
lemma FactorsThrough.extend_apply {g : α -> γ} (hf : g.FactorsThrough f) (e' : β -> γ) (a : α) :
    extend f g e' (f a) = g a := by
  classical
  simp only [extend_def, dif_pos, exists_apply_eq_apply]
  exact hf (Classical.choose_spec (exists_apply_eq_apply f a))

@[simp]
/--
theorem `Injective.extend_apply` / 定理 `Injective.extend_apply`

English:
theorem Injective.extend_apply
  given: (hf : Injective f) (g : α -> γ) (e' : β -> γ) (a : α)
  proof: (hf.factorsThrough g).extend_apply e' a

@[simp]

中文:
定理 单射.extend_apply
  条件: (hf : 单射 f) (g : α -> γ) (e' : β -> γ) (a : α)
  证明: (hf.factorsThrough g).extend_apply e' a

@[simp]

Depends on / 依赖: extend_apply, factorsThrough, hf.factorsThrough
-/
theorem Injective.extend_apply (hf : Injective f) (g : α -> γ) (e' : β -> γ) (a : α) :
    extend f g e' (f a) = g a :=
  (hf.factorsThrough g).extend_apply e' a

@[simp]
/--
theorem `extend_apply'` / 定理 `extend_apply'`

English:
theorem extend_apply'
  given: (g : α -> γ) (e' : β -> γ) (b : β) (hb : ¬exists a, f a = b)
  proof: by
  classical
  simp [Function.extend_def, hb]

@[simp]

中文:
定理 extend_apply'
  条件: (g : α -> γ) (e' : β -> γ) (b : β) (hb : ¬存在 a, f a = b)
  证明: by
  classical
  simp [Function.extend_def, hb]

@[simp]

Depends on / 依赖: Function, Function.extend_def, classical, extend_def
-/
theorem extend_apply' (g : α -> γ) (e' : β -> γ) (b : β) (hb : ¬exists a, f a = b) :
    extend f g e' b = e' b := by
  classical
  simp [Function.extend_def, hb]

@[simp]
/--
theorem `extend_id` / 定理 `extend_id`

English:
theorem extend_id
  given: (g : α -> γ) (e' : α -> γ)
  proof: funext injective_id.extend_apply g _

中文:
定理 extend_id
  条件: (g : α -> γ) (e' : α -> γ)
  证明: funext injective_id.extend_apply g _

Depends on / 依赖: extend_apply, injective_id, injective_id.extend_apply
-/
theorem extend_id (g : α -> γ) (e' : α -> γ) :
    extend id g e' = g :=
funext injective_id.extend_apply g _

/--
theorem `Injective.extend_comp` / 定理 `Injective.extend_comp`

English:
theorem Injective.extend_comp
  statement: {α₁ α₂ α₃ : Sort*} {f₁₂ : α₁ -> α₂} (h₁₂ : Function.Injective f₁₂)
  proof: by
  ext a
  by_cases h₃ : exists b, f₂₃ b = a
  · obtain ⟨b, rfl⟩ := h₃
    rw [Injective.extend_apply h₂₃]
    by_cases h₂ : exists c, f₁₂ c = b
    · obtain ⟨c, rfl⟩ := h₂
      rw [h₁₂.extend_apply]
      exact (h₂₃.comp h₁₂).extend_apply _ _ _
    · rw [extend_apply' _ _ _ h₂, extend_apply', co

中文:
定理 单射.extend_comp
  结论: {α₁ α₂ α₃ : 类型层*} {f₁₂ : α₁ -> α₂} (h₁₂ : 函数.单射 f₁₂)
  证明: by
  ext a
  by_cases h₃ : exists b, f₂₃ b = a
  · obtain ⟨b, rfl⟩ := h₃
    rw [Injective.extend_apply h₂₃]
    by_cases h₂ : exists c, f₁₂ c = b
    · obtain ⟨c, rfl⟩ := h₂
      rw [h₁₂.extend_apply]
      exact (h₂₃.comp h₁₂).extend_apply _ _ _
    · rw [extend_apply' _ _ _ h₂, extend_apply', co

Depends on / 依赖: Exists, Exists.casesOn, Exists.intro, Injective, Injective.extend_apply, casesOn, comp_apply, extend_apply
-/
theorem Injective.extend_comp {α₁ α₂ α₃ : Sort*} {f₁₂ : α₁ -> α₂} (h₁₂ : Function.Injective f₁₂)
    {f₂₃ : α₂ -> α₃} (h₂₃ : Function.Injective f₂₃) (g : α₁ -> γ) (e' : α₃ -> γ) :
    extend (f₂₃ ∘ f₁₂) g e' = extend f₂₃ (extend f₁₂ g (e' ∘ f₂₃)) e' := by
  ext a
  by_cases h₃ : exists b, f₂₃ b = a
  · obtain ⟨b, rfl⟩ := h₃
    rw [Injective.extend_apply h₂₃]
    by_cases h₂ : exists c, f₁₂ c = b
    · obtain ⟨c, rfl⟩ := h₂
      rw [h₁₂.extend_apply]
      exact (h₂₃.comp h₁₂).extend_apply _ _ _
    · rw [extend_apply' _ _ _ h₂, extend_apply', comp_apply]
      exact fun h => h₂ (Exists.casesOn h fun c hc => Exists.intro c (h₂₃ hc))
  · rw [extend_apply' _ _ _ h₃, extend_apply']
    exact fun h => h₃ (Exists.casesOn h fun c hc => Exists.intro (f₁₂ c) (hc))

/--
lemma `factorsThrough_iff` / 引理 `factorsThrough_iff`

English:
lemma factorsThrough_iff
  given: (g : α -> γ) [Nonempty γ]
  statement: g.FactorsThrough f ↔ exists (e : β -> γ), g = e ∘ f
  proof: ⟨fun hf => ⟨extend f g (const β (Classical.arbitrary γ)),
      funext (fun x => by simp only [comp_apply, hf.extend_apply])⟩,
  fun h _ _ hf => by rw [Classical.choose_spec h, comp_apply, comp_apply, hf]⟩

中文:
引理 factorsThrough_iff
  条件: (g : α -> γ) [非空 γ]
  结论: g.FactorsThrough f ↔ 存在 (e : β -> γ), g = e ∘ f
  证明: ⟨fun hf => ⟨extend f g (const β (Classical.arbitrary γ)),
      funext (fun x => by simp only [comp_apply, hf.extend_apply])⟩,
  fun h _ _ hf => by rw [Classical.choose_spec h, comp_apply, comp_apply, hf]⟩

Depends on / 依赖: Classical, Classical.arbitrary, Classical.choose_spec, arbitrary, choose_spec, comp_apply, extend, extend_apply, hf.extend_apply
-/
lemma factorsThrough_iff (g : α -> γ) [Nonempty γ] : g.FactorsThrough f ↔ exists (e : β -> γ), g = e ∘ f :=
  ⟨fun hf => ⟨extend f g (const β (Classical.arbitrary γ)),
      funext (fun x => by simp only [comp_apply, hf.extend_apply])⟩,
  fun h _ _ hf => by rw [Classical.choose_spec h, comp_apply, comp_apply, hf]⟩

/--
lemma `apply_extend` / 引理 `apply_extend`

English:
lemma apply_extend
  given: {δ} {g : α -> γ} (F : γ -> δ) (f : α -> β) (e' : β -> γ) (b : β)
  proof: open scoped Classical in apply_dite F _ _ _

中文:
引理 apply_extend
  条件: {δ} {g : α -> γ} (F : γ -> δ) (f : α -> β) (e' : β -> γ) (b : β)
  证明: open scoped Classical in apply_dite F _ _ _

Depends on / 依赖: Classical, apply_dite, scoped
-/
lemma apply_extend {δ} {g : α -> γ} (F : γ -> δ) (f : α -> β) (e' : β -> γ) (b : β) :
    F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b :=
  open scoped Classical in apply_dite F _ _ _

/--
theorem `extend_injective` / 定理 `extend_injective`

English:
theorem extend_injective
  given: (hf : Injective f) (e' : β -> γ)
  statement: Injective fun g => extend f g e'
  proof: by
  intro g₁ g₂ hg
  refine funext fun x => ?_
  have H := congr_fun hg (f x)
  simp only [hf.extend_apply] at H
  exact H

中文:
定理 extend_injective
  条件: (hf : 单射 f) (e' : β -> γ)
  结论: 单射 fun g => extend f g e'
  证明: by
  intro g₁ g₂ hg
  refine funext fun x => ?_
  have H := congr_fun hg (f x)
  simp only [hf.extend_apply] at H
  exact H

Depends on / 依赖: congr_fun, extend_apply, hf.extend_apply
-/
theorem extend_injective (hf : Injective f) (e' : β -> γ) : Injective fun g => extend f g e' := by
  intro g₁ g₂ hg
  refine funext fun x => ?_
  have H := congr_fun hg (f x)
  simp only [hf.extend_apply] at H
  exact H

/--
lemma `FactorsThrough.extend_comp` / 引理 `FactorsThrough.extend_comp`

English:
lemma FactorsThrough.extend_comp
  given: {g : α -> γ} (e' : β -> γ) (hf : FactorsThrough g f)
  proof: funext fun a => hf.extend_apply e' a

@[simp]

中文:
引理 FactorsThrough.extend_comp
  条件: {g : α -> γ} (e' : β -> γ) (hf : FactorsThrough g f)
  证明: funext fun a => hf.extend_apply e' a

@[simp]

Depends on / 依赖: extend_apply, hf.extend_apply
-/
lemma FactorsThrough.extend_comp {g : α -> γ} (e' : β -> γ) (hf : FactorsThrough g f) :
    extend f g e' ∘ f = g :=
  funext fun a => hf.extend_apply e' a

@[simp]
/--
lemma `extend_const` / 引理 `extend_const`

English:
lemma extend_const
  given: (f : α -> β) (c : γ)
  statement: extend f (fun _ => c) (fun _ => c) = fun _ => c
  proof: funext fun _ => open scoped Classical in ite_id _

@[simp]

中文:
引理 extend_const
  条件: (f : α -> β) (c : γ)
  结论: extend f (fun _ => c) (fun _ => c) = fun _ => c
  证明: funext fun _ => open scoped Classical in ite_id _

@[simp]

Depends on / 依赖: Classical, ite_id, scoped
-/
lemma extend_const (f : α -> β) (c : γ) : extend f (fun _ => c) (fun _ => c) = fun _ => c :=
  funext fun _ => open scoped Classical in ite_id _

@[simp]
/--
theorem `extend_comp` / 定理 `extend_comp`

English:
theorem extend_comp
  given: (hf : Injective f) (g : α -> γ) (e' : β -> γ)
  statement: extend f g e' ∘ f = g
  proof: funext fun a => hf.extend_apply g e' a

中文:
定理 extend_comp
  条件: (hf : 单射 f) (g : α -> γ) (e' : β -> γ)
  结论: extend f g e' ∘ f = g
  证明: funext fun a => hf.extend_apply g e' a

Depends on / 依赖: extend_apply, hf.extend_apply
-/
theorem extend_comp (hf : Injective f) (g : α -> γ) (e' : β -> γ) : extend f g e' ∘ f = g :=
  funext fun a => hf.extend_apply g e' a

/--
theorem `Injective.surjective_comp_right'` / 定理 `Injective.surjective_comp_right'`

English:
theorem Injective.surjective_comp_right'
  given: (hf : Injective f) (g₀ : β -> γ)
  proof: fun g => ⟨extend f g g₀, Function.extend_comp hf _ _⟩

中文:
定理 单射.surjective_comp_right'
  条件: (hf : 单射 f) (g₀ : β -> γ)
  证明: fun g => ⟨extend f g g₀, Function.extend_comp hf _ _⟩

Depends on / 依赖: Function, Function.extend_comp, extend, extend_comp
-/
theorem Injective.surjective_comp_right' (hf : Injective f) (g₀ : β -> γ) :
    Surjective fun g : β -> γ => g ∘ f :=
  fun g => ⟨extend f g g₀, Function.extend_comp hf _ _⟩

/--
theorem `Injective.surjective_comp_right` / 定理 `Injective.surjective_comp_right`

English:
theorem Injective.surjective_comp_right
  given: [Nonempty γ] (hf : Injective f)
  proof: hf.surjective_comp_right' fun _ => Classical.choice ‹_›

中文:
定理 单射.surjective_comp_right
  条件: [非空 γ] (hf : 单射 f)
  证明: hf.surjective_comp_right' fun _ => Classical.choice ‹_›

Depends on / 依赖: Classical, Classical.choice, Nat.eq_sq_add_sq_iff, choice, decidable_of_iff, eq_sq_add_sq_iff, hf.surjective_comp_right, surjective_comp_right
-/
theorem Injective.surjective_comp_right [Nonempty γ] (hf : Injective f) :
    Surjective fun g : β -> γ => g ∘ f :=
  hf.surjective_comp_right' fun _ => Classical.choice ‹_›

/--
theorem `surjective_comp_right_iff_injective` / 定理 `surjective_comp_right_iff_injective`

English:
theorem surjective_comp_right_iff_injective
  given: {γ : Type*} [Nontrivial γ]
  proof: by
  classical
  refine ⟨not_imp_not.mp fun not_inj surj => not_subsingleton γ ⟨fun c c' => ?_⟩,
    (·.surjective_comp_right)⟩
  simp only [Injective, not_forall] at not_inj
  have ⟨a₁, a₂, eq, ne⟩ := not_inj
  have ⟨f, hf⟩ := surj (if · = a₂ then c else c')
  have h₁ := congr_fun hf a₁
  have h₂ :

中文:
定理 surjective_comp_right_iff_injective
  条件: {γ : 类型} [非平凡 γ]
  证明: by
  classical
  refine ⟨not_imp_not.mp fun not_inj surj => not_subsingleton γ ⟨fun c c' => ?_⟩,
    (·.surjective_comp_right)⟩
  simp only [Injective, not_forall] at not_inj
  have ⟨a₁, a₂, eq, ne⟩ := not_inj
  have ⟨f, hf⟩ := surj (if · = a₂ then c else c')
  have h₁ := congr_fun hf a₁
  have h₂ :

Depends on / 依赖: Injective, classical, comp_apply, congr_fun, if_neg, not_forall, not_imp_not, not_imp_not.mp, not_inj, not_subsingleton, reduceIte, surjective_comp_right
-/
theorem surjective_comp_right_iff_injective {γ : Type*} [Nontrivial γ] :
    Surjective (fun g : β -> γ => g ∘ f) ↔ Injective f := by
  classical
  refine ⟨not_imp_not.mp fun not_inj surj => not_subsingleton γ ⟨fun c c' => ?_⟩,
    (·.surjective_comp_right)⟩
  simp only [Injective, not_forall] at not_inj
  have ⟨a₁, a₂, eq, ne⟩ := not_inj
  have ⟨f, hf⟩ := surj (if · = a₂ then c else c')
  have h₁ := congr_fun hf a₁
  have h₂ := congr_fun hf a₂
  simp only [comp_apply, if_neg ne, reduceIte] at h₁ h₂
  rw [← h₁]; rw [eq]; rw [h₂]

/--
theorem `Bijective.comp_right` / 定理 `Bijective.comp_right`

English:
theorem Bijective.comp_right
  given: (hf : Bijective f)
  statement: Bijective fun g : β -> γ => g ∘ f
  proof: ⟨hf.surjective.injective_comp_right, fun g =>
    ⟨g ∘ surjInv hf.surjective,
     by simp only [comp_assoc g _ f, (leftInverse_surjInv hf).comp_eq_id, comp_id]⟩⟩

中文:
定理 双射.comp_right
  条件: (hf : 双射 f)
  结论: 双射 fun g : β -> γ => g ∘ f
  证明: ⟨hf.surjective.injective_comp_right, fun g =>
    ⟨g ∘ surjInv hf.surjective,
     by simp only [comp_assoc g _ f, (leftInverse_surjInv hf).comp_eq_id, comp_id]⟩⟩

Depends on / 依赖: comp_assoc, comp_eq_id, comp_id, hf.surjective, hf.surjective.injective_comp_right, injective_comp_right, leftInverse_surjInv, surjInv, surjective
-/
theorem Bijective.comp_right (hf : Bijective f) : Bijective fun g : β -> γ => g ∘ f :=
  ⟨hf.surjective.injective_comp_right, fun g =>
    ⟨g ∘ surjInv hf.surjective,
     by simp only [comp_assoc g _ f, (leftInverse_surjInv hf).comp_eq_id, comp_id]⟩⟩

end Extend

namespace FactorsThrough

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  given: {α β : Sort*} {f : α -> β}
  statement: FactorsThrough f f
  proof: fun _ _ => id

中文:
定理 rfl
  条件: {α β : 类型层*} {f : α -> β}
  结论: FactorsThrough f f
  证明: fun _ _ => id
-/
protected theorem rfl {α β : Sort*} {f : α -> β} : FactorsThrough f f := fun _ _ => id

/--
theorem `comp_left` / 定理 `comp_left`

English:
theorem comp_left
  given: {α β γ δ : Sort*} {f : α -> β} {g : α -> γ} (h : FactorsThrough g f) (g' : γ -> δ)
  proof: fun _x _y hxy =>
  congr_arg g' (h hxy)

中文:
定理 comp_left
  条件: {α β γ δ : 类型层*} {f : α -> β} {g : α -> γ} (h : FactorsThrough g f) (g' : γ -> δ)
  证明: fun _x _y hxy =>
  congr_arg g' (h hxy)
-/
theorem comp_left {α β γ δ : Sort*} {f : α -> β} {g : α -> γ} (h : FactorsThrough g f) (g' : γ -> δ) :
    FactorsThrough (g' ∘ g) f := fun _x _y hxy =>
  congr_arg g' (h hxy)

/--
theorem `comp_right` / 定理 `comp_right`

English:
theorem comp_right
  given: {α β γ δ : Sort*} {f : α -> β} {g : α -> γ} (h : FactorsThrough g f) (g' : δ -> α)
  proof: fun _x _y hxy =>
  h hxy

中文:
定理 comp_right
  条件: {α β γ δ : 类型层*} {f : α -> β} {g : α -> γ} (h : FactorsThrough g f) (g' : δ -> α)
  证明: fun _x _y hxy =>
  h hxy
-/
theorem comp_right {α β γ δ : Sort*} {f : α -> β} {g : α -> γ} (h : FactorsThrough g f) (g' : δ -> α) :
    FactorsThrough (g ∘ g') (f ∘ g') := fun _x _y hxy =>
  h hxy

end FactorsThrough

section CurryAndUncurry

/--
theorem `uncurry_def` / 定理 `uncurry_def`

English:
theorem uncurry_def
  given: {α β γ} (f : α -> β -> γ)
  statement: uncurry f = fun p => f p.1 p.2
  proof: rfl

中文:
定理 uncurry_def
  条件: {α β γ} (f : α -> β -> γ)
  结论: uncurry f = fun p => f p.1 p.2
  证明: rfl
-/
theorem uncurry_def {α β γ} (f : α -> β -> γ) : uncurry f = fun p => f p.1 p.2 :=
  rfl

/--
theorem `uncurry_injective` / 定理 `uncurry_injective`

English:
theorem uncurry_injective
  given: {α β γ}
  statement: Function.Injective (uncurry : (α -> β -> γ) -> _)
  proof: LeftInverse.injective curry_uncurry

中文:
定理 uncurry_injective
  条件: {α β γ}
  结论: 函数.单射 (uncurry : (α -> β -> γ) -> _)
  证明: LeftInverse.injective curry_uncurry

Depends on / 依赖: LeftInverse, LeftInverse.injective, curry_uncurry, injective
-/
theorem uncurry_injective {α β γ} : Function.Injective (uncurry : (α -> β -> γ) -> _) :=
  LeftInverse.injective curry_uncurry

/--
theorem `curry_injective` / 定理 `curry_injective`

English:
theorem curry_injective
  given: {α β γ}
  statement: Function.Injective (curry : (α × β -> γ) -> _)
  proof: LeftInverse.injective uncurry_curry

中文:
定理 curry_injective
  条件: {α β γ}
  结论: 函数.单射 (curry : (α × β -> γ) -> _)
  证明: LeftInverse.injective uncurry_curry

Depends on / 依赖: LeftInverse, LeftInverse.injective, injective, uncurry_curry
-/
theorem curry_injective {α β γ} : Function.Injective (curry : (α × β -> γ) -> _) :=
  LeftInverse.injective uncurry_curry

/--
theorem `uncurry_flip` / 定理 `uncurry_flip`

English:
theorem uncurry_flip
  given: {α β γ} (f : α -> β -> γ)
  statement: uncurry (flip f) = uncurry f ∘ Prod.swap
  proof: rfl

中文:
定理 uncurry_flip
  条件: {α β γ} (f : α -> β -> γ)
  结论: uncurry (flip f) = uncurry f ∘ 积类型.swap
  证明: rfl
-/
theorem uncurry_flip {α β γ} (f : α -> β -> γ) : uncurry (flip f) = uncurry f ∘ Prod.swap :=
  rfl

/--
theorem `flip_curry` / 定理 `flip_curry`

English:
theorem flip_curry
  given: {α β γ} (f : α × β -> γ)
  statement: flip (curry f) = curry (f ∘ Prod.swap)
  proof: rfl

中文:
定理 flip_curry
  条件: {α β γ} (f : α × β -> γ)
  结论: flip (curry f) = curry (f ∘ 积类型.swap)
  证明: rfl
-/
theorem flip_curry {α β γ} (f : α × β -> γ) : flip (curry f) = curry (f ∘ Prod.swap) :=
  rfl

/--
theorem `curry_update` / 定理 `curry_update`

English:
theorem curry_update
  statement: {α α' β : Type*} [DecidableEq α] [DecidableEq α']
  proof: by
  ext a a'
  let ⟨a₂, a₂'⟩ := aa'
  obtain rfl | ha := eq_or_ne a a₂ <;> obtain rfl | ha' := eq_or_ne a' a₂' <;> simp [*]

中文:
定理 curry_update
  结论: {α α' β : 类型} [DecidableEq α] [DecidableEq α']
  证明: by
  ext a a'
  let ⟨a₂, a₂'⟩ := aa'
  obtain rfl | ha := eq_or_ne a a₂ <;> obtain rfl | ha' := eq_or_ne a' a₂' <;> simp [*]

Depends on / 依赖: eq_or_ne
-/
theorem curry_update {α α' β : Type*} [DecidableEq α] [DecidableEq α']
    (f : α × α' -> β) (aa' : α × α') (b : β) :
    curry (Function.update f aa' b) =
      Function.update (curry f) aa'.1 (Function.update (curry f aa'.1) aa'.2 b) := by
  ext a a'
  let ⟨a₂, a₂'⟩ := aa'
  obtain rfl | ha := eq_or_ne a a₂ <;> obtain rfl | ha' := eq_or_ne a' a₂' <;> simp [*]

/--
theorem `uncurry_update_update` / 定理 `uncurry_update_update`

English:
theorem uncurry_update_update
  statement: {α α' β : Type*} [DecidableEq α] [DecidableEq α']
  proof: by
  apply curry_injective
  simp [curry_update]

中文:
定理 uncurry_update_update
  结论: {α α' β : 类型} [DecidableEq α] [DecidableEq α']
  证明: by
  apply curry_injective
  simp [curry_update]

Depends on / 依赖: curry_injective, curry_update
-/
theorem uncurry_update_update {α α' β : Type*} [DecidableEq α] [DecidableEq α']
    (f : α -> α' -> β) (a : α) (a' : α') (b : β) :
    uncurry (Function.update f a (Function.update (f a) a' b)) =
      Function.update (uncurry f) (a, a') b := by
  apply curry_injective
  simp [curry_update]

end CurryAndUncurry

section Uncurry

variable {α β γ δ : Type*}

/--
Definition of `HasUncurry` / `HasUncurry` 的定义

English:
class HasUncurry
  parameters: (α : Type*) (β : outParam Type*) (γ : outParam Type*)
  axioms and operations (1):
    - uncurry : α -> β -> γ

中文:
类 有Uncurry
  参数: (α : 类型) (β : outParam 类型) (γ : outParam 类型)
  公理与运算 (1 个):
    - uncurry : α -> β -> γ
-/
class HasUncurry (α : Type*) (β : outParam Type*) (γ : outParam Type*) where
  /-- Uncurrying operator. The most generic use is to recursively uncurry. For instance
  `f : α → β → γ → δ` will be turned into `↿f : α × β × γ → δ`. One can also add instances
  for bundled maps. -/
  uncurry : α -> β -> γ

@[inherit_doc] prefix:max "↿" => HasUncurry.uncurry

/--
Instance `hasUncurryBase` / 实例 `hasUncurryBase`

English:
instance hasUncurryBase
  signature: : HasUncurry (α -> β) α β
  body: ⟨id⟩

中文:
实例 hasUncurryBase
  签名: : 有Uncurry (α -> β) α β
  定义体: ⟨id⟩
-/
instance hasUncurryBase : HasUncurry (α -> β) α β :=
  ⟨id⟩

/--
Instance `hasUncurryInduction` / 实例 `hasUncurryInduction`

English:
instance hasUncurryInduction
  signature: [HasUncurry β γ δ]
  body: ⟨fun f p => ↿(f p.1) p.2⟩

中文:
实例 hasUncurryInduction
  签名: [有Uncurry β γ δ]
  定义体: ⟨fun f p => ↿(f p.1) p.2⟩
-/
instance hasUncurryInduction [HasUncurry β γ δ] : HasUncurry (α -> β) (α × γ) δ :=
  ⟨fun f p => ↿(f p.1) p.2⟩

end Uncurry

/--
Definition of `Involutive` / `Involutive` 的定义

English:
definition Involutive
  signature: {α} (f : α -> α)
  body: forall x, f (f x) = x

中文:
定义 对合
  签名: {α} (f : α -> α)
  定义体: forall x, f (f x) = x
-/
def Involutive {α} (f : α -> α) : Prop :=
  forall x, f (f x) = x

/--
theorem `_root_.Bool.involutive_not` / 定理 `_root_.Bool.involutive_not`

English:
theorem _root_.Bool.involutive_not
  statement: Involutive not
  proof: Bool.not_not

中文:
定理 _root_.布尔值.involutive_not
  结论: 对合 not
  证明: Bool.not_not

Depends on / 依赖: Bool.not_not, not_not
-/
theorem _root_.Bool.involutive_not : Involutive not :=
  Bool.not_not

namespace Involutive

variable {α : Sort u} {f : α -> α} (h : Involutive f)

include h

@[simp]
/--
theorem `comp_self` / 定理 `comp_self`

English:
theorem comp_self
  statement: f ∘ f = id
  proof: funext h

中文:
定理 comp_self
  结论: f ∘ f = id
  证明: funext h
-/
theorem comp_self : f ∘ f = id :=
  funext h

/--
theorem `leftInverse` / 定理 `leftInverse`

English:
theorem leftInverse
  statement: LeftInverse f f
  proof: h

中文:
定理 leftInverse
  结论: 左逆 f f
  证明: h
-/
protected theorem leftInverse : LeftInverse f f := h

/--
theorem `leftInverse_iff` / 定理 `leftInverse_iff`

English:
theorem leftInverse_iff
  given: {g : α -> α}
  proof: ⟨fun hg => funext fun x => by rw [← h x, hg, h], fun he => he ▸ h.leftInverse⟩

中文:
定理 leftInverse_iff
  条件: {g : α -> α}
  证明: ⟨fun hg => funext fun x => by rw [← h x, hg, h], fun he => he ▸ h.leftInverse⟩

Depends on / 依赖: h.leftInverse, leftInverse
-/
theorem leftInverse_iff {g : α -> α} :
    g.LeftInverse f ↔ g = f :=
  ⟨fun hg => funext fun x => by rw [← h x, hg, h], fun he => he ▸ h.leftInverse⟩

/--
theorem `rightInverse` / 定理 `rightInverse`

English:
theorem rightInverse
  statement: RightInverse f f
  proof: h

中文:
定理 rightInverse
  结论: 右逆 f f
  证明: h
-/
protected theorem rightInverse : RightInverse f f := h

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: Injective f
  proof: h.leftInverse.injective

中文:
定理 injective
  结论: 单射 f
  证明: h.leftInverse.injective
-/
protected theorem injective : Injective f := h.leftInverse.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  statement: Surjective f
  proof: fun x => ⟨f x, h x⟩

中文:
定理 surjective
  结论: 满射 f
  证明: fun x => ⟨f x, h x⟩
-/
protected theorem surjective : Surjective f := fun x => ⟨f x, h x⟩

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  statement: Bijective f
  proof: ⟨h.injective, h.surjective⟩

中文:
定理 bijective
  结论: 双射 f
  证明: ⟨h.injective, h.surjective⟩
-/
protected theorem bijective : Bijective f := ⟨h.injective, h.surjective⟩

/--
theorem `ite_not` / 定理 `ite_not`

English:
theorem ite_not
  given: (P : Prop) [Decidable P] (x : α)
  proof: by rw [apply_ite f, h, ite_not]

中文:
定理 ite_not
  条件: (P : 命题) [可判定 P] (x : α)
  证明: by rw [apply_ite f, h, ite_not]
-/
protected theorem ite_not (P : Prop) [Decidable P] (x : α) :
    f (ite P x (f x)) = ite (¬P) x (f x) := by rw [apply_ite f, h, ite_not]

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: {x y : α}
  statement: f x = y ↔ x = f y
  proof: h.injective.eq_iff' (h y)

中文:
定理 eq_iff
  条件: {x y : α}
  结论: f x = y ↔ x = f y
  证明: h.injective.eq_iff' (h y)
-/
protected theorem eq_iff {x y : α} : f x = y ↔ x = f y :=
  h.injective.eq_iff' (h y)

end Involutive

/--
lemma `not_involutive` / 引理 `not_involutive`

English:
lemma not_involutive
  statement: Involutive Not
  proof: fun _ => propext not_not

中文:
引理 not_involutive
  结论: 对合 非
  证明: fun _ => propext not_not

Depends on / 依赖: not_not, propext
-/
lemma not_involutive : Involutive Not := fun _ => propext not_not
/--
lemma `not_injective` / 引理 `not_injective`

English:
lemma not_injective
  statement: Injective Not
  proof: not_involutive.injective

中文:
引理 not_injective
  结论: 单射 非
  证明: not_involutive.injective

Depends on / 依赖: injective, not_involutive, not_involutive.injective
-/
lemma not_injective : Injective Not := not_involutive.injective
/--
lemma `not_surjective` / 引理 `not_surjective`

English:
lemma not_surjective
  statement: Surjective Not
  proof: not_involutive.surjective

中文:
引理 not_surjective
  结论: 满射 非
  证明: not_involutive.surjective

Depends on / 依赖: not_involutive, not_involutive.surjective, surjective
-/
lemma not_surjective : Surjective Not := not_involutive.surjective
/--
lemma `not_bijective` / 引理 `not_bijective`

English:
lemma not_bijective
  statement: Bijective Not
  proof: not_involutive.bijective

@[simp]

中文:
引理 not_bijective
  结论: 双射 非
  证明: not_involutive.bijective

@[simp]

Depends on / 依赖: bijective, not_involutive, not_involutive.bijective
-/
lemma not_bijective : Bijective Not := not_involutive.bijective

@[simp]
/--
lemma `symm_apply_eq_iff` / 引理 `symm_apply_eq_iff`

English:
lemma symm_apply_eq_iff
  given: {α : Sort*} {f : α -> α}
  statement: Std.Symm (f · = ·) ↔ Involutive f
  proof: by
  simp [symm_def, Involutive]

@[deprecated (since := "2026-06-10")] alias symmetric_apply_eq_iff := symm_apply_eq_iff

中文:
引理 symm_apply_eq_iff
  条件: {α : 类型层*} {f : α -> α}
  结论: Std.Symm (f · = ·) ↔ 对合 f
  证明: by
  simp [symm_def, Involutive]

@[deprecated (since := "2026-06-10")] alias symmetric_apply_eq_iff := symm_apply_eq_iff

Depends on / 依赖: Involutive, symm_def
-/
lemma symm_apply_eq_iff {α : Sort*} {f : α -> α} : Std.Symm (f · = ·) ↔ Involutive f := by
  simp [symm_def, Involutive]

@[deprecated (since := "2026-06-10")] alias symmetric_apply_eq_iff := symm_apply_eq_iff

/--
Definition of `Injective2` / `Injective2` 的定义

English:
definition Injective2
  signature: {α β γ : Sort*} (f : α -> β -> γ)
  body: forall ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ -> a₁ = a₂ ∧ b₁ = b₂

中文:
定义 Injective2
  签名: {α β γ : 类型层*} (f : α -> β -> γ)
  定义体: forall ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ -> a₁ = a₂ ∧ b₁ = b₂
-/
def Injective2 {α β γ : Sort*} (f : α -> β -> γ) : Prop :=
  forall ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ -> a₁ = a₂ ∧ b₁ = b₂

namespace Injective2

variable {α β γ : Sort*} {f : α -> β -> γ}

/--
theorem `left` / 定理 `left`

English:
theorem left
  given: (hf : Injective2 f) (b : β)
  statement: Function.Injective fun a => f a b
  proof: fun _ _ h => (hf h).left

中文:
定理 left
  条件: (hf : Injective2 f) (b : β)
  结论: 函数.单射 fun a => f a b
  证明: fun _ _ h => (hf h).left
-/
protected theorem left (hf : Injective2 f) (b : β) : Function.Injective fun a => f a b :=
  fun _ _ h => (hf h).left

/--
theorem `right` / 定理 `right`

English:
theorem right
  given: (hf : Injective2 f) (a : α)
  statement: Function.Injective (f a)
  proof: fun _ _ h => (hf h).right

中文:
定理 right
  条件: (hf : Injective2 f) (a : α)
  结论: 函数.单射 (f a)
  证明: fun _ _ h => (hf h).right
-/
protected theorem right (hf : Injective2 f) (a : α) : Function.Injective (f a) :=
  fun _ _ h => (hf h).right

/--
theorem `uncurry` / 定理 `uncurry`

English:
theorem uncurry
  given: {α β γ : Type*} {f : α -> β -> γ} (hf : Injective2 f)
  proof: fun ⟨_, _⟩ ⟨_, _⟩ h => (hf h).elim (congr_arg₂ _)

中文:
定理 uncurry
  条件: {α β γ : 类型} {f : α -> β -> γ} (hf : Injective2 f)
  证明: fun ⟨_, _⟩ ⟨_, _⟩ h => (hf h).elim (congr_arg₂ _)
-/
protected theorem uncurry {α β γ : Type*} {f : α -> β -> γ} (hf : Injective2 f) :
    Function.Injective (uncurry f) :=
  fun ⟨_, _⟩ ⟨_, _⟩ h => (hf h).elim (congr_arg₂ _)

/--
theorem `left'` / 定理 `left'`

English:
theorem left'
  given: (hf : Injective2 f) [Nonempty β]
  statement: Function.Injective f
  proof: fun _ _ h =>
  let ⟨b⟩ := ‹Nonempty β›
hf.left b (congr_fun h b :)

中文:
定理 left'
  条件: (hf : Injective2 f) [非空 β]
  结论: 函数.单射 f
  证明: fun _ _ h =>
  let ⟨b⟩ := ‹Nonempty β›
hf.left b (congr_fun h b :)
-/
theorem left' (hf : Injective2 f) [Nonempty β] : Function.Injective f := fun _ _ h =>
  let ⟨b⟩ := ‹Nonempty β›
hf.left b (congr_fun h b :)

/--
theorem `right'` / 定理 `right'`

English:
theorem right'
  given: (hf : Injective2 f) [Nonempty α]
  statement: Function.Injective fun b a => f a b
  proof: fun _ _ h =>
    let ⟨a⟩ := ‹Nonempty α›
hf.right a (congr_fun h a :)

中文:
定理 right'
  条件: (hf : Injective2 f) [非空 α]
  结论: 函数.单射 fun b a => f a b
  证明: fun _ _ h =>
    let ⟨a⟩ := ‹Nonempty α›
hf.right a (congr_fun h a :)

Depends on / 依赖: Nonempty, congr_fun, hf.right
-/
theorem right' (hf : Injective2 f) [Nonempty α] : Function.Injective fun b a => f a b :=
  fun _ _ h =>
    let ⟨a⟩ := ‹Nonempty α›
hf.right a (congr_fun h a :)

/--
theorem `eq_iff` / 定理 `eq_iff`

English:
theorem eq_iff
  given: (hf : Injective2 f) {a₁ a₂ b₁ b₂}
  statement: f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
  proof: ⟨fun h => hf h, fun ⟨h1, h2⟩ => congr_arg₂ f h1 h2⟩

中文:
定理 eq_iff
  条件: (hf : Injective2 f) {a₁ a₂ b₁ b₂}
  结论: f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂
  证明: ⟨fun h => hf h, fun ⟨h1, h2⟩ => congr_arg₂ f h1 h2⟩
-/
theorem eq_iff (hf : Injective2 f) {a₁ a₂ b₁ b₂} : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun h => hf h, fun ⟨h1, h2⟩ => congr_arg₂ f h1 h2⟩

end Injective2

section Sometimes

/--
Definition of `sometimes` / `sometimes` 的定义

English:
definition sometimes
  signature: {α β} [Nonempty β] (f : α -> β)
  body: open scoped Classical in
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

中文:
定义 sometimes
  签名: {α β} [非空 β] (f : α -> β)
  定义体: open scoped Classical in
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

Depends on / 依赖: Classical, Classical.choice, Nonempty, choice, scoped
-/
noncomputable def sometimes {α β} [Nonempty β] (f : α -> β) : β :=
  open scoped Classical in
  if h : Nonempty α then f (Classical.choice h) else Classical.choice ‹_›

/--
theorem `sometimes_eq` / 定理 `sometimes_eq`

English:
theorem sometimes_eq
  given: {p : Prop} {α} [Nonempty α] (f : p -> α) (a : p)
  statement: sometimes f = f a
  proof: dif_pos ⟨a⟩

中文:
定理 sometimes_eq
  条件: {p : 命题} {α} [非空 α] (f : p -> α) (a : p)
  结论: sometimes f = f a
  证明: dif_pos ⟨a⟩

Depends on / 依赖: dif_pos
-/
theorem sometimes_eq {p : Prop} {α} [Nonempty α] (f : p -> α) (a : p) : sometimes f = f a :=
  dif_pos ⟨a⟩

/--
theorem `sometimes_spec` / 定理 `sometimes_spec`

English:
theorem sometimes_spec
  statement: {p : Prop} {α} [Nonempty α] (P : α -> Prop) (f : p -> α) (a : p)
  proof: by
  rwa [sometimes_eq]

中文:
定理 sometimes_spec
  结论: {p : 命题} {α} [非空 α] (P : α -> 命题) (f : p -> α) (a : p)
  证明: by
  rwa [sometimes_eq]

Depends on / 依赖: sometimes_eq
-/
theorem sometimes_spec {p : Prop} {α} [Nonempty α] (P : α -> Prop) (f : p -> α) (a : p)
    (h : P (f a)) : P (sometimes f) := by
  rwa [sometimes_eq]

end Sometimes

end Function

variable {α β : Sort*}

/--
lemma `forall_existsUnique_iff` / 引理 `forall_existsUnique_iff`

English:
lemma forall_existsUnique_iff
  given: {r : α -> β -> Prop}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · refine ⟨fun a => (h a).choose, fun hr => ?_, fun h' => h' ▸ ?_⟩
    exacts [((h _).choose_spec.2 _ hr).symm, (h _).choose_spec.1]
  · rintro ⟨f, hf⟩
    simp [hf]

中文:
引理 对任意_存在Unique_iff
  条件: {r : α -> β -> 命题}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · refine ⟨fun a => (h a).choose, fun hr => ?_, fun h' => h' ▸ ?_⟩
    exacts [((h _).choose_spec.2 _ hr).symm, (h _).choose_spec.1]
  · rintro ⟨f, hf⟩
    simp [hf]

Depends on / 依赖: choose_spec, exacts
-/
lemma forall_existsUnique_iff {r : α -> β -> Prop} :
    (forall a, exists! b, r a b) ↔ exists f : α -> β, forall {a b}, r a b ↔ f a = b := by
  refine ⟨fun h => ?_, ?_⟩
  · refine ⟨fun a => (h a).choose, fun hr => ?_, fun h' => h' ▸ ?_⟩
    exacts [((h _).choose_spec.2 _ hr).symm, (h _).choose_spec.1]
  · rintro ⟨f, hf⟩
    simp [hf]

/--
lemma `forall_existsUnique_iff'` / 引理 `forall_existsUnique_iff'`

English:
lemma forall_existsUnique_iff'
  given: {r : α -> β -> Prop}
  proof: by
  simp [forall_existsUnique_iff, funext_iff]

中文:
引理 对任意_存在Unique_iff'
  条件: {r : α -> β -> 命题}
  证明: by
  simp [forall_existsUnique_iff, funext_iff]

Depends on / 依赖: forall_existsUnique_iff, funext_iff
-/
lemma forall_existsUnique_iff' {r : α -> β -> Prop} :
    (forall a, exists! b, r a b) ↔ exists f : α -> β, r = (f · = ·) := by
  simp [forall_existsUnique_iff, funext_iff]

/--
lemma `Std.Symm.forall_existsUnique_iff'` / 引理 `Std.Symm.forall_existsUnique_iff'`

English:
lemma Std.Symm.forall_existsUnique_iff'
  given: {r : α -> α -> Prop} [Std.Symm r]
  proof: by
  refine ⟨fun h => ?_, fun ⟨f, _, hf⟩ => forall_existsUnique_iff'.2 ⟨f, hf⟩⟩
  rcases forall_existsUnique_iff'.1 h with ⟨f, rfl : r = _⟩
  exact ⟨f, symm_apply_eq_iff.1 ‹_›, rfl⟩

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff' := Std.Symm.forall_existsUni

中文:
引理 Std.Symm.对任意_存在Unique_iff'
  条件: {r : α -> α -> 命题} [Std.Symm r]
  证明: by
  refine ⟨fun h => ?_, fun ⟨f, _, hf⟩ => forall_existsUnique_iff'.2 ⟨f, hf⟩⟩
  rcases forall_existsUnique_iff'.1 h with ⟨f, rfl : r = _⟩
  exact ⟨f, symm_apply_eq_iff.1 ‹_›, rfl⟩

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff' := Std.Symm.forall_existsUni
-/
protected lemma Std.Symm.forall_existsUnique_iff' {r : α -> α -> Prop} [Std.Symm r] :
    (forall a, exists! b, r a b) ↔ exists f : α -> α, Involutive f ∧ r = (f · = ·) := by
  refine ⟨fun h => ?_, fun ⟨f, _, hf⟩ => forall_existsUnique_iff'.2 ⟨f, hf⟩⟩
  rcases forall_existsUnique_iff'.1 h with ⟨f, rfl : r = _⟩
  exact ⟨f, symm_apply_eq_iff.1 ‹_›, rfl⟩

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff' := Std.Symm.forall_existsUnique_iff'

/--
lemma `Std.Symm.forall_existsUnique_iff` / 引理 `Std.Symm.forall_existsUnique_iff`

English:
lemma Std.Symm.forall_existsUnique_iff
  given: {r : α -> α -> Prop} [Std.Symm r]
  proof: by
  simp [Std.Symm.forall_existsUnique_iff', funext_iff]

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff := Std.Symm.forall_existsUnique_iff

中文:
引理 Std.Symm.对任意_存在Unique_iff
  条件: {r : α -> α -> 命题} [Std.Symm r]
  证明: by
  simp [Std.Symm.forall_existsUnique_iff', funext_iff]

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff := Std.Symm.forall_existsUnique_iff
-/
protected lemma Std.Symm.forall_existsUnique_iff {r : α -> α -> Prop} [Std.Symm r] :
    (forall a, exists! b, r a b) ↔ exists f : α -> α, Involutive f ∧ forall {a b}, r a b ↔ f a = b := by
  simp [Std.Symm.forall_existsUnique_iff', funext_iff]

@[deprecated (since := "2026-06-10")]
protected alias Symmetric.forall_existsUnique_iff := Std.Symm.forall_existsUnique_iff

/--
Definition of `Set.piecewise` / `Set.piecewise` 的定义

English:
definition Set.piecewise
  signature: {α : Type u} {β : α -> Sort v} (s : Set α) (f g : forall i, β i)
  body: fun i => if i in s then f i else g i

中文:
定义 集合.piecewise
  签名: {α : 类型u} {β : α -> 类型层 v} (s : 集合 α) (f g : 对任意 i, β i)
  定义体: fun i => if i in s then f i else g i
-/
def Set.piecewise {α : Type u} {β : α -> Sort v} (s : Set α) (f g : forall i, β i)
    [forall j, Decidable (j in s)] : forall i, β i :=
  fun i => if i in s then f i else g i



/--
theorem `eq_rec_on_bijective` / 定理 `eq_rec_on_bijective`

English:
theorem eq_rec_on_bijective
  given: {C : α -> Sort*}

中文:
定理 eq_rec_on_bijective
  条件: {C : α -> 类型层*}
-/
theorem eq_rec_on_bijective {C : α -> Sort*} :
    forall {a a' : α} (h : a = a'), Function.Bijective (@Eq.ndrec _ _ C · _ h)
  | _, _, rfl => ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

/--
theorem `eq_mp_bijective` / 定理 `eq_mp_bijective`

English:
theorem eq_mp_bijective
  given: {α β : Sort _} (h : α = β)
  statement: Function.Bijective (Eq.mp h)
  proof: by
  -- TODO: mathlib3 uses `eq_rec_on_bijective`, difference in elaboration here
  -- due to `@[macro_inline]` possibly?
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

中文:
定理 eq_mp_bijective
  条件: {α β : 类型层 _} (h : α = β)
  结论: 函数.双射 (相等.mp h)
  证明: by
  -- TODO: mathlib3 uses `eq_rec_on_bijective`, difference in elaboration here
  -- due to `@[macro_inline]` possibly?
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩
-/
theorem eq_mp_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mp h) := by
  -- TODO: mathlib3 uses `eq_rec_on_bijective`, difference in elaboration here
  -- due to `@[macro_inline]` possibly?
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

/--
theorem `eq_mpr_bijective` / 定理 `eq_mpr_bijective`

English:
theorem eq_mpr_bijective
  given: {α β : Sort _} (h : α = β)
  statement: Function.Bijective (Eq.mpr h)
  proof: by
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

中文:
定理 eq_mpr_bijective
  条件: {α β : 类型层 _} (h : α = β)
  结论: 函数.双射 (相等.mpr h)
  证明: by
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩
-/
theorem eq_mpr_bijective {α β : Sort _} (h : α = β) : Function.Bijective (Eq.mpr h) := by
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

/--
theorem `cast_bijective` / 定理 `cast_bijective`

English:
theorem cast_bijective
  given: {α β : Sort _} (h : α = β)
  statement: Function.Bijective (cast h)
  proof: by
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

中文:
定理 cast_bijective
  条件: {α β : 类型层 _} (h : α = β)
  结论: 函数.双射 (cast h)
  证明: by
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩
-/
theorem cast_bijective {α β : Sort _} (h : α = β) : Function.Bijective (cast h) := by
  cases h
  exact ⟨fun _ _ => id, fun x => ⟨x, rfl⟩⟩

/-! Note these lemmas apply to `Type*` not `Sort*`, as the latter interferes with `simp`, and
is trivial anyway. -/

@[simp]
/--
theorem `eq_rec_inj` / 定理 `eq_rec_inj`

English:
theorem eq_rec_inj
  given: {a a' : α} (h : a = a') {C : α -> Type*} (x y : C a)
  proof: (eq_rec_on_bijective h).injective.eq_iff

@[simp]

中文:
定理 eq_rec_inj
  条件: {a a' : α} (h : a = a') {C : α -> 类型} (x y : C a)
  证明: (eq_rec_on_bijective h).injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, eq_rec_on_bijective, injective, injective.eq_iff
-/
theorem eq_rec_inj {a a' : α} (h : a = a') {C : α -> Type*} (x y : C a) :
    (Eq.ndrec x h : C a') = Eq.ndrec y h ↔ x = y :=
  (eq_rec_on_bijective h).injective.eq_iff

@[simp]
/--
theorem `cast_inj` / 定理 `cast_inj`

English:
theorem cast_inj
  given: {α β : Type u} (h : α = β) {x y : α}
  statement: cast h x = cast h y ↔ x = y
  proof: (cast_bijective h).injective.eq_iff

中文:
定理 cast_inj
  条件: {α β : 类型u} (h : α = β) {x y : α}
  结论: cast h x = cast h y ↔ x = y
  证明: (cast_bijective h).injective.eq_iff

Depends on / 依赖: cast_bijective, eq_iff, injective, injective.eq_iff
-/
theorem cast_inj {α β : Type u} (h : α = β) {x y : α} : cast h x = cast h y ↔ x = y :=
  (cast_bijective h).injective.eq_iff

/--
theorem `Function.LeftInverse.eq_rec_eq` / 定理 `Function.LeftInverse.eq_rec_eq`

English:
theorem Function.LeftInverse.eq_rec_eq
  statement: {γ : β -> Sort v} {f : α -> β} {g : β -> α}
  proof: eq_of_heq (eqRec_heq _ _).trans by rw [h]

中文:
定理 函数.左逆.eq_rec_eq
  结论: {γ : β -> 类型层 v} {f : α -> β} {g : β -> α}
  证明: eq_of_heq (eqRec_heq _ _).trans by rw [h]

Depends on / 依赖: eqRec_heq, eq_of_heq
-/
theorem Function.LeftInverse.eq_rec_eq {γ : β -> Sort v} {f : α -> β} {g : β -> α}
    (h : Function.LeftInverse g f) (C : forall a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).rec (C (g (f a)))` for LHS
    @Eq.rec β (f (g (f a))) (fun x _ => γ x) (C (g (f a))) (f a) (congr_arg f (h a)) = C a :=
eq_of_heq (eqRec_heq _ _).trans by rw [h]

/--
theorem `Function.LeftInverse.eq_rec_on_eq` / 定理 `Function.LeftInverse.eq_rec_on_eq`

English:
theorem Function.LeftInverse.eq_rec_on_eq
  statement: {γ : β -> Sort v} {f : α -> β} {g : β -> α}
  proof: h.eq_rec_eq _ _

中文:
定理 函数.左逆.eq_rec_on_eq
  结论: {γ : β -> 类型层 v} {f : α -> β} {g : β -> α}
  证明: h.eq_rec_eq _ _

Depends on / 依赖: eq_rec_eq, h.eq_rec_eq
-/
theorem Function.LeftInverse.eq_rec_on_eq {γ : β -> Sort v} {f : α -> β} {g : β -> α}
    (h : Function.LeftInverse g f) (C : forall a : α, γ (f a)) (a : α) :
    -- TODO: mathlib3 uses `(congr_arg f (h a)).recOn (C (g (f a)))` for LHS
    @Eq.recOn β (f (g (f a))) (fun x _ => γ x) (f a) (congr_arg f (h a)) (C (g (f a))) = C a :=
  h.eq_rec_eq _ _

/--
theorem `Function.LeftInverse.cast_eq` / 定理 `Function.LeftInverse.cast_eq`

English:
theorem Function.LeftInverse.cast_eq
  statement: {γ : β -> Sort v} {f : α -> β} {g : β -> α}
  proof: by
  grind

中文:
定理 函数.左逆.cast_eq
  结论: {γ : β -> 类型层 v} {f : α -> β} {g : β -> α}
  证明: by
  grind
-/
theorem Function.LeftInverse.cast_eq {γ : β -> Sort v} {f : α -> β} {g : β -> α}
    (h : Function.LeftInverse g f) (C : forall a : α, γ (f a)) (a : α) :
    cast (congr_arg (fun a => γ (f a)) (h a)) (C (g (f a))) = C a := by
  grind

/--
Definition of `Set.SeparatesPoints` / `Set.SeparatesPoints` 的定义

English:
definition Set.SeparatesPoints
  signature: {α β : Type*} (A : Set (α -> β))
  body: forall ⦃x y : α⦄, x != y -> exists f in A, f x != f y

中文:
定义 集合.SeparatesPoints
  签名: {α β : 类型} (A : 集合 (α -> β))
  定义体: forall ⦃x y : α⦄, x != y -> exists f in A, f x != f y
-/
def Set.SeparatesPoints {α β : Type*} (A : Set (α -> β)) : Prop :=
  forall ⦃x y : α⦄, x != y -> exists f in A, f x != f y

/--
theorem `Set.separatesPoints_mono` / 定理 `Set.separatesPoints_mono`

English:
theorem Set.separatesPoints_mono
  statement: {α β : Type*} {A B : Set (α -> β)} (hAB : A subseteq B)
  proof: by
  intro x y hne
  obtain ⟨f, hfA, hne'⟩ := hA hne
  exact ⟨f, hAB hfA, hne'⟩

中文:
定理 集合.separatesPoints_mono
  结论: {α β : 类型} {A B : 集合 (α -> β)} (hAB : A subseteq B)
  证明: by
  intro x y hne
  obtain ⟨f, hfA, hne'⟩ := hA hne
  exact ⟨f, hAB hfA, hne'⟩
-/
theorem Set.separatesPoints_mono {α β : Type*} {A B : Set (α -> β)} (hAB : A subseteq B)
    (hA : Set.SeparatesPoints A) : Set.SeparatesPoints B := by
  intro x y hne
  obtain ⟨f, hfA, hne'⟩ := hA hne
  exact ⟨f, hAB hfA, hne'⟩

/--
theorem `InvImage.equivalence` / 定理 `InvImage.equivalence`

English:
theorem InvImage.equivalence
  statement: {α : Sort u} {β : Sort v} (r : β -> β -> Prop) (f : α -> β)
  proof: ⟨fun _ => h.1 _, h.symm, h.trans⟩

中文:
定理 InvImage.equivalence
  结论: {α : 类型层 u} {β : 类型层 v} (r : β -> β -> 命题) (f : α -> β)
  证明: ⟨fun _ => h.1 _, h.symm, h.trans⟩

Depends on / 依赖: h.symm, h.trans
-/
theorem InvImage.equivalence {α : Sort u} {β : Sort v} (r : β -> β -> Prop) (f : α -> β)
    (h : Equivalence r) : Equivalence (InvImage r f) :=
  ⟨fun _ => h.1 _, h.symm, h.trans⟩

instance {α β : Type*} {r : α -> β -> Prop} {x : α × β} [Decidable (r x.1 x.2)] :
    Decidable (uncurry r x) :=
  ‹Decidable _›

instance {α β : Type*} {r : α × β -> Prop} {a : α} {b : β} [Decidable (r (a, b))] :
    Decidable (curry r a b) :=
  ‹Decidable _›

namespace Pi

variable {ι : Type*}

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {α : ι -> Type*}
  statement: Pi.map (fun i => @id (α i)) = id
  proof: rfl

中文:
定理 map_id
  条件: {α : ι -> 类型}
  结论: 依赖函数类型.map (fun i => @id (α i)) = id
  证明: rfl
-/
@[simp] theorem map_id {α : ι -> Type*} : Pi.map (fun i => @id (α i)) = id := rfl

/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  given: {α : ι -> Type*}
  statement: Pi.map (fun i (a : α i) => a) = fun x => x
  proof: rfl

中文:
定理 map_id'
  条件: {α : ι -> 类型}
  结论: 依赖函数类型.map (fun i (a : α i) => a) = fun x => x
  证明: rfl
-/
@[simp] theorem map_id' {α : ι -> Type*} : Pi.map (fun i (a : α i) => a) = fun x => x := rfl

/--
theorem `map_comp_map` / 定理 `map_comp_map`

English:
theorem map_comp_map
  given: {α β γ : ι -> Type*} (f : forall i, α i -> β i) (g : forall i, β i -> γ i)
  proof: rfl

中文:
定理 map_comp_map
  条件: {α β γ : ι -> 类型} (f : 对任意 i, α i -> β i) (g : 对任意 i, β i -> γ i)
  证明: rfl
-/
theorem map_comp_map {α β γ : ι -> Type*} (f : forall i, α i -> β i) (g : forall i, β i -> γ i) :
    Pi.map g ∘ Pi.map f = Pi.map fun i => g i ∘ f i :=
  rfl

end Pi
