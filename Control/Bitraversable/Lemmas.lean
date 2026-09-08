/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Bitraversable.Basic

/-!
# Bitraversable Lemmas

## Main definitions
  * tfst - traverse on first functor argument
  * tsnd - traverse on second functor argument

## Lemmas

Combination of
  * bitraverse
  * tfst
  * tsnd

with the applicatives `id` and `comp`

## References

* Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative


-/

public section


universe u

variable {t : Type u → Type u → Type u} [Bitraversable t]
variable {β : Type u}

namespace Bitraversable

open Functor LawfulApplicative

variable {F G : Type u → Type u} [Applicative F] [Applicative G]

/-- traverse on the first functor argument -/
/-
**Bitraversable.tfst** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bitraversable`。
形式化陈述：tfst {α α'} (f : α -> F α') : t α β -> F (t α' β)
参数：f : α -> F α'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
traverse on the first functor argument
-/
abbrev tfst {α α'} (f : α → F α') : t α β → F (t α' β) :=
  bitraverse f pure

/-- traverse on the second functor argument -/
/-
**Bitraversable.tsnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `Bitraversable`。
形式化陈述：tsnd {α α'} (f : α -> F α') : t β α -> F (t β α')
参数：f : α -> F α'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
traverse on the second functor argument
-/
abbrev tsnd {α α'} (f : α → F α') : t β α → F (t β α') :=
  bitraverse pure f

variable [LawfulBitraversable t] [LawfulApplicative F] [LawfulApplicative G]

@[higher_order tfst_id]
/-
**Bitraversable.id_tfst** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：id_tfst : forall {α β} (x : t α β), tfst (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBitraversable.id_bitraverse`：∀ {t : Type u → Type u → Type u} {ins
t : Bitraversable t} [self : LawfulBitraversable t] {α β : Type u} (x : t α β), 
  bitraverse pure pure …
-/
theorem id_tfst : ∀ {α β} (x : t α β), tfst (F := Id) pure x = pure x :=
  id_bitraverse

@[higher_order tsnd_id]
/-
**Bitraversable.id_tsnd** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：id_tsnd : forall {α β} (x : t α β), tsnd (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBitraversable.id_bitraverse`：∀ {t : Type u → Type u → Type u} {ins
t : Bitraversable t} [self : LawfulBitraversable t] {α β : Type u} (x : t α β), 
  bitraverse pure pure …
-/
theorem id_tsnd : ∀ {α β} (x : t α β), tsnd (F := Id) pure x = pure x :=
  id_bitraverse

@[higher_order tfst_comp_tfst]
/-
**Bitraversable.comp_tfst** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：comp_tfst {α₀ α₁ α₂ β} (f : α₀ -> F α₁) (f' : α₁ -> G α₂) (x : t α₀ β) : C
omp.mk (tfst f' <$> tfst f x) = tfst (Comp.mk ∘ map f' ∘ f) x
参数：f : α₀ -> F α₁；f' : α₁ -> G α₂；x : t α₀ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulBitraversable.comp_bitraverse`：∀ {t : Type u → Type u → Type u} {i
nst : Bitraversable t} [self : LawfulBitraversable t] {F G : Type u → Type u}   
[inst_1 : Applicative F] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_tfst {α₀ α₁ α₂ β} (f : α₀ → F α₁) (f' : α₁ → G α₂) (x : t α₀ β) :
    Comp.mk (tfst f' <$> tfst f x) = tfst (Comp.mk ∘ map f' ∘ f) x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, tfst, map_pure, Pure.pure]

@[higher_order tfst_comp_tsnd]
/-
**Bitraversable.tfst_tsnd** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：tfst_tsnd {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀) :
 Comp.mk (tfst f <$> tsnd f' x) = bitraverse (Comp.mk ∘ pure ∘ f) (Comp.mk ∘ map
 pure ∘ f') x
参数：f : α₀ -> F α₁；f' : β₀ -> G β₁；x : t α₀ β₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulBitraversable.comp_bitraverse`：∀ {t : Type u → Type u → Type u} {i
nst : Bitraversable t} [self : LawfulBitraversable t] {F G : Type u → Type u}   
[inst_1 : Applicative F] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tfst_tsnd {α₀ α₁ β₀ β₁} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
    Comp.mk (tfst f <$> tsnd f' x)
      = bitraverse (Comp.mk ∘ pure ∘ f) (Comp.mk ∘ map pure ∘ f') x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tfst]
/-
**Bitraversable.tsnd_tfst** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：tsnd_tfst {α₀ α₁ β₀ β₁} (f : α₀ -> F α₁) (f' : β₀ -> G β₁) (x : t α₀ β₀) :
 Comp.mk (tsnd f' <$> tfst f x) = bitraverse (Comp.mk ∘ map pure ∘ f) (Comp.mk ∘
 pure ∘ f') x
参数：f : α₀ -> F α₁；f' : β₀ -> G β₁；x : t α₀ β₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulBitraversable.comp_bitraverse`：∀ {t : Type u → Type u → Type u} {i
nst : Bitraversable t} [self : LawfulBitraversable t] {F G : Type u → Type u}   
[inst_1 : Applicative F] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tsnd_tfst {α₀ α₁ β₀ β₁} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
    Comp.mk (tsnd f' <$> tfst f x)
      = bitraverse (Comp.mk ∘ map pure ∘ f) (Comp.mk ∘ pure ∘ f') x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]

@[higher_order tsnd_comp_tsnd]
/-
**Bitraversable.comp_tsnd** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：comp_tsnd {α β₀ β₁ β₂} (g : β₀ -> F β₁) (g' : β₁ -> G β₂) (x : t α β₀) : C
omp.mk (tsnd g' <$> tsnd g x) = tsnd (Comp.mk ∘ map g' ∘ g) x
参数：g : β₀ -> F β₁；g' : β₁ -> G β₂；x : t α β₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulBitraversable.comp_bitraverse`：∀ {t : Type u → Type u → Type u} {i
nst : Bitraversable t} [self : LawfulBitraversable t] {F G : Type u → Type u}   
[inst_1 : Applicative F] …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
-/
theorem comp_tsnd {α β₀ β₁ β₂} (g : β₀ → F β₁) (g' : β₁ → G β₂) (x : t α β₀) :
    Comp.mk (tsnd g' <$> tsnd g x) = tsnd (Comp.mk ∘ map g' ∘ g) x := by
  rw [← comp_bitraverse]
  simp only [Function.comp_def, map_pure]
  rfl

open Bifunctor Function

@[higher_order]
/-
**Bitraversable.tfst_eq_fst_id** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：tfst_eq_fst_id {α α' β} (f : α -> α') (x : t α β) : tfst (F
参数：f : α -> α'；x : t α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBitraversable.bitraverse_eq_bimap_id`：∀ {t : Type u → Type u → Typ
e u} {inst : Bitraversable t} [self : LawfulBitraversable t] {α α' β β' : Type u
}   (f : α → β) (f' : α' → β') (…
-/
theorem tfst_eq_fst_id {α α' β} (f : α → α') (x : t α β) :
    tfst (F := Id) (pure ∘ f) x = pure (fst f x) := by
  apply bitraverse_eq_bimap_id

@[higher_order]
/-
**Bitraversable.tsnd_eq_snd_id** 是 Mathlib 中的一个定理，位于命名空间 `Bitraversable`。
形式化陈述：tsnd_eq_snd_id {α β β'} (f : β -> β') (x : t α β) : tsnd (F
参数：f : β -> β'；x : t α β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBitraversable.bitraverse_eq_bimap_id`：∀ {t : Type u → Type u → Typ
e u} {inst : Bitraversable t} [self : LawfulBitraversable t] {α α' β β' : Type u
}   (f : α → β) (f' : α' → β') (…
-/
theorem tsnd_eq_snd_id {α β β'} (f : β → β') (x : t α β) :
    tsnd (F := Id) (pure ∘ f) x = pure (snd f x) := by
  apply bitraverse_eq_bimap_id

attribute [functor_norm] comp_bitraverse comp_tsnd comp_tfst tsnd_comp_tsnd tsnd_comp_tfst
  tfst_comp_tsnd tfst_comp_tfst bitraverse_comp bitraverse_id_id tfst_id tsnd_id

end Bitraversable

