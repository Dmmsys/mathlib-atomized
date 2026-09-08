/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Bitraversable.Lemmas
public import Mathlib.Control.Traversable.Lemmas

/-!
# Bitraversable instances

This file provides `Bitraversable` instances for concrete bifunctors:
* `Prod`
* `Sum`
* `Functor.Const`
* `flip`
* `Function.bicompl`
* `Function.bicompr`

## References

* Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative
-/

@[expose] public section


universe u v w

variable {t : Type u → Type u → Type u} [Bitraversable t]

section

variable {F : Type u → Type u} [Applicative F]

/-- The bitraverse function for `α × β`. -/
/-
**Prod.bitraverse** 是 Mathlib 中的一个定义，位于命名空间 `Prod`。
形式化陈述：{F : Type u → Type u} →   [Applicative F] →     {α : Type u_1} → {α' : Typ
e u} → {β : Type u_2} → {β' : Type u} → (α → F α') → (β → F β') → α × β → F (α' 
× β')
参数：α → F α'；β → F β'；α' × β'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bitraverse function for `α × β`.
-/
def Prod.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : α × β → F (α' × β')
  | (x, y) => Prod.mk <$> f x <*> f' y
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bitraversable Prod where bitraverse := @Prod.bitraverse
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulBitraversable Prod := by
  constructor <;> intros <;> casesm _ × _ <;>
    simp [bitraverse, Prod.bitraverse, functor_norm] <;> rfl

open Functor

/-- The bitraverse function for `α ⊕ β`. -/
/-
**Sum.bitraverse** 是 Mathlib 中的一个定义，位于命名空间 `Sum`。
形式化陈述：{F : Type u → Type u} →   [Applicative F] →     {α : Type u_1} → {α' : Typ
e u} → {β : Type u_2} → {β' : Type u} → (α → F α') → (β → F β') → α ⊕ β → F (α' 
⊕ β')
参数：α → F α'；β → F β'；α' ⊕ β'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bitraverse function for `α ⊕ β`.
-/
def Sum.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : α ⊕ β → F (α' ⊕ β')
  | Sum.inl x => Sum.inl <$> f x
  | Sum.inr x => Sum.inr <$> f' x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bitraversable Sum where bitraverse := @Sum.bitraverse
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulBitraversable Sum := by
  constructor <;> intros <;> casesm _ ⊕ _ <;>
    simp [bitraverse, Sum.bitraverse, functor_norm] <;> rfl


set_option linter.unusedVariables false in
/-- The bitraverse function for `Const`. It throws away the second map. -/
@[nolint unusedArguments]
/-
**Const.bitraverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Const.bitraverse {F : Type u -> Type u} [Applicative F] {α α' β β'} (f : α
 -> F α') (f' : β -> F β') : Const α β -> F (Const α' β')
参数：f : α -> F α'；f' : β -> F β'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bitraverse function for `Const`. It throws away the second map.
-/
def Const.bitraverse {F : Type u → Type u} [Applicative F] {α α' β β'} (f : α → F α')
    (f' : β → F β') : Const α β → F (Const α' β') :=
  f
/-
**Bitraversable.const** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bitraversable.const : Bitraversable Const where bitraverse
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bitraversable.const : Bitraversable Const where bitraverse := @Const.bitraverse
/-
**LawfulBitraversable.const** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LawfulBitraversable.const : LawfulBitraversable Const
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LawfulBitraversable.const : LawfulBitraversable Const := by
  constructor <;> intros <;> simp [bitraverse, Const.bitraverse, functor_norm] <;> rfl

/-- The bitraverse function for `flip`. -/
nonrec def flip.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') :
    flip t α β → F (flip t α' β') :=
  (bitraverse f' f : t β α → F (t β' α'))

/-
**Bitraversable.flip** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bitraversable.flip : Bitraversable (flip t) where bitraverse
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Bitraversable.flip : Bitraversable (flip t) where bitraverse := @flip.bitraverse t _

open LawfulBitraversable
/-
**LawfulBitraversable.flip** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LawfulBitraversable.flip [LawfulBitraversable t] : LawfulBitraversable (fl
ip t)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulBitraversable.toLawfulBifunctor`：∀ {t : Type u → Type u → Type u} 
{inst : Bitraversable t} [self : LawfulBitraversable t], LawfulBifunctor t
-/
instance LawfulBitraversable.flip [LawfulBitraversable t] : LawfulBitraversable (flip t) := by
  constructor <;> intros <;> casesm LawfulBitraversable t <;> apply_assumption only [*]

open Bitraversable
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) Bitraversable.traversable {α} : Traversable (t α) where
  traverse := @tsnd t _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) Bitraversable.isLawfulTraversable [LawfulBitraversable t] {α} :
    LawfulTraversable (t α) := by
  constructor <;> intros <;>
    simp [traverse, comp_tsnd, functor_norm]
  · simp [tsnd_eq_snd_id, (· <$> ·)]
  · simp [tsnd, binaturality, Function.comp_def, functor_norm]

end

open Bifunctor Traversable LawfulTraversable LawfulBitraversable

open Function (bicompl bicompr)

section Bicompl

variable (F G : Type u → Type u) [Traversable F] [Traversable G]

/-- The bitraverse function for `bicompl`. -/
nonrec def Bicompl.bitraverse {m} [Applicative m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
    bicompl t F G α α' → m (bicompl t F G β β') :=
  (bitraverse (traverse f) (traverse f') : t (F α) (G α') → m _)

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bitraversable (bicompl t F G) where bitraverse := @Bicompl.bitraverse t _ F G _ _

set_option backward.isDefEq.respectTransparency false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LawfulTraversable F] [LawfulTraversable G] [LawfulBitraversable t] :
    LawfulBitraversable (bicompl t F G) := by
  constructor <;> intros <;>
    simp [bitraverse, Bicompl.bitraverse, bimap, traverse_id, bitraverse_id_id, comp_bitraverse,
      functor_norm]
  · simp [traverse_eq_map_id', bitraverse_eq_bimap_id]
  · dsimp only [bicompl]
    simp [binaturality, naturality_pf]

end Bicompl

section Bicompr

variable (F : Type u → Type u) [Traversable F]

/-- The bitraverse function for `bicompr`. -/
nonrec def Bicompr.bitraverse {m} [Applicative m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
    bicompr F t α α' → m (bicompr F t β β') :=
  (traverse (bitraverse f f') : F (t α α') → m _)

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bitraversable (bicompr F t) where bitraverse := @Bicompr.bitraverse t _ F _

set_option backward.isDefEq.respectTransparency false in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LawfulTraversable F] [LawfulBitraversable t] : LawfulBitraversable (bicompr F t) := by
  constructor <;> intros <;>
    simp [bitraverse, Bicompr.bitraverse, bitraverse_id_id, functor_norm]
  · simp only [bitraverse_eq_bimap_id', traverse_eq_map_id', Function.comp_apply]; rfl
  · dsimp only [bicompr]
    simp [naturality, binaturality']

end Bicompr

