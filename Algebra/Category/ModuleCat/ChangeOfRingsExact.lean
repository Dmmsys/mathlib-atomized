/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!

# Exactness of functors for change of rings.

In this file we provide exactness of restrictScalars for general universe level using it preserves
short exact sequences.
Note : previously exactness of `ModuleCat.restrictScalars` is synthesized via being adjoint functor,
however this needs the universe level to be some `max u v`, where `u` is the universe level
of the ring.

-/

@[expose] public section

universe v u u'

variable {R : Type u} [CommRing R] {R' : Type u'} [CommRing R']

open CategoryTheory

section

variable (f : R →+* R')

/-
**ModuleCat.restrictScalars_map_exact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModuleCat.restrictScalars_map_exact (S : ShortComplex (ModuleCat.{v} R')) 
(h : S.Exact) : (S.map (ModuleCat.restrictScalars.{v} f)).Exact
参数：S : ShortComplex (ModuleCat.{v} R')；h : S.Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `ModuleCat.instAdditiveRestrictScalars`：∀ {R : Type u_1} {S : Type u_2} [
inst : Ring R] [inst_1 : Ring S] (f : R →+* S), (ModuleCat.restrictScalars f).Ad
ditive
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exac
t`：∀ {R : Type u} [inst : Ring R] (S : CategoryTheory.ShortComplex (ModuleCat R)
),   S.Exact ↔ Function.Exact ⇑(CategoryTheory.ConcreteCategory…
-/
lemma ModuleCat.restrictScalars_map_exact (S : ShortComplex (ModuleCat.{v} R')) (h : S.Exact) :
    (S.map (ModuleCat.restrictScalars.{v} f)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact this.1
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact this.2

end

