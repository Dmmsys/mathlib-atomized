/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-! # Short Exact Sequences in Abelian Categories

This file contains lemmas about short exact sequences in abelian categories.

-/

public section

namespace CategoryTheory.ShortExact

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits Preadditive CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F] [F.Faithful]
variable {S : ShortComplex C}

/-
**CategoryTheory.ShortExact.reflects_shortExact_of_faithful** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortExact`。
形式化陈述：reflects_shortExact_of_faithful (hS : (S.map F).ShortExact) : S.ShortExact
 where exact
参数：hS : (S.map F).ShortExact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.reflects_exact_of_faithful`：reflects_exact_of_fai
thful [F.Faithful] (S : ShortComplex C) (hS : (S.map F).Exact) : S.Exact
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Functor.ReflectsMonomorphisms.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.Functor.ReflectsEpimorphisms.reflects`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory
.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma reflects_shortExact_of_faithful (hS : (S.map F).ShortExact) : S.ShortExact where
  exact := F.reflects_exact_of_faithful _ hS.1
  mono_f := ReflectsMonomorphisms.reflects _ hS.mono_f
  epi_g := ReflectsEpimorphisms.reflects _ hS.epi_g
/-
**CategoryTheory.ShortExact.shortExact_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ShortExact`。
形式化陈述：shortExact_map_iff [PreservesFiniteColimits F] [PreservesFiniteLimits F] :
 (S.map F).ShortExact ↔ S.ShortExact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortExact.reflects_shortExact_of_faithful`：reflects_shor
tExact_of_faithful (hS : (S.map F).ShortExact) : S.ShortExact where exact
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map_of_exact`：∀ {C : Type u_1} {D
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_2, u_2} D] [inst_2 : Ca…
-/
lemma shortExact_map_iff [PreservesFiniteColimits F] [PreservesFiniteLimits F] :
    (S.map F).ShortExact ↔ S.ShortExact :=
  ⟨reflects_shortExact_of_faithful F, fun h ↦ ShortComplex.ShortExact.map_of_exact h F⟩

end CategoryTheory.ShortExact

