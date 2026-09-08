/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.Shrink

/-!
# Category of $R$-modules has enough injectives

We lift enough injectives of abelian groups to arbitrary $R$-modules by adjoint functors
`restrictScalars ⊣ coextendScalars`
-/

public section

open CategoryTheory

universe v u

variable (R : Type u) [Ring R]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EnoughInjectives (ModuleCat.{v} ℤ) :=
  EnoughInjectives.of_equivalence (forget₂ (ModuleCat ℤ) AddCommGrpCat)
/-
**ModuleCat.enoughInjectives** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EnoughInjectives.of_adjunction`：∀ {C : Type u₁} {D : Type
 u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `ModuleCat.instPreservesMonomorphismsRestrictScalars`：∀ {R : Type u₁} {S 
: Type u₂} [inst : Ring R] [inst_1 : Ring S] (f : R →+* S),   (ModuleCat.restric
tScalars f).PreservesMonomorphisms
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `ModuleCat.instFaithfulRestrictScalars`：∀ {R : Type u₁} {S : Type u₂} [in
st : Ring R] [inst_1 : Ring S] (f : R →+* S), (ModuleCat.restrictScalars f).Fait
hful
· 使用定理 `instEnoughInjectivesModuleCatInt`：CategoryTheory.EnoughInjectives (Modul
eCat ℤ)
-/
lemma ModuleCat.enoughInjectives : EnoughInjectives (ModuleCat.{max v u} R) :=
  EnoughInjectives.of_adjunction (ModuleCat.restrictCoextendScalarsAdj.{max v u} (algebraMap ℤ R))

open ModuleCat in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Small.{v} R] : EnoughInjectives (ModuleCat.{v} R) :=
  letI := enoughInjectives.{v} (Shrink.{v} R)
  EnoughInjectives.of_equivalence (restrictScalars (equivShrink R).symm.ringEquiv.toRingHom)
