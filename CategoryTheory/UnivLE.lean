/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.UnivLE

/-!
# Universe inequalities and essential surjectivity of `uliftFunctor`.

We show `UnivLE.{max u v, v} ↔ EssSurj (uliftFunctor.{u, v} : Type v ⥤ Type max u v)`.
-/

@[expose] public section

open CategoryTheory

universe u v

noncomputable section

/-
**UnivLE.ofEssSurj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UnivLE.ofEssSurj (w : (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSur
j) : UnivLE.{max u v, v} where small α
参数：w : (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.EssSurj.mem_essImage`：∀ {C : Type u₁} {D : Type u
₂} {inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   (F : CategoryTheor…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem UnivLE.ofEssSurj (w : (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj) :
    UnivLE.{max u v, v} where
  small α := by
    obtain ⟨a', m⟩ := w.mem_essImage α
    obtain ⟨m'⟩ := m
    exact ⟨a', ⟨(Iso.toEquiv m').symm.trans Equiv.ulift⟩⟩
/-
**EssSurj.ofUnivLE** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EssSurj.ofUnivLE [UnivLE.{max u v, v}] : (uliftFunctor.{u, v} : Type v ⥤ T
ype max u v).EssSurj where mem_essImage α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance EssSurj.ofUnivLE [UnivLE.{max u v, v}] :
    (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj where
  mem_essImage α :=
    ⟨Shrink α, ⟨Equiv.toIso (Equiv.ulift.trans (equivShrink α).symm)⟩⟩
/-
**UnivLE_iff_essSurj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UnivLE_iff_essSurj : UnivLE.{max u v, v} ↔ (uliftFunctor.{u, v} : Type v ⥤
 Type max u v).EssSurj
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.ofEssSurj`：UnivLE.ofEssSurj (w : (uliftFunctor.{u, v} : Type v ⥤ 
Type max u v).EssSurj) : UnivLE.{max u v, v} where small α
-/
theorem UnivLE_iff_essSurj :
    UnivLE.{max u v, v} ↔ (uliftFunctor.{u, v} : Type v ⥤ Type max u v).EssSurj :=
  ⟨fun _ => inferInstance, fun w => UnivLE.ofEssSurj w⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UnivLE.{max u v, v}] : uliftFunctor.{u, v}.IsEquivalence where
/-
**UnivLE.witness** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UnivLE.witness [UnivLE.{max u v, v}] : Type u ⥤ Type v
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsEquivalenceUliftFunctorOfUnivLE`：∀ [UnivLE.{max u v, v}], Category
Theory.uliftFunctor.{u, v}.IsEquivalence
-/
def UnivLE.witness [UnivLE.{max u v, v}] : Type u ⥤ Type v :=
  uliftFunctor.{v, u} ⋙ (uliftFunctor.{u, v}).inv
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UnivLE.{max u v, v}] : UnivLE.witness.{u, v}.Faithful :=
  inferInstanceAs <| Functor.Faithful (_ ⋙ _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UnivLE.{max u v, v}] : UnivLE.witness.{u, v}.Full :=
  inferInstanceAs <| Functor.Full (_ ⋙ _)
