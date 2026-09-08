/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Morita equivalence

Two `R`-algebras `A` and `B` are Morita equivalent if the categories of modules over `A` and
`B` are `R`-linearly equivalent. In this file, we prove that Morita equivalence is an equivalence
relation and that isomorphic algebras are Morita equivalent.

## Main definitions

- `MoritaEquivalence R A B`: a structure containing an `R`-linear equivalence of categories between
  the module categories of `A` and `B`.
- `IsMoritaEquivalent R A B`: a predicate asserting that `R`-algebras `A` and `B` are Morita
  equivalent.

## TODO

- For any ring `R`, `R` and `Matₙ(R)` are Morita equivalent.
- Morita equivalence in terms of projective generators.
- Morita equivalence in terms of full idempotents.
- Morita equivalence in terms of existence of an invertible bimodule.
- If `R ≈ S`, then `R` is simple iff `S` is simple.

## References

* [Nathan Jacobson, *Basic Algebra II*][jacobson1989]

## Tags

Morita Equivalence, Category Theory, Noncommutative Ring, Module Theory

-/

@[expose] public section

universe u₀ u₁ u₂ u₃

open CategoryTheory

variable (R : Type u₀) [CommSemiring R]

open scoped ModuleCat.Algebra

/--
Let `A` and `B` be `R`-algebras. A Morita equivalence between `A` and `B` is an `R`-linear
equivalence between the categories of `A`-modules and `B`-modules.
-/
/-
**MoritaEquivalence** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：MoritaEquivalence (A : Type u₁) [Ring A] [Algebra R A] (B : Type u₂) [Ring
 B] [Algebra R B] where /-- The underlying equivalence of categories -/ eqv : Mo
duleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B linear : eqv.functor.Linear R
参数：A : Type u₁；B : Type u₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `A` and `B` be `R`-algebras. A Morita equivalence between `A` and `B` is an 
`R`-linear
equivalence between the categories of `A`-modules and `B`-modules.
-/
structure MoritaEquivalence
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] where
  /-- The underlying equivalence of categories -/
  eqv : ModuleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B
  linear : eqv.functor.Linear R := by infer_instance

namespace MoritaEquivalence

attribute [instance] MoritaEquivalence.linear

/-
**MoritaEquivalence.** 是 Mathlib 中的一个实例，位于命名空间 `MoritaEquivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) : e.eqv.functor.Additive :=
  e.eqv.functor.additive_of_preserves_binary_products

/--
For any `R`-algebra `A`, `A` is Morita equivalent to itself.
-/
/-
**MoritaEquivalence.refl** 是 Mathlib 中的一个定义，位于命名空间 `MoritaEquivalence`。
形式化陈述：refl (A : Type u₁) [Ring A] [Algebra R A] : MoritaEquivalence R A A where 
eqv
参数：A : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `R`-algebra `A`, `A` is Morita equivalent to itself.
-/
def refl (A : Type u₁) [Ring A] [Algebra R A] : MoritaEquivalence R A A where
  eqv := CategoryTheory.Equivalence.refl
  linear := Functor.instLinearId

/--
For any `R`-algebras `A` and `B`, if `A` is Morita equivalent to `B`, then `B` is Morita equivalent
to `A`.
-/
/-
**MoritaEquivalence.symm** 是 Mathlib 中的一个定义，位于命名空间 `MoritaEquivalence`。
形式化陈述：symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra 
R B] (e : MoritaEquivalence R A B) : MoritaEquivalence R B A where eqv
参数：e : MoritaEquivalence R A B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `R`-algebras `A` and `B`, if `A` is Morita equivalent to `B`, then `B` i
s Morita equivalent
to `A`.
-/
def symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) : MoritaEquivalence R B A where
  eqv := e.eqv.symm
  linear := e.eqv.inverseLinear R

-- TODO: We have restricted all the rings to the same universe here because of the complication
-- `max u₁ u₂`, `max u₂ u₃` vs `max u₁ u₃`. But once we proved the definition of Morita
-- equivalence is equivalent to the existence of a full idempotent element, we can remove this
-- restriction in the universe.
-- Or alternatively, @alreadydone has sketched an argument on how the universe restriction can be
-- removed via a categorical argument,
-- see [here](https://github.com/leanprover-community/mathlib4/pull/20640#discussion_r1912189931)
/--
For any `R`-algebras `A`, `B`, and `C`, if `A` is Morita equivalent to `B` and `B` is Morita
equivalent to `C`, then `A` is Morita equivalent to `C`.
-/
/-
**MoritaEquivalence.trans** 是 Mathlib 中的一个定义，位于命名空间 `MoritaEquivalence`。
形式化陈述：trans {A B C : Type u₁} [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Rin
g C] [Algebra R C] (e : MoritaEquivalence R A B) (e' : MoritaEquivalence R B C) 
: MoritaEquivalence R A C where eqv
参数：e : MoritaEquivalence R A B；e' : MoritaEquivalence R B C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `R`-algebras `A`, `B`, and `C`, if `A` is Morita equivalent to `B` and `
B` is Morita
equivalent to `C`, then `A` is Morita equivalent to `C`.
-/
def trans {A B C : Type u₁}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (e : MoritaEquivalence R A B) (e' : MoritaEquivalence R B C) :
    MoritaEquivalence R A C where
  eqv := e.eqv.trans e'.eqv
  linear := e.eqv.functor.instLinearComp e'.eqv.functor

variable {R} in
/--
Isomorphic `R`-algebras are Morita equivalent.
-/
/-
**MoritaEquivalence.ofAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MoritaEquivalence`。
形式化陈述：ofAlgEquiv {A : Type u₁} {B : Type u₂} [Ring A] [Algebra R A] [Ring B] [Al
gebra R B] (f : A ≃ₐ[R] B) : MoritaEquivalence R A B where eqv
参数：f : A ≃ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic `R`-algebras are Morita equivalent.
-/
noncomputable def ofAlgEquiv {A : Type u₁} {B : Type u₂}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] (f : A ≃ₐ[R] B) :
    MoritaEquivalence R A B where
  eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv
  linear := ModuleCat.Algebra.restrictScalarsEquivalenceOfRingEquiv_linear f.symm

end MoritaEquivalence

/--
Let `A` and `B` be `R`-algebras. We say that `A` and `B` are Morita equivalent if the categories of
`A`-modules and `B`-modules are equivalent as `R`-linear categories.
-/
/-
**IsMoritaEquivalent** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u₀) →   [inst : CommSemiring R] →     (A : Type u₁) → [inst_1 : 
Ring A] → [Algebra R A] → (B : Type u₂) → [inst_3 : Ring B] → [Algebra R B] → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `A` and `B` be `R`-algebras. We say that `A` and `B` are Morita equivalent i
f the categories of
`A`-modules and `B`-modules are equivalent as `R`-linear categories.
-/
structure IsMoritaEquivalent
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] : Prop where
  cond : Nonempty <| MoritaEquivalence R A B

namespace IsMoritaEquivalent

/-
**IsMoritaEquivalent.refl** 是 Mathlib 中的一个引理，位于命名空间 `IsMoritaEquivalent`。
形式化陈述：refl (A : Type u₁) [Ring A] [Algebra R A] : IsMoritaEquivalent R A A where
 cond
参数：A : Type u₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma refl (A : Type u₁) [Ring A] [Algebra R A] : IsMoritaEquivalent R A A where
  cond := ⟨.refl R A⟩
/-
**IsMoritaEquivalent.symm** 是 Mathlib 中的一个引理，位于命名空间 `IsMoritaEquivalent`。
形式化陈述：symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra 
R B] (h : IsMoritaEquivalent R A B) : IsMoritaEquivalent R B A where cond
参数：h : IsMoritaEquivalent R A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `IsMoritaEquivalent.cond`：∀ {R : Type u₀} [inst : CommSemiring R] {A : Ty
pe u₁} [inst_1 : Ring A] [inst_2 : Algebra R A] {B : Type u₂}   [inst_3 : Ring B
] [inst_4 : A…
-/
lemma symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (h : IsMoritaEquivalent R A B) : IsMoritaEquivalent R B A where
  cond := h.cond.map <| .symm R
/-
**IsMoritaEquivalent.trans** 是 Mathlib 中的一个引理，位于命名空间 `IsMoritaEquivalent`。
形式化陈述：trans {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra 
R B] [Algebra R C] (h : IsMoritaEquivalent R A B) (h' : IsMoritaEquivalent R B C
) : IsMoritaEquivalent R A C where cond
参数：h : IsMoritaEquivalent R A B；h' : IsMoritaEquivalent R B C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ
· 使用定理 `IsMoritaEquivalent.cond`：∀ {R : Type u₀} [inst : CommSemiring R] {A : Ty
pe u₁} [inst_1 : Ring A] [inst_2 : Algebra R A] {B : Type u₂}   [inst_3 : Ring B
] [inst_4 : A…
-/
lemma trans {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (h : IsMoritaEquivalent R A B) (h' : IsMoritaEquivalent R B C) :
    IsMoritaEquivalent R A C where
  cond := Nonempty.map2 (.trans R) h.cond h'.cond
/-
**IsMoritaEquivalent.of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `IsMoritaEquivalent`。
形式化陈述：of_algEquiv {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [A
lgebra R B] (f : A ≃ₐ[R] B) : IsMoritaEquivalent R A B where cond
参数：f : A ≃ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_algEquiv {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (f : A ≃ₐ[R] B) : IsMoritaEquivalent R A B where
  cond := ⟨.ofAlgEquiv f⟩

end IsMoritaEquivalent

