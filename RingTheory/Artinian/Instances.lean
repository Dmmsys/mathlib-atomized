/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Divisibility.Prod
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.RingTheory.Artinian.Module

/-!
# Instances related to Artinian rings

We show that every reduced Artinian ring and the polynomial ring over it
are decomposition monoids, and every reduced Artinian ring is semisimple.
-/

public section

/-- If each `Rⁿ` is a Artinian `R`-module, then `R` satisfies the strong rank condition.
Not an instance for performance reasons. -/
/-
**StrongRankCondition.of_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrongRankCondition.of_isArtinian (R) [Semiring R] [Nontrivial R] [forall 
n, IsArtinian R (Fin n -> R)] : StrongRankCondition R
参数：R；Fin n -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `strongRankCondition_iff_succ`：strongRankCondition_iff_succ : StrongRankC
ondition R ↔ forall (n : Nat) (f : (Fin (n + 1) -> R) ->ₗ[R] Fin n -> R), ¬Funct
ion.Injective f
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用引理 `IsArtinian.subsingleton_of_injective`：IsArtinian.subsingleton_of_injecti
ve [IsArtinian R N] {f : P × N ->ₗ[R] N} (inj : Function.Injective f) : Subsingl
eton P
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
If each `Rⁿ` is a Artinian `R`-module, then `R` satisfies the strong rank condit
ion.
Not an instance for performance reasons.
-/
theorem StrongRankCondition.of_isArtinian (R) [Semiring R] [Nontrivial R]
    [∀ n, IsArtinian R (Fin n → R)] : StrongRankCondition R :=
  (strongRankCondition_iff_succ R).2 fun n f hf ↦
    have e := LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
    not_subsingleton R <| IsArtinian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

namespace IsArtinianRing

variable (R : Type*) [CommRing R] [IsArtinianRing R] [IsReduced R]

attribute [local instance] fieldOfSubtypeIsMaximal

/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecompositionMonoid R := MulEquiv.decompositionMonoid (equivPi R)
/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecompositionMonoid (Polynomial R) :=
  MulEquiv.decompositionMonoid <|
    (Polynomial.mapEquiv <| (equivPi R).toRingEquiv).trans (Polynomial.piEquiv _)

end IsArtinianRing

