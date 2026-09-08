/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite and free modules

We provide some instances for finite and free modules.

## Main results

* `Module.Free.ChooseBasisIndex.fintype` : If a free module is finite, then any basis is finite.
* `Module.Finite.of_basis` : A free module with a basis indexed by a `Fintype` is finite.
-/

public section

universe u v w

/-- If a free module is finite, then the arbitrary basis is finite. -/
/-
**Module.Free.ChooseBasisIndex.fintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Free.ChooseBasisIndex.fintype (R : Type u) (M : Type v) [Semiring R
] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M] : Fintype
 (Module.Free.ChooseBasisIndex R M)
参数：R : Type u；M : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a free module is finite, then the arbitrary basis is finite.
-/
noncomputable instance Module.Free.ChooseBasisIndex.fintype (R : Type u) (M : Type v)
    [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Fintype (Module.Free.ChooseBasisIndex R M) := by
  refine @Fintype.ofFinite _ ?_
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    rw [ChooseBasisIndex]
    infer_instance
  · exact Module.Finite.finite_basis (chooseBasis _ _)

/-- A free module with a basis indexed by a `Fintype` is finite. -/
/-
**Module.Finite.of_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Finite.of_basis {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Mod
ule R M] [_root_.Finite ι] (b : Basis ι R M) : Module.Finite R M
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A free module with a basis indexed by a `Fintype` is finite.
-/
theorem Module.Finite.of_basis {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [_root_.Finite ι] (b : Basis ι R M) : Module.Finite R M := by
  cases nonempty_fintype ι
  classical
    refine ⟨⟨Finset.univ.image b, ?_⟩⟩
    simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]
/-
**Module.Finite.matrix** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Finite.matrix {R ι₁ ι₂ M : Type*} [Semiring R] [AddCommMonoid M] [M
odule R M] [Module.Free R M] [Module.Finite R M] [_root_.Finite ι₁] [_root_.Fini
te ι₂] : Module.Finite R (Matrix ι₁ ι₂ M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance Module.Finite.matrix {R ι₁ ι₂ M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [_root_.Finite ι₁] [_root_.Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ M) := by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
  exact Module.Finite.of_basis <| (Free.chooseBasis _ _).matrix _ _
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {ι₁ ι₂ R : Type*} [Semiring R] [Finite ι₁] [Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) := inferInstance
