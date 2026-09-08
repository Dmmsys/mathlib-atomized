/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # The exponential map from selfadjoint to unitary
In this file, we establish various properties related to the map
`fun a ↦ NormedSpace.exp ℂ A (I • a)` between the subtypes `selfAdjoint A` and `unitary A`.

## TODO

* Show that any exponential unitary is path-connected in `unitary A` to `1 : unitary A`.
* Prove any unitary whose distance to `1 : unitary A` is less than `1` can be expressed as an
  exponential unitary.
* A unitary is in the path component of `1` if and only if it is a finite product of exponential
  unitaries.
-/

@[expose] public section

open NormedSpace -- For `NormedSpace.exp`.

section Star

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

open Complex

/-- The map from the selfadjoint real subspace to the unitary group. This map only makes sense
over ℂ. -/
@[simps]
/-
**selfAdjoint.expUnitary** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A
参数：a : selfAdjoint A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the selfadjoint real subspace to the unitary group. This map only m
akes sense
over ℂ.
-/
noncomputable def selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A :=
  ⟨exp ((I • a.val) : A),
      let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
      exp_mem_unitary_of_mem_skewAdjoint (a.prop.smul_mem_skewAdjoint conj_I)⟩

open selfAdjoint

@[simp]
/-
**selfAdjoint.expUnitary_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `selfAdjoint.expUnitary_coe`：∀ {A : Type u_1} [inst : NormedRing A] [inst
_1 : NormedAlgebra ℂ A] [inst_2 : StarRing A] [inst_3 : ContinuousStar A]   [ins
t_4 : CompleteSp…
· 使用定理 `NormedSpace.exp.congr_simp`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : T
opologicalSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x x_1 : 𝔸),   x = x_1 → Norme
dSpace.exp x = N…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `NormedSpace.exp_zero`：exp_zero : exp (0 : 𝔸) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1 := by
  ext
  simp

@[fun_prop]
/-
**selfAdjoint.continuous_expUnitary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：selfAdjoint.continuous_expUnitary : Continuous (expUnitary : selfAdjoint A
 -> unitary A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `selfAdjoint.expUnitary_coe`：∀ {A : Type u_1} [inst : NormedRing A] [inst
_1 : NormedAlgebra ℂ A] [inst_2 : StarRing A] [inst_3 : ContinuousStar A]   [ins
t_4 : CompleteSp…
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `NormedSpace.exp_continuous`：exp_continuous : Continuous (exp : 𝔸 -> 𝔸)
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
lemma selfAdjoint.continuous_expUnitary : Continuous (expUnitary : selfAdjoint A → unitary A) := by
  simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
  let +nondep : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  fun_prop
/-
**Commute.expUnitary_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A))
 : expUnitary (a + b) = expUnitary a * expUnitary b
参数：h : Commute (a : A) (b : A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `selfAdjoint.expUnitary_coe`：∀ {A : Type u_1} [inst : NormedRing A] [inst
_1 : NormedAlgebra ℂ A] [inst_2 : StarRing A] [inst_3 : ContinuousStar A]   [ins
t_4 : CompleteSp…
· 使用定理 `NormedSpace.exp.congr_simp`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : T
opologicalSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x x_1 : 𝔸),   x = x_1 → Norme
dSpace.exp x = N…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `NormedSpace.exp_add_of_commute`：exp_add_of_commute {x y : 𝔸} (hxy : Comm
ute x y) : exp (x + y) = exp x * exp y
· 使用引理 `Commute.smul_right`：Commute.smul_right [Mul α] [SMulCommClass M α α] [Is
ScalarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute a (r • b)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
-/
theorem Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    expUnitary (a + b) = expUnitary a * expUnitary b := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  simpa only [Subtype.ext_iff, expUnitary_coe, AddSubgroup.coe_add, smul_add] using!
    exp_add_of_commute ((h.smul_left I).smul_right I)
/-
**Commute.expUnitary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.expUnitary {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) : C
ommute (expUnitary a) (expUnitary b)
参数：h : Commute (a : A) (b : A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq_1`：∀ {S : Type u_3} [inst : Mul S] (a b : S), Commute a b = S
emiconjBy a b b
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.expUnitary_add`：Commute.expUnitary_add {a b : selfAdjoint A} (h 
: Commute (a : A) (b : A)) : expUnitary (a + b) = expUnitary a * expUnitary b
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem Commute.expUnitary {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    Commute (expUnitary a) (expUnitary b) := by
  rw [Commute, SemiconjBy, ← h.expUnitary_add, ← h.symm.expUnitary_add, add_comm]

end Star

