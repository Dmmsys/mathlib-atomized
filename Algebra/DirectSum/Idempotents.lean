/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Andrew Yang
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Decomposition of the identity of a semiring into orthogonal idempotents

In this file we show that if a semiring `R` can be decomposed into a direct sum
of (left) ideals `R = V₁ ⊕ V₂ ⊕ ⋯ ⊕ Vₙ` then in the corresponding decomposition
`1 = e₁ + e₂ + ⋯ + eₙ` with `eᵢ ∈ Vᵢ`, each `eᵢ` is an idempotent and the
`eᵢ`'s form a family of complete orthogonal idempotents.
-/

@[expose] public section

namespace DirectSum

section OrthogonalIdempotents

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

/-- The decomposition of `(1 : R)` where `1 = e₁ + e₂ + ⋯ + eₙ` which is induced by
  the decomposition of the semiring `R = V1 ⊕ V2 ⊕ ⋯ ⊕ Vn`. -/
/-
**DirectSum.idempotent** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：idempotent (i : I) : R
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The decomposition of `(1 : R)` where `1 = e₁ + e₂ + ⋯ + eₙ` which is induced by
  the decomposition of the semiring `R = V1 ⊕ V2 ⊕ ⋯ ⊕ Vn`.
-/
def idempotent (i : I) : R :=
  decompose V 1 i
/-
**DirectSum.decompose_eq_mul_idempotent** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decompose_eq_mul_idempotent (x : R) (i : I) : decompose V x i = x * idempo
tent V i
参数：x : R；i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `DirectSum.idempotent.eq_1`：∀ {R : Type u_1} {I : Type u_2} [inst : Semir
ing R] [inst_1 : DecidableEq I] (V : I → Ideal R)   [inst_2 : DirectSum.Decompos
ition V] (i : I…
· 使用定理 `Submodule.coe_smul`：coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (
x : M)
· 使用定理 `DirectSum.smul_apply`：smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v
) i = b • v i
· 使用定理 `DirectSum.decompose_smul`：decompose_smul (r : R) (x : M) : decompose ℳ (
r • x) = r • decompose ℳ x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma decompose_eq_mul_idempotent (x : R) (i : I) : decompose V x i = x * idempotent V i := by
  rw [← smul_eq_mul (a := x), idempotent, ← Submodule.coe_smul, ← smul_apply, ← decompose_smul,
    smul_eq_mul, mul_one]
/-
**DirectSum.isIdempotentElem_idempotent** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：isIdempotentElem_idempotent (i : I) : IsIdempotentElem (idempotent V i : R
)
参数：i : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirectSum.decompose_eq_mul_idempotent`：decompose_eq_mul_idempotent (x : 
R) (i : I) : decompose V x i = x * idempotent V i
· 使用定理 `DirectSum.idempotent.eq_1`：∀ {R : Type u_1} {I : Type u_2} [inst : Semir
ing R] [inst_1 : DecidableEq I] (V : I → Ideal R)   [inst_2 : DirectSum.Decompos
ition V] (i : I…
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
-/
lemma isIdempotentElem_idempotent (i : I) : IsIdempotentElem (idempotent V i : R) := by
  rw [IsIdempotentElem, ← decompose_eq_mul_idempotent, idempotent, decompose_coe, of_eq_same]

/-- If a semiring can be decomposed into direct sum of finite left ideals `Vᵢ`
  where `1 = e₁ + ... + eₙ` and `eᵢ ∈ Vᵢ`, then `eᵢ` is a family of complete
  orthogonal idempotents. -/
/-
**DirectSum.completeOrthogonalIdempotents_idempotent** 是 Mathlib 中的一个定理，位于命名空间 `
DirectSum`。
形式化陈述：completeOrthogonalIdempotents_idempotent [Fintype I] : CompleteOrthogonalI
dempotents (idempotent V) where idem
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirectSum.isIdempotentElem_idempotent`：isIdempotentElem_idempotent (i : 
I) : IsIdempotentElem (idempotent V i : R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirectSum.decompose_eq_mul_idempotent`：decompose_eq_mul_idempotent (x : 
R) (i : I) : decompose V x i = x * idempotent V i
· 使用定理 `DirectSum.idempotent.eq_1`：∀ {R : Type u_1} {I : Type u_2} [inst : Semir
ing R] [inst_1 : DecidableEq I] (V : I → Ideal R)   [inst_2 : DirectSum.Decompos
ition V] (i : I…
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Submodule.coe_zero`：coe_zero : ((0 : p) : M) = 0
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `DirectSum.decompose_sum`：decompose_sum {ι'} (s : Finset ι') (f : ι' -> M
) : decompose ℳ (∑ i in s, f i) = ∑ i in s, decompose ℳ (f i)
· 使用定理 `DFinsupp.finsetSum_apply`：finsetSum_apply {α} [forall i, AddCommMonoid (
β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι) : (∑ a in s, g a) i = ∑ a in s
, g a i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `DirectSum.of_apply`：of_apply {i : ι} (j : ι) (x : β i) : of β i x j = if
 h : i = j then Eq.recOn h x else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a semiring can be decomposed into direct sum of finite left ideals `Vᵢ`
  where `1 = e₁ + ... + eₙ` and `eᵢ ∈ Vᵢ`, then `eᵢ` is a family of complete
  orthogonal idempotents.
-/
theorem completeOrthogonalIdempotents_idempotent [Fintype I] :
    CompleteOrthogonalIdempotents (idempotent V) where
  idem := isIdempotentElem_idempotent V
  ortho i j hij := by
    simp only
    rw [← decompose_eq_mul_idempotent, idempotent, decompose_coe,
      of_eq_of_ne (h := hij.symm), Submodule.coe_zero]
  complete := by
    apply (decompose V).injective
    refine DFunLike.ext _ _ fun i ↦ ?_
    rw [decompose_sum, DFinsupp.finsetSum_apply]
    simp [idempotent, of_apply]

end OrthogonalIdempotents

end DirectSum

