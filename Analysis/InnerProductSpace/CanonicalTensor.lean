/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canonical tensors in real inner product spaces

Given an `InnerProductSpace ℝ E`, this file defines two canonical tensors.

* `InnerProductSpace.canonicalContravariantTensor E : E ⊗[ℝ] E →ₗ[ℝ] ℝ`. This is the element
  corresponding to the inner product.

* If `E` is finite-dimensional, then `E ⊗[ℝ] E` is canonically isomorphic to its dual. Accordingly,
  there exists an element `InnerProductSpace.canonicalCovariantTensor E : E ⊗[ℝ] E` that
  corresponds to `InnerProductSpace.canonicalContravariantTensor E` under this identification.

The theorem `canonicalCovariantTensor_eq_sum` shows that
`InnerProductSpace.canonicalCovariantTensor E` can be computed from any orthonormal basis `v` as
`∑ i, (v i) ⊗ₜ[ℝ] (v i)`.
-/

@[expose] public section

open InnerProductSpace TensorProduct

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The canonical contravariant tensor corresponding to the inner product -/
/-
**InnerProductSpace.canonicalContravariantTensor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.canonicalContravariantTensor : E otimes[Real] E ->ₗ[Real
] Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical contravariant tensor corresponding to the inner product
-/
noncomputable def InnerProductSpace.canonicalContravariantTensor :
    E ⊗[ℝ] E →ₗ[ℝ] ℝ := lift (innerₗ E)

/--
The canonical covariant tensor corresponding to `InnerProductSpace.canonicalContravariantTensor`
under the identification of `E` with its dual.
-/
/-
**InnerProductSpace.canonicalCovariantTensor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.canonicalCovariantTensor [FiniteDimensional Real E] : E 
otimes[Real] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical covariant tensor corresponding to `InnerProductSpace.canonicalCont
ravariantTensor`
under the identification of `E` with its dual.
-/
noncomputable def InnerProductSpace.canonicalCovariantTensor [FiniteDimensional ℝ E] :
    E ⊗[ℝ] E := ∑ i, ((stdOrthonormalBasis ℝ E) i) ⊗ₜ[ℝ] ((stdOrthonormalBasis ℝ E) i)

/-- Representation of the canonical covariant tensor in terms of an orthonormal basis. -/
/-
**InnerProductSpace.canonicalCovariantTensor_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：InnerProductSpace.canonicalCovariantTensor_eq_sum [FiniteDimensional Real 
E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι Real E) : InnerProductSpace.c
anonicalCovariantTensor E = ∑ i, (v i) otimesₜ[Real] (v i)
参数：v : OrthonormalBasis ι Real E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `OrthonormalBasis.sum_inner_mul_inner`：∀ {ι : Type u_1} {𝕜 : Type u_3} [i
nst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Inner
ProductSpace 𝕜 E] [inst_3 …
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `TensorProduct.tmul_sum`：tmul_sum (m : M) {α : Type*} (s : Finset α) (n :
 α -> N) : (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a
· 使用定理 `TensorProduct.sum_tmul`：sum_tmul {α : Type*} (s : Finset α) (m : α -> M)
 (n : N) : (∑ a in s, m a) otimesₜ[R] n = ∑ a in s, m a otimesₜ[R] n
· 使用定理 `TensorProduct.smul_tmul_smul`：smul_tmul_smul (r s : R) (m : M) (n : N) :
 (r • m) otimesₜ[R] (s • n) = (r * s) • m otimesₜ[R] n
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `OrthonormalBasis.sum_repr'`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLi
ke 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 …

--- 原说明 ---
Representation of the canonical covariant tensor in terms of an orthonormal basi
s.
-/
theorem InnerProductSpace.canonicalCovariantTensor_eq_sum [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) :
    InnerProductSpace.canonicalCovariantTensor E = ∑ i, (v i) ⊗ₜ[ℝ] (v i) := by
  let w := stdOrthonormalBasis ℝ E
  calc ∑ m, w m ⊗ₜ[ℝ] w m
  _ = ∑ m, ∑ n, ⟪w m, w n⟫_ℝ • w m ⊗ₜ[ℝ] w n := by
    congr 1 with m
    rw [Fintype.sum_eq_single m _, orthonormal_iff_ite.1 w.orthonormal]
    · simp only [↓reduceIte, one_smul]
    simp only [orthonormal_iff_ite.1 w.orthonormal, ite_smul, one_smul, zero_smul,
      ite_eq_right_iff]
    tauto
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_ℝ * ⟪v i, w n⟫_ℝ) • w m ⊗ₜ[ℝ] w n := by
    simp_rw [OrthonormalBasis.sum_inner_mul_inner v]
  _ = ∑ m, ∑ n, (∑ i, ⟪w m, v i⟫_ℝ * ⟪w n, v i⟫_ℝ) • w m ⊗ₜ[ℝ] w n := by
    simp only [real_inner_comm (w _)]
  _ = ∑ i, (∑ m, ⟪w m, v i⟫_ℝ • w m) ⊗ₜ[ℝ] ∑ n, ⟪w n, v i⟫_ℝ • w n := by
    simp only [sum_tmul, tmul_sum, smul_tmul_smul, Finset.sum_comm (γ := ι), Finset.sum_smul]
    rw [Finset.sum_comm]
  _ = ∑ i, v i ⊗ₜ[ℝ] v i := by
    simp only [w.sum_repr' (v _)]
