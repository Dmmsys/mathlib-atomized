/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Gershgorin's circle theorem

This file gives the proof of Gershgorin's circle theorem `eigenvalue_mem_ball` on the eigenvalues
of matrices and some applications.

## Reference

* https://en.wikipedia.org/wiki/Gershgorin_circle_theorem
-/

public section

variable {K n : Type*} [NormedField K] [Fintype n] [DecidableEq n] {A : Matrix n n K}

/-- **Gershgorin's circle theorem**: for any eigenvalue `μ` of a square matrix `A`, there exists an
index `k` such that `μ` lies in the closed ball of center the diagonal term `A k k` and of
radius the sum of the norms `∑ j ≠ k, ‖A k j‖`. -/
/-
**eigenvalue_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eigenvalue_mem_ball {μ : K} (hμ : Module.End.HasEigenvalue (Matrix.toLin' 
A) μ) : exists k, μ in Metric.closedBall (A k k) (∑ j in Finset.univ.erase k, ‖A
 k j‖)
参数：hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Submodule.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton p
] : p = ⊥
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Module.End.HasEigenvalue.exists_hasEigenvector`：∀ {R : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]  
 {f : Module.End R M} {μ : R}, f.Has…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `mul_inv_le_iff₀`：mul_inv_le_iff₀ (hc : 0 < c) : b * c⁻¹ <= a ↔ b <= a * 
c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
（共 91 条，此处仅展示前 30 条）

--- 原说明 ---
**Gershgorin's circle theorem**: for any eigenvalue `μ` of a square matrix `A`, 
there exists an
index `k` such that `μ` lies in the closed ball of center the diagonal term `A k
 k` and of
radius the sum of the norms `∑ j ≠ k, ‖A k j‖`.
-/
theorem eigenvalue_mem_ball {μ : K} (hμ : Module.End.HasEigenvalue (Matrix.toLin' A) μ) :
    ∃ k, μ ∈ Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖) := by
  cases isEmpty_or_nonempty n
  · exfalso
    exact hμ Submodule.eq_bot_of_subsingleton
  · obtain ⟨v, h_eg, h_nz⟩ := hμ.exists_hasEigenvector
    obtain ⟨i, -, h_i⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => ‖v i‖)
    have h_nz : v i ≠ 0 := by
      contrapose h_nz
      ext j
      rw [Pi.zero_apply, ← norm_le_zero_iff]
      refine (h_i ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)).trans ?_
      exact norm_le_zero_iff.mpr h_nz
    have h_le : ∀ j, ‖v j * (v i)⁻¹‖ ≤ 1 := fun j => by
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.mpr h_nz), one_mul]
      exact h_i ▸ Finset.le_sup' (fun i => ‖v i‖) (Finset.mem_univ j)
    simp_rw [mem_closedBall_iff_norm']
    refine ⟨i, ?_⟩
    calc
      _ = ‖(A i i * v i - μ * v i) * (v i)⁻¹‖ := by congr; field
      _ = ‖(A i i * v i - ∑ j, A i j * v j) * (v i)⁻¹‖ := by
                rw [show μ * v i = ∑ x : n, A i x * v x by
                  rw [← dotProduct, ← Matrix.mulVec]
                  exact (congrFun (Module.End.mem_eigenspace_iff.mp h_eg) i).symm]
      _ = ‖(∑ j ∈ Finset.univ.erase i, A i j * v j) * (v i)⁻¹‖ := by
                rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), ← neg_sub, neg_mul, norm_neg]
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ * ‖v j * (v i)⁻¹‖ := by
                rw [Finset.sum_mul]
                exact (norm_sum_le _ _).trans (le_of_eq (by simp_rw [mul_assoc, norm_mul]))
      _ ≤ ∑ j ∈ Finset.univ.erase i, ‖A i j‖ :=
                (Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (norm_nonneg _) (h_le j))

/-- If `A` is a row strictly dominant diagonal matrix, then its determinant is nonzero. -/
/-
**det_ne_zero_of_sum_row_lt_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：det_ne_zero_of_sum_row_lt_diag (h : forall k, ∑ j in Finset.univ.erase k, 
‖A k j‖ < ‖A k k‖) : A.det != 0
参数：h : forall k, ∑ j in Finset.univ.erase k, ‖A k j‖ < ‖A k k‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eigenvalue_mem_ball`：eigenvalue_mem_ball {μ : K} (hμ : Module.End.HasEig
envalue (Matrix.toLin' A) μ) : exists k, μ in Metric.closedBall (A k k) (∑ j in 
Finset.un…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.End.hasEigenvalue_iff`：hasEigenvalue_iff {f : End R M} {μ : R} : 
f.HasEigenvalue μ ↔ f.eigenspace μ != ⊥
· 使用定理 `Module.End.eigenspace_zero`：eigenspace_zero (f : End R M) : f.eigenspace
 0 = LinearMap.ker f
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LinearMap.bot_lt_ker_of_det_eq_zero`：bot_lt_ker_of_det_eq_zero [IsDomain
 R] [Free R M] {f : M ->ₗ[R] M} (hf : f.det = 0) : ⊥ < ker f
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.det_toLin'`：det_toLin' (f : Matrix ι ι R) : LinearMap.det (Mat
rix.toLin' f) = Matrix.det f
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mem_closedBall_iff_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGrou
p E] {a b : E} {r : ℝ}, b ∈ Metric.closedBall a r ↔ ‖a - b‖ ≤ r

--- 原说明 ---
If `A` is a row strictly dominant diagonal matrix, then its determinant is nonze
ro.
-/
theorem det_ne_zero_of_sum_row_lt_diag (h : ∀ k, ∑ j ∈ Finset.univ.erase k, ‖A k j‖ < ‖A k k‖) :
    A.det ≠ 0 := by
  contrapose! h
  suffices ∃ k, 0 ∈ Metric.closedBall (A k k) (∑ j ∈ Finset.univ.erase k, ‖A k j‖) by
    exact this.imp (fun a h ↦ by rwa [mem_closedBall_iff_norm', sub_zero] at h)
  refine eigenvalue_mem_ball ?_
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_zero, ne_comm]
  exact ne_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero (by rwa [LinearMap.det_toLin']))

/-- If `A` is a column strictly dominant diagonal matrix, then its determinant is nonzero. -/
/-
**det_ne_zero_of_sum_col_lt_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：det_ne_zero_of_sum_col_lt_diag (h : forall k, ∑ i in Finset.univ.erase k, 
‖A i k‖ < ‖A k k‖) : A.det != 0
参数：h : forall k, ∑ i in Finset.univ.erase k, ‖A i k‖ < ‖A k k‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `det_ne_zero_of_sum_row_lt_diag`：det_ne_zero_of_sum_row_lt_diag (h : fora
ll k, ∑ j in Finset.univ.erase k, ‖A k j‖ < ‖A k k‖) : A.det != 0

--- 原说明 ---
If `A` is a column strictly dominant diagonal matrix, then its determinant is no
nzero.
-/
theorem det_ne_zero_of_sum_col_lt_diag (h : ∀ k, ∑ i ∈ Finset.univ.erase k, ‖A i k‖ < ‖A k k‖) :
    A.det ≠ 0 := by
  rw [← Matrix.det_transpose]
  exact det_ne_zero_of_sum_row_lt_diag (by simp_rw [Matrix.transpose_apply]; exact h)
