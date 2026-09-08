/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrices as a normed space

In this file we provide the following non-instances for norms on matrices:

* The elementwise norm (with `open scoped Matrix.Norms.Elementwise`):

  * `Matrix.seminormedAddCommGroup`
  * `Matrix.normedAddCommGroup`
  * `Matrix.normedSpace`
  * `Matrix.isBoundedSMul`
  * `Matrix.normSMulClass`

* The Frobenius norm (with `open scoped Matrix.Norms.Frobenius`):

  * `Matrix.frobeniusSeminormedAddCommGroup`
  * `Matrix.frobeniusNormedAddCommGroup`
  * `Matrix.frobeniusNormedSpace`
  * `Matrix.frobeniusNormedRing`
  * `Matrix.frobeniusNormedAlgebra`
  * `Matrix.frobeniusIsBoundedSMul`
  * `Matrix.frobeniusNormSMulClass`

* The $L^\infty$ operator norm (with `open scoped Matrix.Norms.Operator`):

  * `Matrix.linftyOpSeminormedAddCommGroup`
  * `Matrix.linftyOpNormedAddCommGroup`
  * `Matrix.linftyOpNormedSpace`
  * `Matrix.linftyOpIsBoundedSMul`
  * `Matrix.linftyOpNormSMulClass`
  * `Matrix.linftyOpNonUnitalSemiNormedRing`
  * `Matrix.linftyOpSemiNormedRing`
  * `Matrix.linftyOpNonUnitalNormedRing`
  * `Matrix.linftyOpNormedRing`
  * `Matrix.linftyOpNormedAlgebra`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.

The norm induced by the identification of `Matrix m n 𝕜` with
`EuclideanSpace n 𝕜 →L[𝕜] EuclideanSpace m 𝕜` (i.e., the ℓ² operator norm) can be found in
`Mathlib/Analysis/CStarAlgebra/Matrix.lean` and `open scoped Matrix.Norms.L2Operator`.
It is separated to avoid extraneous imports in this file.
-/

@[expose] public section

noncomputable section

open WithLp
open scoped NNReal Matrix

namespace Matrix

variable {R l m n α β ι : Type*} [Fintype l] [Fintype m] [Fintype n] [Unique ι]

/-! ### The elementwise supremum norm -/


section LinfLinf

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible]
/-
**Matrix.seminormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_3} →   {n : Type u_4} →     {α : Type u_5} → [Fintype m] → [Fi
ntype n] → [SeminormedAddCommGroup α] → SeminormedAddCommGroup (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed group instance (using sup norm of sup norm) for matrices over a semin
ormed group. Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def seminormedAddCommGroup : SeminormedAddCommGroup (Matrix m n α) :=
  fast_instance% Pi.seminormedAddCommGroup

attribute [local instance] Matrix.seminormedAddCommGroup
/-
**Matrix.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_def (A : Matrix m n α) : ‖A‖ = ‖fun i j => A i j‖
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def (A : Matrix m n α) : ‖A‖ = ‖fun i j => A i j‖ := rfl

/-- The norm of a matrix is the sup of the sup of the nnnorm of the entries -/
/-
**Matrix.norm_eq_sup_sup_nnnorm** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：norm_eq_sup_sup_nnnorm (A : Matrix m n α) : ‖A‖ = Finset.sup Finset.univ f
un i => Finset.sup Finset.univ fun j => ‖A i j‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The norm of a matrix is the sup of the sup of the nnnorm of the entries
-/
lemma norm_eq_sup_sup_nnnorm (A : Matrix m n α) :
    ‖A‖ = Finset.sup Finset.univ fun i ↦ Finset.sup Finset.univ fun j ↦ ‖A i j‖₊ := by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]
/-
**Matrix.nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_def (A : Matrix m n α) : ‖A‖₊ = ‖fun i j => A i j‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_def (A : Matrix m n α) : ‖A‖₊ = ‖fun i j => A i j‖₊ := rfl
/-
**Matrix.norm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_le_iff {r : Real} (hr : 0 <= r) {A : Matrix m n α} : ‖A‖ <= r ↔ foral
l i j, ‖A i j‖ <= r
参数：hr : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : Matrix m n α} : ‖A‖ ≤ r ↔ ∀ i j, ‖A i j‖ ≤ r := by
  simp_rw [norm_def, pi_norm_le_iff_of_nonneg hr]
/-
**Matrix.nnnorm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_le_iff {r : Real>=0} {A : Matrix m n α} : ‖A‖₊ <= r ↔ forall i j, ‖
A i j‖₊ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nnnorm_le_iff {r : ℝ≥0} {A : Matrix m n α} : ‖A‖₊ ≤ r ↔ ∀ i j, ‖A i j‖₊ ≤ r := by
  simp_rw [nnnorm_def, pi_nnnorm_le_iff]
/-
**Matrix.norm_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_lt_iff {r : Real} (hr : 0 < r) {A : Matrix m n α} : ‖A‖ < r ↔ forall 
i j, ‖A i j‖ < r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pi_norm_lt_iff`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [
inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r : ℝ}, 0 < 
r → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem norm_lt_iff {r : ℝ} (hr : 0 < r) {A : Matrix m n α} : ‖A‖ < r ↔ ∀ i j, ‖A i j‖ < r := by
  simp_rw [norm_def, pi_norm_lt_iff hr]
/-
**Matrix.nnnorm_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_lt_iff {r : Real>=0} (hr : 0 < r) {A : Matrix m n α} : ‖A‖₊ < r ↔ f
orall i j, ‖A i j‖₊ < r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pi_nnnorm_lt_iff`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι]
 [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r : NNReal
}, 0 <…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nnnorm_lt_iff {r : ℝ≥0} (hr : 0 < r) {A : Matrix m n α} :
    ‖A‖₊ < r ↔ ∀ i j, ‖A i j‖₊ < r := by
  simp_rw [nnnorm_def, pi_nnnorm_lt_iff hr]
/-
**Matrix.norm_entry_le_entrywise_sup_norm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ‖A i
 j‖ <= ‖A‖
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_le_pi_norm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] 
[inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι), ‖f 
i‖ ≤ …
-/
theorem norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖ ≤ ‖A‖ :=
  (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
/-
**Matrix.nnnorm_entry_le_entrywise_sup_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：nnnorm_entry_le_entrywise_sup_nnnorm (A : Matrix m n α) {i : m} {j : n} : 
‖A i j‖₊ <= ‖A‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `nnnorm_le_pi_nnnorm`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype
 ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] (f : (i : ι) → G i)   (i : ι),
 ‖f i‖₊ ≤…
-/
theorem nnnorm_entry_le_entrywise_sup_nnnorm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖₊ ≤ ‖A‖₊ :=
  (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp]
/-
**Matrix.nnnorm_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖₊ = ‖a‖
₊) : ‖A.map f‖₊ = ‖A‖₊
参数：A : Matrix m n α；f : α -> β；hf : forall a, ‖f a‖₊ = ‖a‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by
  simp only [nnnorm_def, Pi.nnnorm_def, Matrix.map_apply, hf]

@[simp]
/-
**Matrix.norm_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a‖ = ‖a‖) :
 ‖A.map f‖ = ‖A‖
参数：A : Matrix m n α；f : α -> β；hf : forall a, ‖f a‖ = ‖a‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.nnnorm_map_eq`：nnnorm_map_eq (A : Matrix m n α) (f : α -> β) (hf 
: forall a, ‖f a‖₊ = ‖a‖₊) : ‖A.map f‖₊ = ‖A‖₊
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) : ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]
/-
**Matrix.nnnorm_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_comm`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : 
SemilatticeSup α] [inst_1 : OrderBot α] (s : Finset β)   (t : Finset γ) (f : β →
 γ → …
-/
theorem nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ :=
  Finset.sup_comm _ _ _

@[simp]
/-
**Matrix.norm_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.nnnorm_transpose`：nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖
A‖₊
-/
theorem norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_transpose A

@[simp]
/-
**Matrix.nnnorm_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n
 α) : ‖Aᴴ‖₊ = ‖A‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.nnnorm_map_eq`：nnnorm_map_eq (A : Matrix m n α) (f : α -> β) (hf 
: forall a, ‖f a‖₊ = ‖a‖₊) : ‖A.map f‖₊ = ‖A‖₊
· 使用定理 `nnnorm_star`：nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊
· 使用定理 `Matrix.nnnorm_transpose`：nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖
A‖₊
-/
theorem nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose

@[simp]
/-
**Matrix.norm_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α
) : ‖Aᴴ‖ = ‖A‖
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.nnnorm_conjTranspose`：nnnorm_conjTranspose [StarAddMonoid α] [Nor
medStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖₊ = ‖A‖₊
-/
theorem norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_conjTranspose A
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [StarAddMonoid α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α) :=
  ⟨(le_of_eq <| norm_conjTranspose ·)⟩

@[simp]
/-
**Matrix.nnnorm_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_replicateCol (v : m -> α) : ‖replicateCol ι v‖₊ = ‖v‖₊
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_replicateCol (v : m → α) : ‖replicateCol ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]
/-
**Matrix.norm_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_replicateCol (v : m -> α) : ‖replicateCol ι v‖ = ‖v‖
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.nnnorm_replicateCol`：nnnorm_replicateCol (v : m -> α) : ‖replicat
eCol ι v‖₊ = ‖v‖₊
-/
theorem norm_replicateCol (v : m → α) : ‖replicateCol ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_replicateCol v

@[simp]
/-
**Matrix.nnnorm_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_replicateRow (v : n -> α) : ‖replicateRow ι v‖₊ = ‖v‖₊
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_replicateRow (v : n → α) : ‖replicateRow ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]
/-
**Matrix.norm_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_replicateRow (v : n -> α) : ‖replicateRow ι v‖ = ‖v‖
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.nnnorm_replicateRow`：nnnorm_replicateRow (v : n -> α) : ‖replicat
eRow ι v‖₊ = ‖v‖₊
-/
theorem norm_replicateRow (v : n → α) : ‖replicateRow ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_replicateRow v

@[simp]
/-
**Matrix.nnnorm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：nnnorm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖₊ = ‖v‖₊
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem nnnorm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  simp_rw [nnnorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine le_antisymm (Finset.sup_le fun j hj => ?_) ?_
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
    · simp [hij]
  · refine Eq.trans_le ?_ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]

@[simp]
/-
**Matrix.norm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：norm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖ = ‖v‖
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.nnnorm_diagonal`：nnnorm_diagonal [DecidableEq n] (v : n -> α) : ‖
diagonal v‖₊ = ‖v‖₊
-/
theorem norm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_diagonal v

/-- Note this is safe as an instance as it carries no data. -/
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note this is safe as an instance as it carries no data.
-/
instance [Nonempty n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α) :=
  ⟨(norm_diagonal _).trans <| norm_one⟩

end SeminormedAddCommGroup

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible]
/-
**Matrix.normedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_3} →   {n : Type u_4} →     {α : Type u_5} → [Fintype m] → [Fi
ntype n] → [NormedAddCommGroup α] → NormedAddCommGroup (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed group instance (using sup norm of sup norm) for matrices over a normed gr
oup.  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def normedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  fast_instance% Pi.normedAddCommGroup

section NormedSpace

attribute [local instance] Matrix.seminormedAddCommGroup

/-- This applies to the sup norm of sup norm. -/
/-
**Matrix.isBoundedSMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} {m : Type u_3} {n : Type u_4} {α : Type u_5} [inst : Fint
ype m] [inst_1 : Fintype n]   [inst_2 : SeminormedRing R] [inst_3 : SeminormedAd
dCommGroup α] [inst_4 : _root_.Module R α] [IsBoundedSMul R α],   IsBoundedSMul 
R (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This applies to the sup norm of sup norm.
-/
protected theorem isBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [IsBoundedSMul R α] : IsBoundedSMul R (Matrix m n α) :=
  Pi.instIsBoundedSMul

/-- This applies to the sup norm of sup norm. -/
/-
**Matrix.normSMulClass** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} {m : Type u_3} {n : Type u_4} {α : Type u_5} [inst : Fint
ype m] [inst_1 : Fintype n]   [inst_2 : SeminormedRing R] [inst_3 : SeminormedAd
dCommGroup α] [inst_4 : _root_.Module R α] [NormSMulClass R α],   NormSMulClass 
R (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This applies to the sup norm of sup norm.
-/
protected theorem normSMulClass [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [NormSMulClass R α] : NormSMulClass R (Matrix m n α) :=
  Pi.instNormSMulClass

variable [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible]
/-
**Matrix.normedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{R : Type u_1} →   {m : Type u_3} →     {n : Type u_4} →       {α : Type u
_5} →         [inst : Fintype m] →           [inst_1 : Fintype n] →             
[inst_2 : NormedField R] →               [inst_3 : SeminormedAddCommGroup α] → [
NormedSpace R α] → NormedSpace R (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed space instance (using sup norm of sup norm) for matrices over a normed sp
ace.  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def normedSpace : NormedSpace R (Matrix m n α) :=
  fast_instance% Pi.normedSpace

namespace Norms.Elementwise

attribute [scoped instance]
  Matrix.seminormedAddCommGroup
  Matrix.normedAddCommGroup
  Matrix.normedSpace
  Matrix.isBoundedSMul
  Matrix.normSMulClass

end Norms.Elementwise

end NormedSpace

end LinfLinf

/-! ### The $L_\infty$ operator norm

This section defines the matrix norm $\|A\|_\infty = \operatorname{sup}_i (\sum_j \|A_{ij}\|)$.

Note that this is equivalent to the operator norm, considering $A$ as a linear map between two
$L^\infty$ spaces.
-/


section LinftyOp

/-- Seminormed group instance (using sup norm of L1 norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpSeminormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_3} →   {n : Type u_4} →     {α : Type u_5} → [Fintype m] → [Fi
ntype n] → [SeminormedAddCommGroup α] → SeminormedAddCommGroup (Matrix m n α)
参数：Matrix m n α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)

--- 原说明 ---
Seminormed group instance (using sup norm of L1 norm) for matrices over a semino
rmed group. Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def linftyOpSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  fast_instance%
  @Pi.seminormedAddCommGroup m _ _ (fun _ ↦ PiLp.seminormedAddCommGroupToPi 1 (fun _ : n ↦ α))

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpNormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{m : Type u_3} →   {n : Type u_4} →     {α : Type u_5} → [Fintype m] → [Fi
ntype n] → [NormedAddCommGroup α] → NormedAddCommGroup (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed group instance (using sup norm of L1 norm) for matrices over a normed rin
g.  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def linftyOpNormedAddCommGroup [NormedAddCommGroup α] :
    NormedAddCommGroup (Matrix m n α) :=
  fast_instance%
  @Pi.normedAddCommGroup m _ _ (fun _ ↦ PiLp.normedAddCommGroupToPi 1 (fun _ : n ↦ α))

/-- This applies to the sup norm of L1 norm. -/
@[local instance]
/-
**Matrix.linftyOpIsBoundedSMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} {m : Type u_3} {n : Type u_4} {α : Type u_5} [inst : Fint
ype m] [inst_1 : Fintype n]   [inst_2 : SeminormedRing R] [inst_3 : SeminormedAd
dCommGroup α] [inst_4 : _root_.Module R α] [IsBoundedSMul R α],   IsBoundedSMul 
R (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This applies to the sup norm of L1 norm.
-/
protected theorem linftyOpIsBoundedSMul
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [IsBoundedSMul R α] :
    IsBoundedSMul R (Matrix m n α) :=
  letI := PiLp.pseudoMetricSpaceToPi 1 (fun _ : n ↦ α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n ↦ α)
  inferInstanceAs (IsBoundedSMul R (m → n → α))

/-- This applies to the sup norm of L1 norm. -/
@[local instance]
/-
**Matrix.linftyOpNormSMulClass** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} {m : Type u_3} {n : Type u_4} {α : Type u_5} [inst : Fint
ype m] [inst_1 : Fintype n]   [inst_2 : SeminormedRing R] [inst_3 : SeminormedAd
dCommGroup α] [inst_4 : _root_.Module R α] [NormSMulClass R α],   NormSMulClass 
R (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This applies to the sup norm of L1 norm.
-/
protected theorem linftyOpNormSMulClass
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [NormSMulClass R α] :
    NormSMulClass R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n ↦ α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n ↦ α)
  inferInstanceAs (NormSMulClass R (m → n → α))

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpNormedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{R : Type u_1} →   {m : Type u_3} →     {n : Type u_4} →       {α : Type u
_5} →         [inst : Fintype m] →           [inst_1 : Fintype n] →             
[inst_2 : NormedField R] →               [inst_3 : SeminormedAddCommGroup α] → [
NormedSpace R α] → NormedSpace R (Matrix m n α)
参数：Matrix m n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed space instance (using sup norm of L1 norm) for matrices over a normed spa
ce.  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def linftyOpNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 1 (fun _ : n ↦ α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 1 (fun _ : n ↦ α)
  inferInstanceAs (NormedSpace R (m → n → α))

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α]

/-
**Matrix.linfty_opNorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNorm_def (A : Matrix m n α) : ‖A‖ = ((Finset.univ : Finset m).sup
 fun i : m => ∑ j : n, ‖A i j‖₊ : Real>=0)
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PiLp.nnnorm_eq_of_L1`：nnnorm_eq_of_L1 (x : PiLp 1 β) : ‖x‖₊ = ∑ i : ι, ‖
x i‖₊
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linfty_opNorm_def (A : Matrix m n α) :
    ‖A‖ = ((Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ : ℝ≥0) := by
  change ‖fun i => toLp 1 (A i)‖ = _
  simp [Pi.norm_def, PiLp.nnnorm_eq_of_L1]
/-
**Matrix.linfty_opNNNorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNNNorm_def (A : Matrix m n α) : ‖A‖₊ = (Finset.univ : Finset m).s
up fun i : m => ∑ j : n, ‖A i j‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Matrix.linfty_opNorm_def`：linfty_opNorm_def (A : Matrix m n α) : ‖A‖ = (
(Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ : Real>=0)
-/
theorem linfty_opNNNorm_def (A : Matrix m n α) :
    ‖A‖₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ :=
  Subtype.ext <| linfty_opNorm_def A

@[simp]
/-
**Matrix.linfty_opNNNorm_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNNNorm_replicateCol (v : m -> α) : ‖replicateCol ι v‖₊ = ‖v‖₊
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.linfty_opNNNorm_def`：linfty_opNNNorm_def (A : Matrix m n α) : ‖A‖
₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linfty_opNNNorm_replicateCol (v : m → α) : ‖replicateCol ι v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  simp

@[simp]
/-
**Matrix.linfty_opNorm_replicateCol** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNorm_replicateCol (v : m -> α) : ‖replicateCol ι v‖ = ‖v‖
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Matrix.linfty_opNNNorm_replicateCol`：linfty_opNNNorm_replicateCol (v : m
 -> α) : ‖replicateCol ι v‖₊ = ‖v‖₊
-/
theorem linfty_opNorm_replicateCol (v : m → α) : ‖replicateCol ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_replicateCol v

@[simp]
/-
**Matrix.linfty_opNNNorm_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNNNorm_replicateRow (v : n -> α) : ‖replicateRow ι v‖₊ = ∑ i, ‖v 
i‖₊
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.linfty_opNNNorm_def`：linfty_opNNNorm_def (A : Matrix m n α) : ‖A‖
₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linfty_opNNNorm_replicateRow (v : n → α) : ‖replicateRow ι v‖₊ = ∑ i, ‖v i‖₊ := by
  simp [linfty_opNNNorm_def]

@[simp]
/-
**Matrix.linfty_opNorm_replicateRow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNorm_replicateRow (v : n -> α) : ‖replicateRow ι v‖ = ∑ i, ‖v i‖
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.linfty_opNNNorm_replicateRow`：linfty_opNNNorm_replicateRow (v : n
 -> α) : ‖replicateRow ι v‖₊ = ∑ i, ‖v i‖₊
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem linfty_opNorm_replicateRow (v : n → α) : ‖replicateRow ι v‖ = ∑ i, ‖v i‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_replicateRow v).trans <| by simp [NNReal.coe_sum]

@[simp]
/-
**Matrix.linfty_opNNNorm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNNNorm_diagonal [DecidableEq m] (v : m -> α) : ‖diagonal v‖₊ = ‖v
‖₊
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.linfty_opNNNorm_def`：linfty_opNNNorm_def (A : Matrix m n α) : ‖A‖
₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Matrix.diagonal_apply_ne'`：diagonal_apply_ne' [Zero α] (d : n -> α) {i j
 : n} (h : j != i) : (diagonal d) i j = 0
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
-/
theorem linfty_opNNNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ i) fun j _hj hij => ?_).trans ?_
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
  · rw [diagonal_apply_eq]

@[simp]
/-
**Matrix.linfty_opNorm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNorm_diagonal [DecidableEq m] (v : m -> α) : ‖diagonal v‖ = ‖v‖
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Matrix.linfty_opNNNorm_diagonal`：linfty_opNNNorm_diagonal [DecidableEq m
] (v : m -> α) : ‖diagonal v‖₊ = ‖v‖₊
-/
theorem linfty_opNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_diagonal v

end SeminormedAddCommGroup

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

/-
**Matrix.linfty_opNNNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNNNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ <= ‖A
‖₊ * ‖B‖₊
参数：A : Matrix l m α；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.linfty_opNNNorm_def`：linfty_opNNNorm_def (A : Matrix m n α) : ‖A‖
₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊
· 使用定理 `Finset.sup_mono_fun`：sup_mono_fun {g : β -> α} (h : forall b in s, f b <
= g b) : s.sup f <= s.sup g
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `nnnorm_sum_le_of_le`：∀ {ι : Type u_3} {E : Type u_5} [inst : SeminormedA
ddCommGroup E] (s : Finset ι) {f : ι → E} {n : ι → NNReal},   (∀ b ∈ s, ‖f b‖₊ ≤
 n b) → ‖…
· 使用定理 `nnnorm_mul_le`：nnnorm_mul_le (a b : α) : ‖a * b‖₊ <= ‖a‖₊ * ‖b‖₊
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem linfty_opNNNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ := by
  simp_rw [linfty_opNNNorm_def, Matrix.mul_apply]
  calc
    (Finset.univ.sup fun i => ∑ k, ‖∑ j, A i j * B j k‖₊) ≤
        Finset.univ.sup fun i => ∑ k, ∑ j, ‖A i j‖₊ * ‖B j k‖₊ :=
      Finset.sup_mono_fun fun i _hi =>
        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => nnnorm_mul_le _ _
    _ = Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * ∑ k, ‖B j k‖₊ := by
      simp_rw [@Finset.sum_comm m, Finset.mul_sum]
    _ ≤ Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      refine Finset.sup_mono_fun fun i _hi => ?_
      gcongr with j hj
      exact Finset.le_sup (f := fun i ↦ ∑ k : n, ‖B i k‖₊) hj
    _ ≤ (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      simp_rw [← Finset.sum_mul, ← NNReal.finset_sup_mul]
      rfl
/-
**Matrix.linfty_opNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ <= ‖A‖ *
 ‖B‖
参数：A : Matrix l m α；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.linfty_opNNNorm_mul`：linfty_opNNNorm_mul (A : Matrix l m α) (B : 
Matrix m n α) : ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
-/
theorem linfty_opNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNNNorm_mul _ _
/-
**Matrix.linfty_opNNNorm_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNNNorm_mulVec (A : Matrix l m α) (v : m -> α) : ‖A *ᵥ v‖₊ <= ‖A‖₊
 * ‖v‖₊
参数：A : Matrix l m α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.linfty_opNNNorm_replicateCol`：linfty_opNNNorm_replicateCol (v : m
 -> α) : ‖replicateCol ι v‖₊ = ‖v‖₊
· 使用定理 `Matrix.linfty_opNNNorm_mul`：linfty_opNNNorm_mul (A : Matrix l m α) (B : 
Matrix m n α) : ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
-/
theorem linfty_opNNNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖₊ ≤ ‖A‖₊ * ‖v‖₊ := by
  rw [← linfty_opNNNorm_replicateCol (ι := Fin 1) (A *ᵥ v),
    ← linfty_opNNNorm_replicateCol v (ι := Fin 1)]
  exact linfty_opNNNorm_mul A (replicateCol (Fin 1) v)
/-
**Matrix.linfty_opNorm_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNorm_mulVec (A : Matrix l m α) (v : m -> α) : ‖A *ᵥ v‖ <= ‖A‖ * ‖
v‖
参数：A : Matrix l m α；v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.linfty_opNNNorm_mulVec`：linfty_opNNNorm_mulVec (A : Matrix l m α)
 (v : m -> α) : ‖A *ᵥ v‖₊ <= ‖A‖₊ * ‖v‖₊
-/
theorem linfty_opNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖ :=
  linfty_opNNNorm_mulVec _ _

end NonUnitalSeminormedRing

/-- Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices over a seminormed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpNonUnitalSemiNormedRing** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_4} → {α : Type u_5} → [Fintype n] → [NonUnitalSeminormedRing α
] → NonUnitalSeminormedRing (Matrix n n α)
参数：Matrix n n α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.linfty_opNorm_mul`：linfty_opNorm_mul (A : Matrix l m α) (B : Matr
ix m n α) : ‖A * B‖ <= ‖A‖ * ‖B‖

--- 原说明 ---
Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices ove
r a seminormed
non-unital ring. Not declared as an instance because there are several natural c
hoices for defining
the norm of a matrix.
-/
protected def linftyOpNonUnitalSemiNormedRing [NonUnitalSeminormedRing α] :
    NonUnitalSeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpSeminormedAddCommGroup, Matrix.instNonUnitalRing with
    norm_mul_le := linfty_opNorm_mul }

/-- The `L₁-L∞` norm preserves one on non-empty matrices. Note this is safe as an instance, as it
carries no data. -/
/-
**Matrix.linfty_opNormOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：linfty_opNormOneClass [SeminormedRing α] [NormOneClass α] [DecidableEq n] 
[Nonempty n] : NormOneClass (Matrix n n α) where norm_one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.linfty_opNorm_diagonal`：linfty_opNorm_diagonal [DecidableEq m] (v
 : m -> α) : ‖diagonal v‖ = ‖v‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1

--- 原说明 ---
The `L₁-L∞` norm preserves one on non-empty matrices. Note this is safe as an in
stance, as it
carries no data.
-/
instance linfty_opNormOneClass [SeminormedRing α] [NormOneClass α] [DecidableEq n] [Nonempty n] :
    NormOneClass (Matrix n n α) where norm_one := (linfty_opNorm_diagonal _).trans norm_one

/-- Seminormed ring instance (using sup norm of L1 norm) for matrices over a seminormed ring. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpSemiNormedRing** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_4} → {α : Type u_5} → [Fintype n] → [SeminormedRing α] → [Deci
dableEq n] → SeminormedRing (Matrix n n α)
参数：Matrix n n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Seminormed ring instance (using sup norm of L1 norm) for matrices over a seminor
med ring. Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def linftyOpSemiNormedRing [SeminormedRing α] [DecidableEq n] :
    SeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }

/-- Normed non-unital ring instance (using sup norm of L1 norm) for matrices over a normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpNonUnitalNormedRing** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_4} → {α : Type u_5} → [Fintype n] → [NonUnitalNormedRing α] → 
NonUnitalNormedRing (Matrix n n α)
参数：Matrix n n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed non-unital ring instance (using sup norm of L1 norm) for matrices over a 
normed
non-unital ring. Not declared as an instance because there are several natural c
hoices for defining
the norm of a matrix.
-/
protected def linftyOpNonUnitalNormedRing [NonUnitalNormedRing α] :
    NonUnitalNormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpNormedRing** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_4} → {α : Type u_5} → [Fintype n] → [NormedRing α] → [Decidabl
eEq n] → NormedRing (Matrix n n α)
参数：Matrix n n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring
.  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def linftyOpNormedRing [NormedRing α] [DecidableEq n] : NormedRing (Matrix n n α) :=
  { Matrix.linftyOpSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed algebra instance (using sup norm of L1 norm) for matrices over a normed algebra. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.linftyOpNormedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{R : Type u_1} →   {n : Type u_4} →     {α : Type u_5} →       [inst : Fin
type n] →         [inst_1 : NormedField R] →           [inst_2 : SeminormedRing 
α] → [NormedAlgebra R α] → [inst_4 : DecidableEq n] → NormedAlgebra R (Matrix n 
n α)
参数：Matrix n n α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed algebra instance (using sup norm of L1 norm) for matrices over a normed a
lgebra. Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
protected def linftyOpNormedAlgebra [NormedField R] [SeminormedRing α] [NormedAlgebra R α]
    [DecidableEq n] : NormedAlgebra R (Matrix n n α) :=
  { Matrix.linftyOpNormedSpace, Matrix.instAlgebra with }


section
variable [NormedDivisionRing α] [NormedAlgebra ℝ α]

/-- Auxiliary construction; an element of norm 1 such that `a * unitOf a = ‖a‖`. -/
/-
**Matrix.unitOf** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary construction; an element of norm 1 such that `a * unitOf a = ‖a‖`.
-/
private def unitOf (a : α) : α := by classical exact if a = 0 then 1 else ‖a‖ • a⁻¹
/-
**Matrix.norm_unitOf** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem norm_unitOf (a : α) : ‖unitOf a‖₊ = 1 := by
  rw [unitOf]
  split_ifs with h
  · simp
  · rw [← nnnorm_eq_zero] at h
    rw [nnnorm_smul, nnnorm_inv, nnnorm_norm, mul_inv_cancel₀ h]
/-
**Matrix.mul_unitOf** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_unitOf (a : α) : a * unitOf a = algebraMap _ _ (‖a‖₊ : ℝ) := by
  simp only [unitOf, coe_nnnorm]
  split_ifs with h
  · simp [h]
  · rw [mul_smul_comm, mul_inv_cancel₀ h, Algebra.algebraMap_eq_smul_one]

end

/-!
For a matrix over a field, the norm defined in this section agrees with the operator norm on
`ContinuousLinearMap`s between function types (which have the infinity norm).
-/
section
variable [NontriviallyNormedField α] [NormedAlgebra ℝ α]

/-
**Matrix.linfty_opNNNorm_eq_opNNNorm** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNNNorm_eq_opNNNorm (A : Matrix m n α) : ‖A‖₊ = ‖ContinuousLinearM
ap.mk (Matrix.mulVecLin A)‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNNNorm_eq_of_bounds`：opNNNorm_eq_of_bounds {φ : E 
->SL[σ₁₂] F} (M : Real>=0) (h_above : forall x, ‖φ x‖₊ <= M * ‖x‖₊) (h_below : f
orall N, (forall x, ‖φ x‖₊ <= N…
· 使用定理 `Matrix.linfty_opNNNorm_mulVec`：linfty_opNNNorm_mulVec (A : Matrix l m α)
 (v : m -> α) : ‖A *ᵥ v‖₊ <= ‖A‖₊ * ‖v‖₊
· 使用定理 `Matrix.linfty_opNNNorm_def`：linfty_opNNNorm_def (A : Matrix m n α) : ‖A‖
₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `_private.Mathlib.Analysis.Matrix.Normed.0.Matrix.norm_unitOf`：∀ {α : Typ
e u_5} [inst : NormedDivisionRing α] [inst_1 : NormedAlgebra ℝ α] (a : α), ‖Matr
ix.unitOf✝ a‖₊ = 1
· 使用定理 `Finset.sup_const`：sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s
.sup fun _ => c) = c
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NNReal.nnnorm_eq`：∀ (x : NNReal), ‖↑x‖₊ = x
· 使用定理 `nnnorm_algebraMap`：nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x
‖₊ * ‖(1 : 𝕜')‖₊
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `_private.Mathlib.Analysis.Matrix.Normed.0.Matrix.mul_unitOf`：∀ {α : Type
 u_5} [inst : NormedDivisionRing α] [inst_1 : NormedAlgebra ℝ α] (a : α),   a * 
Matrix.unitOf✝ a = (algebraMap ℝ α) ↑‖a‖₊
-/
lemma linfty_opNNNorm_eq_opNNNorm (A : Matrix m n α) :
    ‖A‖₊ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖₊ := by
  rw [ContinuousLinearMap.opNNNorm_eq_of_bounds _ (linfty_opNNNorm_mulVec _) fun N hN => ?_]
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  cases isEmpty_or_nonempty n
  · simp
  let x : n → α := fun j => unitOf (A i j)
  have hxn : ‖x‖₊ = 1 := by
    simp_rw [x, Pi.nnnorm_def, norm_unitOf, Finset.sup_const Finset.univ_nonempty]
  specialize hN x
  rw [hxn, mul_one, Pi.nnnorm_def, Finset.sup_le_iff] at hN
  replace hN := hN i (Finset.mem_univ _)
  dsimp [mulVec, dotProduct] at hN
  simp_rw [x, mul_unitOf, ← map_sum, nnnorm_algebraMap, ← NNReal.coe_sum, NNReal.nnnorm_eq,
    nnnorm_one, mul_one] at hN
  exact hN
/-
**Matrix.linfty_opNorm_eq_opNorm** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：linfty_opNorm_eq_opNorm (A : Matrix m n α) : ‖A‖ = ‖ContinuousLinearMap.mk
 (Matrix.mulVecLin A)‖
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Matrix.linfty_opNNNorm_eq_opNNNorm`：linfty_opNNNorm_eq_opNNNorm (A : Mat
rix m n α) : ‖A‖₊ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖₊
-/
lemma linfty_opNorm_eq_opNorm (A : Matrix m n α) :
    ‖A‖ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_eq_opNNNorm A)

variable [DecidableEq n]
/-
**Matrix.linfty_opNNNorm_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_3} {n : Type u_4} {α : Type u_5} [inst : Fintype m] [inst_1 
: Fintype n]   [inst_2 : NontriviallyNormedField α] [NormedAlgebra ℝ α] [inst_4 
: DecidableEq n] (f : (n → α) →L[α] m → α),   ‖LinearMap.toMatrix' ↑f‖₊ = ‖f‖₊
参数：f : (n → α) →L[α] m → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.linfty_opNNNorm_eq_opNNNorm`：linfty_opNNNorm_eq_opNNNorm (A : Mat
rix m n α) : ‖A‖₊ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖₊
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.toLin'_toMatrix'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n 
→ R) →ₗ[R] m …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.mk.congr_simp`：∀ {R : Type u_1} {S : Type u_2} [inst
 : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : To
pologicalSpace M] [inst…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma linfty_opNNNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖₊ = ‖f‖₊ := by
  rw [linfty_opNNNorm_eq_opNNNorm]
  simp only [← toLin'_apply', toLin'_toMatrix']
/-
**Matrix.linfty_opNorm_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {m : Type u_3} {n : Type u_4} {α : Type u_5} [inst : Fintype m] [inst_1 
: Fintype n]   [inst_2 : NontriviallyNormedField α] [NormedAlgebra ℝ α] [inst_4 
: DecidableEq n] (f : (n → α) →L[α] m → α),   ‖LinearMap.toMatrix' ↑f‖ = ‖f‖
参数：f : (n → α) →L[α] m → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Matrix.linfty_opNNNorm_toMatrix`：∀ {m : Type u_3} {n : Type u_4} {α : Ty
pe u_5} [inst : Fintype m] [inst_1 : Fintype n]   [inst_2 : NontriviallyNormedFi
eld α] [NormedAlgebra…
-/
@[simp] lemma linfty_opNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖ = ‖f‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_toMatrix f)

end

namespace Norms.Operator
attribute [scoped instance]
  Matrix.linftyOpSeminormedAddCommGroup
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpIsBoundedSMul
  Matrix.linftyOpNormSMulClass
  Matrix.linftyOpNonUnitalSemiNormedRing
  Matrix.linftyOpSemiNormedRing
  Matrix.linftyOpNonUnitalNormedRing
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
end Norms.Operator

end LinftyOp

/-! ### The Frobenius norm

This is defined as $\|A\| = \sqrt{\sum_{i,j} \|A_{ij}\|^2}$.
When the matrix is over the real or complex numbers, this norm is submultiplicative.
-/


section frobenius

open scoped Matrix

/-- Seminormed group instance (using the Frobenius norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.frobeniusSeminormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：frobeniusSeminormedAddCommGroup [SeminormedAddCommGroup α] : SeminormedAdd
CommGroup (Matrix m n α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Seminormed group instance (using the Frobenius norm) for matrices over a seminor
med group. Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
def frobeniusSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  fast_instance%
  @PiLp.seminormedAddCommGroupToPi 2 _ _ _ _ (fun _ ↦ PiLp.seminormedAddCommGroupToPi 2 _)

/-- Normed group instance (using the Frobenius norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.frobeniusNormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：frobeniusNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (M
atrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed group instance (using the Frobenius norm) for matrices over a normed grou
p.  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
def frobeniusNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  fast_instance% @PiLp.normedAddCommGroupToPi 2 _ _ _ _ (fun _ ↦ PiLp.normedAddCommGroupToPi 2 _)

/-- This applies to the Frobenius norm. -/
@[local instance]
/-
**Matrix.frobeniusIsBoundedSMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobeniusIsBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Modu
le R α] [IsBoundedSMul R α] : IsBoundedSMul R (Matrix m n α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PiLp.isBoundedSMulSeminormedAddCommGroupToPi`：isBoundedSMulSeminormedAdd
CommGroupToPi [forall i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRi
ng R] [forall i, Module R (α i)] […
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
This applies to the Frobenius norm.
-/
theorem frobeniusIsBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [IsBoundedSMul R α] :
    IsBoundedSMul R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n ↦ α)
  letI := PiLp.isBoundedSMulSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n ↦ α)
  PiLp.isBoundedSMulSeminormedAddCommGroupToPi 2 _

/-- This applies to the Frobenius norm. -/
@[local instance]
/-
**Matrix.frobeniusNormSMulClass** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobeniusNormSMulClass [SeminormedRing R] [SeminormedAddCommGroup α] [Modu
le R α] [NormSMulClass R α] : NormSMulClass R (Matrix m n α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PiLp.normSMulClassSeminormedAddCommGroupToPi`：normSMulClassSeminormedAdd
CommGroupToPi [forall i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRi
ng R] [forall i, Module R (α i)] […
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
This applies to the Frobenius norm.
-/
theorem frobeniusNormSMulClass [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [NormSMulClass R α] :
    NormSMulClass R (Matrix m n α) :=
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n ↦ α)
  letI := PiLp.normSMulClassSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n ↦ α)
  PiLp.normSMulClassSeminormedAddCommGroupToPi 2 _

/-- Normed space instance (using the Frobenius norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.frobeniusNormedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：frobeniusNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpa
ce R α] : NormedSpace R (Matrix m n α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed space instance (using the Frobenius norm) for matrices over a normed spac
e.  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
def frobeniusNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  fast_instance%
  letI := PiLp.seminormedAddCommGroupToPi 2 (fun _ : n ↦ α)
  letI := PiLp.normedSpaceSeminormedAddCommGroupToPi (R := R) 2 (fun _ : n ↦ α)
  PiLp.normedSpaceSeminormedAddCommGroupToPi 2 _

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/-
**Matrix.frobenius_nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_def (A : Matrix m n α) : ‖A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 
: Real)) ^ (1 / 2 : Real)
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PiLp.nnnorm_eq_of_L2`：nnnorm_eq_of_L2 (x : PiLp 2 β) : ‖x‖₊ = NNReal.sqr
t (∑ i : ι, ‖x i‖₊ ^ 2)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
· 使用定理 `NNReal.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real>=0) : sqrt x = x ^ (1 / (2 :
 Real))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NNReal.rpow_two`：rpow_two (x : Real>=0) : x ^ (2 : Real) = x ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobenius_nnnorm_def (A : Matrix m n α) :
    ‖A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  change ‖toLp 2 fun i => toLp 2 fun j => A i j‖₊ = _
  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two]
/-
**Matrix.frobenius_norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_def (A : Matrix m n α) : ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : Re
al)) ^ (1 / 2 : Real)
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_def`：frobenius_nnnorm_def (A : Matrix m n α) : ‖
A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : Real)) ^ (1 / 2 : Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `NNReal.rpow_ofNat`：rpow_ofNat (x : Real>=0) (n : Nat) [n.AtLeastTwo] : x
 ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n : Nat)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Real.rpow_ofNat`：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (o
fNat(n) : Real) = x ^ (ofNat(n) : Nat)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobenius_norm_def (A : Matrix m n α) :
    ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) (frobenius_nnnorm_def A)).trans <| by simp [NNReal.coe_sum]

@[simp]
/-
**Matrix.frobenius_nnnorm_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f
 a‖₊ = ‖a‖₊) : ‖A.map f‖₊ = ‖A‖₊
参数：A : Matrix m n α；f : α -> β；hf : forall a, ‖f a‖₊ = ‖a‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_def`：frobenius_nnnorm_def (A : Matrix m n α) : ‖
A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : Real)) ^ (1 / 2 : Real)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobenius_nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]

@[simp]
/-
**Matrix.frobenius_norm_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_map_eq (A : Matrix m n α) (f : α -> β) (hf : forall a, ‖f a
‖ = ‖a‖) : ‖A.map f‖ = ‖A‖
参数：A : Matrix m n α；f : α -> β；hf : forall a, ‖f a‖ = ‖a‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_map_eq`：frobenius_nnnorm_map_eq (A : Matrix m n 
α) (f : α -> β) (hf : forall a, ‖f a‖₊ = ‖a‖₊) : ‖A.map f‖₊ = ‖A‖₊
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem frobenius_norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) :
    ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]
/-
**Matrix.frobenius_nnnorm_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_def`：frobenius_nnnorm_def (A : Matrix m n α) : ‖
A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : Real)) ^ (1 / 2 : Real)
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobenius_nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ := by
  rw [frobenius_nnnorm_def, frobenius_nnnorm_def, Finset.sum_comm]
  simp_rw [Matrix.transpose_apply]

@[simp]
/-
**Matrix.frobenius_norm_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_transpose`：frobenius_nnnorm_transpose (A : Matri
x m n α) : ‖Aᵀ‖₊ = ‖A‖₊
-/
theorem frobenius_norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_transpose A

@[simp]
/-
**Matrix.frobenius_nnnorm_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : 
Matrix m n α) : ‖Aᴴ‖₊ = ‖A‖₊
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.frobenius_nnnorm_map_eq`：frobenius_nnnorm_map_eq (A : Matrix m n 
α) (f : α -> β) (hf : forall a, ‖f a‖₊ = ‖a‖₊) : ‖A.map f‖₊ = ‖A‖₊
· 使用定理 `nnnorm_star`：nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊
· 使用定理 `Matrix.frobenius_nnnorm_transpose`：frobenius_nnnorm_transpose (A : Matri
x m n α) : ‖Aᵀ‖₊ = ‖A‖₊
-/
theorem frobenius_nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose

@[simp]
/-
**Matrix.frobenius_norm_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Ma
trix m n α) : ‖Aᴴ‖ = ‖A‖
参数：A : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_conjTranspose`：frobenius_nnnorm_conjTranspose [S
tarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖₊ = ‖A‖₊
-/
theorem frobenius_norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_conjTranspose A
/-
**Matrix.frobenius_normedStarGroup** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
形式化陈述：frobenius_normedStarGroup [StarAddMonoid α] [NormedStarGroup α] : NormedSt
arGroup (Matrix m m α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Matrix.frobenius_norm_conjTranspose`：frobenius_norm_conjTranspose [StarA
ddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖ = ‖A‖
-/
instance frobenius_normedStarGroup [StarAddMonoid α] [NormedStarGroup α] :
    NormedStarGroup (Matrix m m α) :=
  ⟨(le_of_eq <| frobenius_norm_conjTranspose ·)⟩

@[simp]
/-
**Matrix.frobenius_norm_replicateRow** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_replicateRow (v : m -> α) : ‖replicateRow ι v‖ = ‖toLp 2 v‖
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.frobenius_norm_def`：frobenius_norm_def (A : Matrix m n α) : ‖A‖ =
 (∑ i, ∑ j, ‖A i j‖ ^ (2 : Real)) ^ (1 / 2 : Real)
· 使用定理 `Fintype.sum_unique`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Unique ι] (f : ι → M),   ∑ x, f x = f defaul
t
· 使用定理 `PiLp.norm_eq_of_L2`：norm_eq_of_L2 (x : PiLp 2 β) : ‖x‖ = √(∑ i : ι, ‖x i
‖ ^ 2)
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_two`：rpow_two (x : Real) : x ^ (2 : Real) = x ^ 2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma frobenius_norm_replicateRow (v : m → α) : ‖replicateRow ι v‖ = ‖toLp 2 v‖ := by
  rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [replicateRow_apply, Real.rpow_two]

@[simp]
/-
**Matrix.frobenius_nnnorm_replicateRow** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_replicateRow (v : m -> α) : ‖replicateRow ι v‖₊ = ‖toLp 2
 v‖₊
参数：v : m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用引理 `Matrix.frobenius_norm_replicateRow`：frobenius_norm_replicateRow (v : m -
> α) : ‖replicateRow ι v‖ = ‖toLp 2 v‖
-/
lemma frobenius_nnnorm_replicateRow (v : m → α) : ‖replicateRow ι v‖₊ = ‖toLp 2 v‖₊ :=
  Subtype.ext <| frobenius_norm_replicateRow v

@[simp]
/-
**Matrix.frobenius_norm_replicateCol** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_replicateCol (v : n -> α) : ‖replicateCol ι v‖ = ‖toLp 2 v‖
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.frobenius_norm_def`：frobenius_norm_def (A : Matrix m n α) : ‖A‖ =
 (∑ i, ∑ j, ‖A i j‖ ^ (2 : Real)) ^ (1 / 2 : Real)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Real.rpow_ofNat`：rpow_ofNat (x : Real) (n : Nat) [n.AtLeastTwo] : x ^ (o
fNat(n) : Real) = x ^ (ofNat(n) : Nat)
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PiLp.norm_eq_of_L2`：norm_eq_of_L2 (x : PiLp 2 β) : ‖x‖ = √(∑ i : ι, ‖x i
‖ ^ 2)
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma frobenius_norm_replicateCol (v : n → α) : ‖replicateCol ι v‖ = ‖toLp 2 v‖ := by
  simp [frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]

@[simp]
/-
**Matrix.frobenius_nnnorm_replicateCol** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_replicateCol (v : n -> α) : ‖replicateCol ι v‖₊ = ‖toLp 2
 v‖₊
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用引理 `Matrix.frobenius_norm_replicateCol`：frobenius_norm_replicateCol (v : n -
> α) : ‖replicateCol ι v‖ = ‖toLp 2 v‖
-/
lemma frobenius_nnnorm_replicateCol (v : n → α) : ‖replicateCol ι v‖₊ = ‖toLp 2 v‖₊ :=
  Subtype.ext <| frobenius_norm_replicateCol v

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Matrix.frobenius_nnnorm_diagonal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖₊ = ‖
toLp 2 v‖₊
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_def`：frobenius_nnnorm_def (A : Matrix m n α) : ‖
A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : Real)) ^ (1 / 2 : Real)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PiLp.nnnorm_eq_of_L2`：nnnorm_eq_of_L2 (x : PiLp 2 β) : ‖x‖₊ = NNReal.sqr
t (∑ i : ι, ‖x i‖₊ ^ 2)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `NNReal.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real>=0) ^ x 
= 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `NNReal.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real>=0) : sqrt x = x ^ (1 / (2 :
 Real))
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NNReal.rpow_two`：rpow_two (x : Real>=0) : x ^ (2 : Real) = x ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma frobenius_nnnorm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖₊ = ‖toLp 2 v‖₊ := by
  simp_rw [frobenius_nnnorm_def, ← Finset.sum_product', Finset.univ_product_univ,
    PiLp.nnnorm_eq_of_L2]
  let s := (Finset.univ : Finset n).map ⟨fun i : n => (i, i), fun i j h => congr_arg Prod.fst h⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _hi his => ?_]
  · rw [Finset.sum_map, NNReal.sqrt_eq_rpow]
    dsimp
    simp_rw [diagonal_apply_eq, NNReal.rpow_two]
  · suffices i.1 ≠ i.2 by rw [diagonal_apply_ne _ this, nnnorm_zero, NNReal.zero_rpow two_ne_zero]
    intro h
    exact Finset.mem_map.not.mp his ⟨i.1, Finset.mem_univ _, Prod.ext rfl h⟩

@[simp]
/-
**Matrix.frobenius_norm_diagonal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_diagonal [DecidableEq n] (v : n -> α) : ‖diagonal v‖ = ‖toL
p 2 v‖
参数：v : n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `Matrix.frobenius_nnnorm_diagonal`：frobenius_nnnorm_diagonal [DecidableEq
 n] (v : n -> α) : ‖diagonal v‖₊ = ‖toLp 2 v‖₊
-/
lemma frobenius_norm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖ = ‖toLp 2 v‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_diagonal v :).trans rfl

end SeminormedAddCommGroup

/-
**Matrix.frobenius_nnnorm_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_one [DecidableEq n] [SeminormedAddCommGroup α] [One α] : 
‖(1 : Matrix n n α)‖₊ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用引理 `Matrix.frobenius_nnnorm_diagonal`：frobenius_nnnorm_diagonal [DecidableEq
 n] (v : n -> α) : ‖diagonal v‖₊ = ‖toLp 2 v‖₊
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.nnnorm_toLp_const`：nnnorm_toLp_const {β} [SeminormedAddCommGroup β]
 (hp : p != ∞) (b : β) : ‖toLp p (Function.const ι b)‖₊ = (Fintype.card ι : Real
>=0) ^ (1 / …
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `NNReal.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real>=0) : sqrt x = x ^ (1 / (2 :
 Real))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobenius_nnnorm_one [DecidableEq n] [SeminormedAddCommGroup α] [One α] :
    ‖(1 : Matrix n n α)‖₊ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
  calc
    ‖(diagonal 1 : Matrix n n α)‖₊
    _ = ‖toLp 2 (Function.const _ 1)‖₊ := frobenius_nnnorm_diagonal _
    _ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
      rw [PiLp.nnnorm_toLp_const (ENNReal.ofNat_ne_top (n := 2))]
      simp [NNReal.sqrt_eq_rpow]

section RCLike

variable [RCLike α]

/-
**Matrix.frobenius_nnnorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ <= ‖
A‖₊ * ‖B‖₊
参数：A : Matrix l m α；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.frobenius_nnnorm_def`：frobenius_nnnorm_def (A : Matrix m n α) : ‖
A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : Real)) ^ (1 / 2 : Real)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `NNReal.rpow_le_rpow`：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y
 ^ z
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `NNReal.rpow_le_rpow_iff`：rpow_le_rpow_iff {x y : Real>=0} {z : Real} (hz
 : 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NNReal.rpow_two`：rpow_two (x : Real>=0) : x ^ (2 : Real) = x ^ 2
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.inner_apply'`：RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `PiLp.nnnorm_eq_of_L2`：nnnorm_eq_of_L2 (x : PiLp 2 β) : ‖x‖₊ = NNReal.sqr
t (∑ i : ι, ‖x i‖₊ ^ 2)
· 使用定理 `nnnorm_star`：nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊
（共 40 条，此处仅展示前 30 条）
-/
theorem frobenius_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ := by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← NNReal.mul_rpow, @Finset.sum_comm _ _ m, Finset.sum_mul_sum]
  gcongr with i _ j
  rw [← NNReal.rpow_le_rpow_iff one_half_pos, ← NNReal.rpow_mul,
    mul_div_cancel₀ (1 : ℝ) two_ne_zero, NNReal.rpow_one, NNReal.mul_rpow]
  simpa only [PiLp.toLp_apply, PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply,
    Pi.nnnorm_def, PiLp.nnnorm_eq_of_L2, star_star, nnnorm_star, NNReal.sqrt_eq_rpow,
    NNReal.rpow_two] using nnnorm_inner_le_nnnorm (𝕜 := α) (toLp 2 (star <| A i ·)) (toLp 2 (B · j))
/-
**Matrix.frobenius_norm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：frobenius_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ <= ‖A‖ 
* ‖B‖
参数：A : Matrix l m α；B : Matrix m n α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.frobenius_nnnorm_mul`：frobenius_nnnorm_mul (A : Matrix l m α) (B 
: Matrix m n α) : ‖A * B‖₊ <= ‖A‖₊ * ‖B‖₊
-/
theorem frobenius_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  frobenius_nnnorm_mul A B

/-- Normed ring instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.frobeniusNormedRing** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.frobenius_norm_mul`：frobenius_norm_mul (A : Matrix l m α) (B : Ma
trix m n α) : ‖A * B‖ <= ‖A‖ * ‖B‖

--- 原说明 ---
Normed ring instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`.  N
ot
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
def frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α) :=
  { Matrix.frobeniusSeminormedAddCommGroup, Matrix.instRing with
    norm_mul_le := frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed algebra instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[instance_reducible, local instance]
/-
**Matrix.frobeniusNormedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α]
 : NormedAlgebra R (Matrix m m α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Normed algebra instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`.
  Not
declared as an instance because there are several natural choices for defining t
he norm of a
matrix.
-/
def frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α] :
    NormedAlgebra R (Matrix m m α) :=
  { Matrix.frobeniusNormedSpace, Matrix.instAlgebra with }

end RCLike

end frobenius

namespace Norms.Frobenius
attribute [scoped instance]
  Matrix.frobeniusSeminormedAddCommGroup
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra
  Matrix.frobeniusIsBoundedSMul
  Matrix.frobeniusNormSMulClass
end Norms.Frobenius

end Matrix

