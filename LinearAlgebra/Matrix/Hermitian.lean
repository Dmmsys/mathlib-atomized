/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Star.Pi
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.ZPow

/-! # Hermitian matrices

This file defines Hermitian matrices and some basic results about them.

See also `IsSelfAdjoint`, which generalizes this definition to other star rings.

## Main definition

* `Matrix.IsHermitian` : a matrix `A : Matrix n n α` is Hermitian if `Aᴴ = A`.

## Tags

self-adjoint matrix, hermitian matrix

-/

@[expose] public section

-- TODO:
-- assert_not_exists MonoidAlgebra
assert_not_exists NormedGroup

namespace Matrix

variable {α β m n : Type*} {A : Matrix n n α}

section Star

variable [Star α] [Star β]

/-- A matrix is Hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
/-
**Matrix.IsHermitian** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsHermitian (A : Matrix n n α) : Prop
参数：A : Matrix n n α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix is Hermitian if it is equal to its conjugate transpose. On the reals, t
his definition
captures symmetric matrices.
-/
def IsHermitian (A : Matrix n n α) : Prop := Aᴴ = A
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Matrix n n α) [Decidable (Aᴴ = A)] : Decidable (IsHermitian A) :=
  inferInstanceAs <| Decidable (_ = _)
/-
**Matrix.IsHermitian.eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α}, A.IsHe
rmitian → A.conjTranspose = A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsHermitian.eq {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ = A := h
/-
**Matrix.isHermitian_iff_isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_iff_isSelfAdjoint {A : Matrix n n α} : A.IsHermitian ↔ IsSelfA
djoint A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isHermitian_iff_isSelfAdjoint {A : Matrix n n α} :
    A.IsHermitian ↔ IsSelfAdjoint A := Iff.rfl

protected alias ⟨IsHermitian.isSelfAdjoint, _root_.IsSelfAdjoint.isHermitian⟩ :=
  isHermitian_iff_isSelfAdjoint
/-
**Matrix.IsHermitian.star_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} {A : Matrix n n α} [inst : Star α], A.IsHe
rmitian → star A = A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `Matrix.IsHermitian.isSelfAdjoint`：∀ {α : Type u_1} {n : Type u_4} [inst 
: Star α] {A : Matrix n n α}, A.IsHermitian → IsSelfAdjoint A
-/
theorem IsHermitian.star_eq (hA : A.IsHermitian) : star A = A := hA.isSelfAdjoint.star_eq
/-
**Matrix.IsHermitian.ext** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α}, (∀ (i 
j : n), star (A j i) = A i j) → A.IsHermitian
参数：∀ (i j : n), star (A j i) = A i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem IsHermitian.ext {A : Matrix n n α} : (∀ i j, star (A j i) = A i j) → A.IsHermitian := by
  intro h; ext i j; exact h i j
/-
**Matrix.IsHermitian.apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α}, A.IsHe
rmitian → ∀ (i j : n), star (A j i) = A i j
参数：i j : n；A j i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem IsHermitian.apply {A : Matrix n n α} (h : A.IsHermitian) (i j : n) : star (A j i) = A i j :=
  congr_fun (congr_fun h _) _
/-
**Matrix.IsHermitian.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α}, A.IsHe
rmitian ↔ ∀ (i j : n), star (A j i) = A i j
参数：i j : n；A j i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.apply`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α
] {A : Matrix n n α}, A.IsHermitian → ∀ (i j : n), star (A j i) = A i j
· 使用定理 `Matrix.IsHermitian.ext`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] 
{A : Matrix n n α}, (∀ (i j : n), star (A j i) = A i j) → A.IsHermitian
-/
theorem IsHermitian.ext_iff {A : Matrix n n α} : A.IsHermitian ↔ ∀ i j, star (A j i) = A i j :=
  ⟨IsHermitian.apply, IsHermitian.ext⟩
/-
**Matrix.isHermitian_iff_isSymm** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] [TrivialStar α] {A : Matri
x n n α}, A.IsHermitian ↔ A.IsSymm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isHermitian_iff_isSymm [TrivialStar α] {A : Matrix n n α} :
    A.IsHermitian ↔ A.IsSymm := by
  simp [IsHermitian.ext_iff, IsSymm.ext_iff]

@[simp]
/-
**Matrix.IsHermitian.map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {n : Type u_4} [inst : Star α] [inst_1 : S
tar β] {A : Matrix n n α},   A.IsHermitian → ∀ (f : α → β), Function.Semiconj f 
star star → (A.map f).IsHermitian
参数：f : α → β；A.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_map`：conjTranspose_map [Star α] [Star β] {A : Matri
x m n α} (f : α -> β) (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f
)ᴴ
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A
-/
theorem IsHermitian.map {A : Matrix n n α} (h : A.IsHermitian) (f : α → β)
    (hf : Function.Semiconj f star star) : (A.map f).IsHermitian := by
  rw [IsHermitian, ← conjTranspose_map f hf, h.eq]

@[simp]
/-
**Matrix.isHermitian_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_map_iff {A : Matrix n n α} {f : α -> β} (hf : Function.Semicon
j f star star) (hinj : f.Injective) : (A.map f).IsHermitian ↔ A.IsHermitian
参数：hf : Function.Semiconj f star star；hinj : f.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_map`：conjTranspose_map [Star α] [Star β] {A : Matri
x m n α} (f : α -> β) (hf : Function.Semiconj f star star) : Aᴴ.map f = (A.map f
)ᴴ
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Matrix.map_injective`：map_injective {f : α -> β} (hf : Function.Injectiv
e f) : Function.Injective fun M : Matrix m n α => M.map f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isHermitian_map_iff {A : Matrix n n α} {f : α → β} (hf : Function.Semiconj f star star)
    (hinj : f.Injective) : (A.map f).IsHermitian ↔ A.IsHermitian := by
  rw [IsHermitian, IsHermitian, ← conjTranspose_map f hf, map_injective hinj |>.eq_iff]

@[simp, nontriviality]
/-
**Matrix.IsHermitian.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermiti
an`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α} [Subsin
gleton α], A.IsHermitian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.ext`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] 
{A : Matrix n n α}, (∀ (i j : n), star (A j i) = A i j) → A.IsHermitian
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem IsHermitian.of_subsingleton {A : Matrix n n α} [Subsingleton α] : A.IsHermitian :=
  .ext fun _ _ ↦ Subsingleton.elim ..
/-
**Matrix.IsHermitian.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α}, A.IsHe
rmitian → A.transpose.IsHermitian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose.eq_1`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} 
[inst : Star α] (M : Matrix m n α), M.conjTranspose = M.transpose.map star
· 使用定理 `Matrix.transpose_map`：transpose_map {f : α -> β} {M : Matrix m n α} : Mᵀ
.map f = (M.map f)ᵀ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem IsHermitian.transpose {A : Matrix n n α} (h : A.IsHermitian) : Aᵀ.IsHermitian := by
  rw [IsHermitian, conjTranspose, transpose_map]
  exact congr_arg Matrix.transpose h

@[simp]
/-
**Matrix.isHermitian_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_transpose_iff {A : Matrix n n α} : Aᵀ.IsHermitian ↔ A.IsHermit
ian
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.IsHermitian.transpose`：∀ {α : Type u_1} {n : Type u_4} [inst : St
ar α] {A : Matrix n n α}, A.IsHermitian → A.transpose.IsHermitian
-/
theorem isHermitian_transpose_iff {A : Matrix n n α} : Aᵀ.IsHermitian ↔ A.IsHermitian :=
  ⟨by intro h; rw [← transpose_transpose A]; exact IsHermitian.transpose h, IsHermitian.transpose⟩
/-
**Matrix.IsHermitian.conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian
`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {A : Matrix n n α}, A.IsHe
rmitian → A.conjTranspose.IsHermitian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.map`：∀ {α : Type u_1} {β : Type u_2} {n : Type u_4} [
inst : Star α] [inst_1 : Star β] {A : Matrix n n α},   A.IsHermitian → ∀ (f : α 
→ β), Functi…
· 使用定理 `Matrix.IsHermitian.transpose`：∀ {α : Type u_1} {n : Type u_4} [inst : St
ar α] {A : Matrix n n α}, A.IsHermitian → A.transpose.IsHermitian
-/
theorem IsHermitian.conjTranspose {A : Matrix n n α} (h : A.IsHermitian) : Aᴴ.IsHermitian :=
  h.transpose.map _ fun _ => rfl

@[simp]
/-
**Matrix.IsHermitian.submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} [inst : Star α] {A : Matrix
 n n α},   A.IsHermitian → ∀ (f : m → n), (A.submatrix f f).IsHermitian
参数：f : m → n；A.submatrix f f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.conjTranspose_submatrix`：conjTranspose_submatrix [Star α] (A : Ma
trix m n α) (r : l -> m) (c : o -> n) : (A.submatrix r c)ᴴ = Aᴴ.submatrix c r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsHermitian.submatrix {A : Matrix n n α} (h : A.IsHermitian) (f : m → n) :
    (A.submatrix f f).IsHermitian := (conjTranspose_submatrix _ _ _).trans (h.symm ▸ rfl)

@[simp]
/-
**Matrix.isHermitian_submatrix_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_submatrix_equiv {A : Matrix n n α} (e : m ≃ n) : (A.submatrix 
e e).IsHermitian ↔ A.IsHermitian
参数：e : m ≃ n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `Matrix.IsHermitian.submatrix`：∀ {α : Type u_1} {m : Type u_3} {n : Type 
u_4} [inst : Star α] {A : Matrix n n α},   A.IsHermitian → ∀ (f : m → n), (A.sub
matrix f f).IsHerm…
-/
theorem isHermitian_submatrix_equiv {A : Matrix n n α} (e : m ≃ n) :
    (A.submatrix e e).IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩
/-
**Matrix.IsHermitian.reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} [inst : Star α] {A : Matrix
 n n α},   A.IsHermitian → ∀ (f : n ≃ m), ((Matrix.reindex f f) A).IsHermitian
参数：f : n ≃ m；(Matrix.reindex f f) A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.reindex_apply`：reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matri
x m n α) : reindex eₘ eₙ M = M.submatrix eₘ.symm eₙ.symm
· 使用定理 `Matrix.IsHermitian.submatrix`：∀ {α : Type u_1} {m : Type u_3} {n : Type 
u_4} [inst : Star α] {A : Matrix n n α},   A.IsHermitian → ∀ (f : m → n), (A.sub
matrix f f).IsHerm…
-/
theorem IsHermitian.reindex {A : Matrix n n α} (h : A.IsHermitian) (f : n ≃ m) :
    (A.reindex f f).IsHermitian := by
  rw [reindex_apply]
  apply submatrix h
/-
**Matrix.isHermitian_reindex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_reindex_iff {A : Matrix n n α} (f : n ≃ m) : (A.reindex f f).I
sHermitian ↔ A.IsHermitian
参数：f : n ≃ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm_comp_self`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e.symm ∘
 ⇑e = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `Matrix.IsHermitian.reindex`：∀ {α : Type u_1} {m : Type u_3} {n : Type u_
4} [inst : Star α] {A : Matrix n n α},   A.IsHermitian → ∀ (f : n ≃ m), ((Matrix
.reindex f f) A)…
-/
theorem isHermitian_reindex_iff {A : Matrix n n α} (f : n ≃ m) :
    (A.reindex f f).IsHermitian ↔ A.IsHermitian := by
  refine ⟨fun h ↦ ?_, (·.reindex f)⟩
  simpa using h.reindex f.symm
/-
**Matrix.conjTranspose_comp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_comp {I J K L : Type*} (M : Matrix I J (Matrix K L α)) : (co
mp I J K L α M)ᴴ = comp J I L K α (Mᵀ.map (·ᴴ))
参数：M : Matrix I J (Matrix K L α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem conjTranspose_comp {I J K L : Type*} (M : Matrix I J (Matrix K L α)) :
    (comp I J K L α M)ᴴ = comp J I L K α (Mᵀ.map (·ᴴ)) :=
  rfl

/-- When the inner matrices are square we can use the induced star operation -/
/-
**Matrix.conjTranspose_comp'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：conjTranspose_comp' {I J K : Type*} (M : Matrix I J (Matrix K K α)) : (com
p I J K K α M)ᴴ = comp J I K K α Mᴴ
参数：M : Matrix I J (Matrix K K α)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the inner matrices are square we can use the induced star operation
-/
theorem conjTranspose_comp' {I J K : Type*} (M : Matrix I J (Matrix K K α)) :
    (comp I J K K α M)ᴴ = comp J I K K α Mᴴ :=
  rfl
/-
**Matrix.isHermitian_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_comp_iff {A : Matrix m m (Matrix n n α)} : (A.comp m m n n α).
IsHermitian ↔ A.IsHermitian
参数：Matrix n n α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose_comp'`：conjTranspose_comp' {I J K : Type*} (M : Mat
rix I J (Matrix K K α)) : (comp I J K K α M)ᴴ = comp J I K K α Mᴴ
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isHermitian_comp_iff {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsHermitian ↔ A.IsHermitian := by
  rw [IsHermitian, IsHermitian, conjTranspose_comp', comp .. |>.injective.eq_iff]
/-
**Matrix.isHermitian_comp_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_comp_iff_forall {A : Matrix m m (Matrix n n α)} : (A.comp m m 
n n α).IsHermitian ↔ forall i j i' j', star (A j i j' i') = A i j i' j'
参数：Matrix n n α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.comp_apply`：∀ (I : Type u_1) (J : Type u_2) (K : Type u_3) (L : T
ype u_4) (R : Type u_5) (m : Matrix I J (Matrix K L R))   (ik : I × K) (jl : J ×
 L), (M…
-/
theorem isHermitian_comp_iff_forall {A : Matrix m m (Matrix n n α)} :
    (A.comp m m n n α).IsHermitian ↔ ∀ i j i' j', star (A j i j' i') = A i j i' j' := by
  simp [IsHermitian.ext_iff]
  grind

end Star

section InvolutiveStar

variable [InvolutiveStar α]

@[simp]
/-
**Matrix.isHermitian_conjTranspose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_conjTranspose_iff {A : Matrix n n α} : Aᴴ.IsHermitian ↔ A.IsHe
rmitian
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.star_iff`：star_iff [InvolutiveStar R] {x : R} : IsSelfAdjo
int (star x) ↔ IsSelfAdjoint x
-/
theorem isHermitian_conjTranspose_iff {A : Matrix n n α} : Aᴴ.IsHermitian ↔ A.IsHermitian :=
  IsSelfAdjoint.star_iff

/-- A block matrix `A.from_blocks B C D` is Hermitian,
if `A` and `D` are Hermitian and `Bᴴ = C`. -/
/-
**Matrix.IsHermitian.fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} [inst : InvolutiveStar α] {
A : Matrix m m α} {B : Matrix m n α}   {C : Matrix n m α} {D : Matrix n n α},   
A.IsHermitian → B.conjTranspose = C → D.IsHermitian → (Matrix.fromBlocks A B C D
).IsHermitian
参数：Matrix.fromBlocks A B C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.fromBlocks_conjTranspose`：fromBlocks_conjTranspose [Star α] (A : 
Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBl
ocks A B C D)ᴴ = from…

--- 原说明 ---
A block matrix `A.from_blocks B C D` is Hermitian,
if `A` and `D` are Hermitian and `Bᴴ = C`.
-/
theorem IsHermitian.fromBlocks {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} (hA : A.IsHermitian) (hBC : Bᴴ = C) (hD : D.IsHermitian) :
    (A.fromBlocks B C D).IsHermitian := by
  have hCB : Cᴴ = B := by rw [← hBC, conjTranspose_conjTranspose]
  unfold Matrix.IsHermitian
  rw [fromBlocks_conjTranspose, hBC, hCB, hA, hD]

/-- This is the `iff` version of `Matrix.IsHermitian.fromBlocks`. -/
/-
**Matrix.isHermitian_fromBlocks_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matr
ix n m α} {D : Matrix n n α} : (A.fromBlocks B C D).IsHermitian ↔ A.IsHermitian 
∧ Bᴴ = C ∧ Cᴴ = B ∧ D.IsHermitian
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.fromBlocks`：∀ {α : Type u_1} {m : Type u_3} {n : Type
 u_4} [inst : InvolutiveStar α] {A : Matrix m m α} {B : Matrix m n α}   {C : Mat
rix n m α} {D : Mat…

--- 原说明 ---
This is the `iff` version of `Matrix.IsHermitian.fromBlocks`.
-/
theorem isHermitian_fromBlocks_iff {A : Matrix m m α} {B : Matrix m n α} {C : Matrix n m α}
    {D : Matrix n n α} :
    (A.fromBlocks B C D).IsHermitian ↔ A.IsHermitian ∧ Bᴴ = C ∧ Cᴴ = B ∧ D.IsHermitian :=
  ⟨fun h =>
    ⟨congr_arg toBlocks₁₁ h, congr_arg toBlocks₂₁ h, congr_arg toBlocks₁₂ h,
      congr_arg toBlocks₂₂ h⟩,
    fun ⟨hA, hBC, _hCB, hD⟩ => IsHermitian.fromBlocks hA hBC hD⟩

end InvolutiveStar

/-- The Hadamard product of Hermitian matrices is Hermitian. -/
/-
**Matrix.IsHermitian.hadamard** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : CommMonoid α] [inst_1 : StarMul α]
 {A B : Matrix n n α},   A.IsHermitian → B.IsHermitian → (A.hadamard B).IsHermit
ian
参数：A.hadamard B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose_hadamard`：conjTranspose_hadamard [Mul α] [StarMul α
] (A B : Matrix m n α) : (A ⊙ B)ᴴ = Bᴴ ⊙ Aᴴ
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A
· 使用定理 `Matrix.hadamard_comm`：hadamard_comm [CommMagma α] : A ⊙ B = B ⊙ A

--- 原说明 ---
The Hadamard product of Hermitian matrices is Hermitian.
-/
theorem IsHermitian.hadamard [CommMonoid α] [StarMul α] {A B : Matrix n n α}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊙ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_hadamard, hB.eq, hA.eq, hadamard_comm]

section AddMonoid

variable [AddMonoid α] [StarAddMonoid α]

/-- A diagonal matrix is Hermitian if the entries are self-adjoint (as a vector) -/
/-
**Matrix.isHermitian_diagonal_of_self_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：isHermitian_diagonal_of_self_adjoint [DecidableEq n] (v : n -> α) (h : IsS
elfAdjoint v) : (diagonal v).IsHermitian
参数：v : n -> α；h : IsSelfAdjoint v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.diagonal_conjTranspose`：diagonal_conjTranspose [AddMonoid α] [Sta
rAddMonoid α] (v : n -> α) : (diagonal v)ᴴ = diagonal (star v)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
A diagonal matrix is Hermitian if the entries are self-adjoint (as a vector)
-/
theorem isHermitian_diagonal_of_self_adjoint [DecidableEq n] (v : n → α) (h : IsSelfAdjoint v) :
    (diagonal v).IsHermitian :=
  (-- TODO: add a `pi.has_trivial_star` instance and remove the `funext`
        diagonal_conjTranspose v).trans <| congr_arg _ h

/-- A diagonal matrix is Hermitian if each diagonal entry is self-adjoint -/
/-
**Matrix.isHermitian_diagonal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_diagonal_iff [DecidableEq n] {d : n -> α} : IsHermitian (diago
nal d) ↔ (forall i : n, IsSelfAdjoint (d i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_transpose`：diagonal_transpose [Zero α] (v : n -> α) : (d
iagonal v)ᵀ = diagonal v
· 使用定理 `Matrix.diagonal_map`：diagonal_map [Zero α] [Zero β] {f : α -> β} (h : f 
0 = 0) {d : n -> α} : (diagonal d).map f = diagonal fun m => f (d m)
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A diagonal matrix is Hermitian if each diagonal entry is self-adjoint
-/
lemma isHermitian_diagonal_iff [DecidableEq n] {d : n → α} :
    IsHermitian (diagonal d) ↔ (∀ i : n, IsSelfAdjoint (d i)) := by
  simp [isSelfAdjoint_iff, IsHermitian, conjTranspose, diagonal_transpose, diagonal_map]

/-- A block diagonal matrix is Hermitian if and only if each block is Hermitian. -/
/-
**Matrix.isHermitian_blockDiagonal'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : AddMonoid α] [inst_1 : StarAddMono
id α] [inst_2 : DecidableEq n]   {p : n → Type u_5} {M : (i : n) → Matrix (p i) 
(p i) α},   (Matrix.blockDiagonal' M).IsHermitian ↔ ∀ (i : n), (M i).IsHermitian
参数：i : n；p i；p i；Matrix.blockDiagonal' M；i : n；M i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A block diagonal matrix is Hermitian if and only if each block is Hermitian.
-/
theorem isHermitian_blockDiagonal'_iff [DecidableEq n] {p : n → Type*}
    {M : ∀ i, Matrix (p i) (p i) α} : (blockDiagonal' M).IsHermitian ↔ ∀ i, (M i).IsHermitian := by
  grind [IsHermitian, blockDiagonal'_conjTranspose, blockDiagonal'_inj]

/-- A block diagonal matrix whose components are all equal is Hermitian if
and only if each block is Hermitian. -/
/-
**Matrix.isHermitian_blockDiagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_blockDiagonal_iff [DecidableEq n] {M : n -> Matrix m m α} : (b
lockDiagonal M).IsHermitian ↔ forall i, (M i).IsHermitian
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.blockDiagonal_conjTranspose`：blockDiagonal_conjTranspose {α : Typ
e*} [AddMonoid α] [StarAddMonoid α] (M : o -> Matrix m n α) : (blockDiagonal M)ᴴ
 = blockDiagonal fun k =…
· 使用定理 `Matrix.blockDiagonal'_conjTranspose`：∀ {o : Type u_4} {m' : o → Type u_7
} {n' : o → Type u_8} [inst : DecidableEq o] {α : Type u_14} [inst_1 : AddMonoid
 α]   [inst_2 : StarAddMo…
· 使用定理 `Matrix.isHermitian_blockDiagonal'_iff`：∀ {α : Type u_1} {n : Type u_4} [
inst : AddMonoid α] [inst_1 : StarAddMonoid α] [inst_2 : DecidableEq n]   {p : n
 → Type u_5} {M : (i : n) →…

--- 原说明 ---
A block diagonal matrix whose components are all equal is Hermitian if
and only if each block is Hermitian.
-/
theorem isHermitian_blockDiagonal_iff [DecidableEq n] {M : n → Matrix m m α} :
    (blockDiagonal M).IsHermitian ↔ ∀ i, (M i).IsHermitian := by
  simpa [IsHermitian] using isHermitian_blockDiagonal'_iff

/-- A diagonal matrix is Hermitian if the entries have the trivial `star` operation
(such as on the reals). -/
/-
**Matrix.isHermitian_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_diagonal [TrivialStar α] [DecidableEq n] (v : n -> α) : (diago
nal v).IsHermitian
参数：v : n -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.isHermitian_diagonal_of_self_adjoint`：isHermitian_diagonal_of_sel
f_adjoint [DecidableEq n] (v : n -> α) (h : IsSelfAdjoint v) : (diagonal v).IsHe
rmitian
· 使用定理 `IsSelfAdjoint.all`：all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint 
r
· 使用定理 `Pi.instTrivialStarForall`：∀ {I : Type u} {f : I → Type v} [inst : (i : I
) → Star (f i)] [∀ (i : I), TrivialStar (f i)],   TrivialStar ((i : I) → f i)

--- 原说明 ---
A diagonal matrix is Hermitian if the entries have the trivial `star` operation
(such as on the reals).
-/
theorem isHermitian_diagonal [TrivialStar α] [DecidableEq n] (v : n → α) :
    (diagonal v).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (IsSelfAdjoint.all _)

@[simp]
/-
**Matrix.isHermitian_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_zero : (0 : Matrix n n α).IsHermitian
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.zero`：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : Star
AddMonoid R], IsSelfAdjoint 0
-/
theorem isHermitian_zero : (0 : Matrix n n α).IsHermitian :=
  IsSelfAdjoint.zero _

@[simp]
/-
**Matrix.IsHermitian.add** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : AddMonoid α] [inst_1 : StarAddMono
id α] {A B : Matrix n n α},   A.IsHermitian → B.IsHermitian → (A + B).IsHermitia
n
参数：A + B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.add`：add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x + y)
-/
theorem IsHermitian.add {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A + B).IsHermitian :=
  IsSelfAdjoint.add hA hB

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid α] [StarAddMonoid α]

/-
**Matrix.isHermitian_add_transpose_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian
参数：A : Matrix n n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.add_star_self`：add_star_self (x : R) : IsSelfAdjoint (x + 
star x)
-/
theorem isHermitian_add_transpose_self (A : Matrix n n α) : (A + Aᴴ).IsHermitian :=
  IsSelfAdjoint.add_star_self A
/-
**Matrix.isHermitian_transpose_add_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian
参数：A : Matrix n n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.star_add_self`：star_add_self (x : R) : IsSelfAdjoint (star
 x + x)
-/
theorem isHermitian_transpose_add_self (A : Matrix n n α) : (Aᴴ + A).IsHermitian :=
  IsSelfAdjoint.star_add_self A

end AddCommMonoid

section AddGroup

variable [AddGroup α] [StarAddMonoid α]

@[simp]
/-
**Matrix.IsHermitian.neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : AddGroup α] [inst_1 : StarAddMonoi
d α] {A : Matrix n n α},   A.IsHermitian → (-A).IsHermitian
参数：-A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.neg`：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-
x)
-/
theorem IsHermitian.neg {A : Matrix n n α} (h : A.IsHermitian) : (-A).IsHermitian :=
  IsSelfAdjoint.neg h

@[simp]
/-
**Matrix.isHermitian_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_neg_iff {A : Matrix n n α} : (-A).IsHermitian ↔ A.IsHermitian
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Matrix.IsHermitian.neg`：∀ {α : Type u_1} {n : Type u_4} [inst : AddGroup
 α] [inst_1 : StarAddMonoid α] {A : Matrix n n α},   A.IsHermitian → (-A).IsHerm
itian
-/
theorem isHermitian_neg_iff {A : Matrix n n α} : (-A).IsHermitian ↔ A.IsHermitian := by
  refine ⟨fun h ↦ ?_, (·.neg)⟩
  rw [← neg_neg A]
  exact h.neg

@[simp]
/-
**Matrix.IsHermitian.sub** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : AddGroup α] [inst_1 : StarAddMonoi
d α] {A B : Matrix n n α},   A.IsHermitian → B.IsHermitian → (A - B).IsHermitian
参数：A - B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
-/
theorem IsHermitian.sub {A B : Matrix n n α} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A - B).IsHermitian :=
  IsSelfAdjoint.sub hA hB

end AddGroup

section StarModule

variable {R : Type*} [Star R] [Star α] [SMul R α] [StarModule R α]

/-
**Matrix.IsHermitian.smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} {R : Type u_5} [inst : Star R] [inst_1 : S
tar α] [inst_2 : SMul R α] [StarModule R α]   {A : Matrix n n α}, A.IsHermitian 
→ ∀ {k : R}, IsSelfAdjoint k → (k • A).IsHermitian
参数：k • A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose_smul`：conjTranspose_smul [Star R] [Star α] [SMul R 
α] [StarModule R α] (c : R) (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A
-/
theorem IsHermitian.smul {A : Matrix n n α} (h : A.IsHermitian) {k : R} (hk : IsSelfAdjoint k) :
    (k • A).IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, hk.star_eq, h.eq]

end StarModule

section MulAction_StarModule

variable {R : Type*} [Monoid R] [Star R] [Star α] [MulAction R α] [StarModule R α]

/-
**Matrix.IsHermitian.of_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} {R : Type u_5} [inst : Monoid R] [inst_1 :
 Star R] [inst_2 : Star α]   [inst_3 : MulAction R α] [StarModule R α] {A : Matr
ix n n α} {k : R} [Invertible k],   (k • A).IsHermitian → IsSelfAdjoint k → A.Is
Hermitian
参数：k • A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_smul_smul`：∀ {α : Type u_5} {β : Type u_6} [inst : Monoid α] [inst
_1 : MulAction α β] (c : α) (x : β) [inst_2 : Invertible c],   ⅟c • c • x = x
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `Matrix.conjTranspose_smul`：conjTranspose_smul [Star R] [Star α] [SMul R 
α] [StarModule R α] (c : R) (M : Matrix m n α) : (c • M)ᴴ = star c • Mᴴ
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
-/
theorem IsHermitian.of_smul {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
    (hk : IsSelfAdjoint k) : A.IsHermitian := by
  rw [IsHermitian, conjTranspose_smul, hk.star_eq] at h
  simpa using! congr(⅟k • $h)

/-- Assumes `IsSelfAdjoint ⅟k` instead of `IsSelfAdjoint k`.
These are equivalent given `StarMul R` -/
/-
**Matrix.IsHermitian.of_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} {R : Type u_5} [inst : Monoid R] [inst_1 :
 Star R] [inst_2 : Star α]   [inst_3 : MulAction R α] [StarModule R α] {A : Matr
ix n n α} {k : R} [inst_5 : Invertible k],   (k • A).IsHermitian → IsSelfAdjoint
 ⅟k → A.IsHermitian
参数：k • A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `invOf_smul_smul`：∀ {α : Type u_5} {β : Type u_6} [inst : Monoid α] [inst
_1 : MulAction α β] (c : α) (x : β) [inst_2 : Invertible c],   ⅟c • c • x = x
· 使用定理 `Matrix.IsHermitian.smul`：∀ {α : Type u_1} {n : Type u_4} {R : Type u_5} 
[inst : Star R] [inst_1 : Star α] [inst_2 : SMul R α] [StarModule R α]   {A : Ma
trix n n α}, …

--- 原说明 ---
Assumes `IsSelfAdjoint ⅟k` instead of `IsSelfAdjoint k`.
These are equivalent given `StarMul R`
-/
theorem IsHermitian.of_smul' {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
    (hk : IsSelfAdjoint ⅟k) : A.IsHermitian := by
  rw [← invOf_smul_smul k A]
  exact h.smul hk

@[simp]
/-
**Matrix.isHermitian_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_smul_iff {A : Matrix n n α} {k : R} [Invertible k] (hk : IsSel
fAdjoint k) : (k • A).IsHermitian ↔ A.IsHermitian
参数：hk : IsSelfAdjoint k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHermitian.of_smul`：∀ {α : Type u_1} {n : Type u_4} {R : Type u_
5} [inst : Monoid R] [inst_1 : Star R] [inst_2 : Star α]   [inst_3 : MulAction R
 α] [StarModule …
· 使用定理 `Matrix.IsHermitian.smul`：∀ {α : Type u_1} {n : Type u_4} {R : Type u_5} 
[inst : Star R] [inst_1 : Star α] [inst_2 : SMul R α] [StarModule R α]   {A : Ma
trix n n α}, …
-/
theorem isHermitian_smul_iff {A : Matrix n n α} {k : R} [Invertible k] (hk : IsSelfAdjoint k) :
    (k • A).IsHermitian ↔ A.IsHermitian :=
  ⟨(·.of_smul hk), (·.smul hk)⟩

end MulAction_StarModule

section NonUnitalSemiring

variable [NonUnitalSemiring α] [StarRing α]

/-- Note this is more general than `IsSelfAdjoint.mul_star_self` as `B` can be rectangular. -/
/-
**Matrix.isHermitian_mul_conjTranspose_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_mul_conjTranspose_self [Fintype n] (A : Matrix m n α) : (A * A
ᴴ).IsHermitian
参数：A : Matrix m n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose_mul`：conjTranspose_mul [Fintype n] [NonUnitalNonAss
ocSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ
 * Mᴴ
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M

--- 原说明 ---
Note this is more general than `IsSelfAdjoint.mul_star_self` as `B` can be recta
ngular.
-/
theorem isHermitian_mul_conjTranspose_self [Fintype n] (A : Matrix m n α) :
    (A * Aᴴ).IsHermitian := by rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Note this is more general than `IsSelfAdjoint.star_mul_self` as `B` can be rectangular. -/
/-
**Matrix.isHermitian_conjTranspose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_conjTranspose_mul_self [Fintype m] (A : Matrix m n α) : (Aᴴ * 
A).IsHermitian
参数：A : Matrix m n α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose_mul`：conjTranspose_mul [Fintype n] [NonUnitalNonAss
ocSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ
 * Mᴴ
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M

--- 原说明 ---
Note this is more general than `IsSelfAdjoint.star_mul_self` as `B` can be recta
ngular.
-/
theorem isHermitian_conjTranspose_mul_self [Fintype m] (A : Matrix m n α) :
    (Aᴴ * A).IsHermitian := by
  rw [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose]

/-- Note this is more general than `IsSelfAdjoint.conjugate'` as `B` can be rectangular. -/
/-
**Matrix.isHermitian_conjTranspose_mul_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_conjTranspose_mul_mul [Fintype m] {A : Matrix m m α} (B : Matr
ix m n α) (hA : A.IsHermitian) : (Bᴴ * A * B).IsHermitian
参数：B : Matrix m n α；hA : A.IsHermitian。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.conjTranspose_mul`：conjTranspose_mul [Fintype n] [NonUnitalNonAss
ocSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ
 * Mᴴ
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note this is more general than `IsSelfAdjoint.conjugate'` as `B` can be rectangu
lar.
-/
theorem isHermitian_conjTranspose_mul_mul [Fintype m] {A : Matrix m m α} (B : Matrix m n α)
    (hA : A.IsHermitian) : (Bᴴ * A * B).IsHermitian := by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/-- Note this is more general than `IsSelfAdjoint.conjugate` as `B` can be rectangular. -/
/-
**Matrix.isHermitian_mul_mul_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_mul_mul_conjTranspose [Fintype m] {A : Matrix m m α} (B : Matr
ix n m α) (hA : A.IsHermitian) : (B * A * Bᴴ).IsHermitian
参数：B : Matrix n m α；hA : A.IsHermitian。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_assoc`：∀ {l : Type u_1} {m : Type u_2} {n : Type u_3} {o : Ty
pe u_4} {α : Type v} [inst : NonUnitalSemiring α]   [inst_1 : Fintype m] [inst_2
 : Fin…
· 使用定理 `Matrix.conjTranspose_mul`：conjTranspose_mul [Fintype n] [NonUnitalNonAss
ocSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᴴ = Nᴴ
 * Mᴴ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note this is more general than `IsSelfAdjoint.conjugate` as `B` can be rectangul
ar.
-/
theorem isHermitian_mul_mul_conjTranspose [Fintype m] {A : Matrix m m α} (B : Matrix n m α)
    (hA : A.IsHermitian) : (B * A * Bᴴ).IsHermitian := by
  simp only [IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
/-
**Matrix.IsHermitian.commute_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : NonUnitalSemiring α] [inst_1 : Sta
rRing α] [inst_2 : Fintype n]   {A B : Matrix n n α}, A.IsHermitian → B.IsHermit
ian → (Commute A B ↔ (A * B).IsHermitian)
参数：Commute A B ↔ (A * B).IsHermitian。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSelfAdjoint.commute_iff`：commute_iff {R : Type*} [Mul R] [StarMul R] {
x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdj
oint (x * y)
· 使用定理 `Matrix.IsHermitian.isSelfAdjoint`：∀ {α : Type u_1} {n : Type u_4} [inst 
: Star α] {A : Matrix n n α}, A.IsHermitian → IsSelfAdjoint A
-/
lemma IsHermitian.commute_iff [Fintype n] {A B : Matrix n n α}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : Commute A B ↔ (A * B).IsHermitian :=
  hA.isSelfAdjoint.commute_iff hB.isSelfAdjoint

end NonUnitalSemiring

section NonAssocSemiring

variable [NonAssocSemiring α] [StarRing α]

/-- Note this is more general for matrices than `isSelfAdjoint_one` as it does not
require `Fintype n`, which is necessary for `Monoid (Matrix n n R)`. -/
@[simp]
/-
**Matrix.isHermitian_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_one`：conjTranspose_one [DecidableEq n] [NonAssocSem
iring α] [StarRing α] : (1 : Matrix n n α)ᴴ = 1

--- 原说明 ---
Note this is more general for matrices than `isSelfAdjoint_one` as it does not
require `Fintype n`, which is necessary for `Monoid (Matrix n n R)`.
-/
theorem isHermitian_one [DecidableEq n] : (1 : Matrix n n α).IsHermitian :=
  conjTranspose_one

end NonAssocSemiring

section Semiring

variable [Semiring α] [StarRing α]

@[simp]
/-
**Matrix.isHermitian_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_natCast [DecidableEq n] (d : Nat) : (d : Matrix n n α).IsHermi
tian
参数：d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_natCast`：conjTranspose_natCast [DecidableEq n] [Non
AssocSemiring α] [StarRing α] (d : Nat) : (d : Matrix n n α)ᴴ = d
-/
theorem isHermitian_natCast [DecidableEq n] (d : ℕ) : (d : Matrix n n α).IsHermitian :=
  conjTranspose_natCast _
/-
**Matrix.IsHermitian.pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {n : Type u_4} [inst : Semiring α] [inst_1 : StarRing α] 
[inst_2 : Fintype n] [inst_3 : DecidableEq n]   {A : Matrix n n α}, A.IsHermitia
n → ∀ (k : ℕ), (A ^ k).IsHermitian
参数：k : ℕ；A ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.pow`：pow {x : R} (hx : IsSelfAdjoint x) (n : Nat) : IsSelf
Adjoint (x ^ n)
-/
theorem IsHermitian.pow [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsHermitian) (k : ℕ) :
    (A ^ k).IsHermitian := IsSelfAdjoint.pow h _

end Semiring

section Ring
variable [Ring α] [StarRing α]

@[simp]
/-
**Matrix.isHermitian_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_intCast [DecidableEq n] (d : Int) : (d : Matrix n n α).IsHermi
tian
参数：d : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.conjTranspose_intCast`：conjTranspose_intCast [DecidableEq n] [Rin
g α] [StarRing α] (d : Int) : (d : Matrix n n α)ᴴ = d
-/
theorem isHermitian_intCast [DecidableEq n] (d : ℤ) : (d : Matrix n n α).IsHermitian :=
  conjTranspose_intCast _

end Ring

section CommRing

variable [CommRing α] [StarRing α]

/-
**Matrix.IsHermitian.inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} [inst : CommRing α] [inst_1 : StarRing α] 
[inst_2 : Fintype m] [inst_3 : DecidableEq m]   {A : Matrix m m α}, A.IsHermitia
n → A⁻¹.IsHermitian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_nonsing_inv`：conjTranspose_nonsing_inv [StarRing α]
 : A⁻¹ᴴ = Aᴴ⁻¹
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsHermitian.inv [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A⁻¹.IsHermitian := by simp [IsHermitian, conjTranspose_nonsing_inv, hA.eq]

@[simp]
/-
**Matrix.isHermitian_inv** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHermitian_inv [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible
 A] : A⁻¹.IsHermitian ↔ A.IsHermitian
参数：A : Matrix m m α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.inv_inv_of_invertible`：inv_inv_of_invertible [Invertible A] : A⁻¹
⁻¹ = A
· 使用定理 `Matrix.IsHermitian.inv`：∀ {α : Type u_1} {m : Type u_3} [inst : CommRing
 α] [inst_1 : StarRing α] [inst_2 : Fintype m] [inst_3 : DecidableEq m]   {A : M
atrix m m α}…
-/
theorem isHermitian_inv [Fintype m] [DecidableEq m] (A : Matrix m m α) [Invertible A] :
    A⁻¹.IsHermitian ↔ A.IsHermitian :=
  ⟨fun h => by rw [← inv_inv_of_invertible A]; exact IsHermitian.inv h, IsHermitian.inv⟩
/-
**Matrix.IsHermitian.adjugate** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} [inst : CommRing α] [inst_1 : StarRing α] 
[inst_2 : Fintype m] [inst_3 : DecidableEq m]   {A : Matrix m m α}, A.IsHermitia
n → A.adjugate.IsHermitian
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.adjugate_conjTranspose`：adjugate_conjTranspose [StarRing α] (A : 
Matrix n n α) : A.adjugateᴴ = adjugate Aᴴ
· 使用定理 `Matrix.IsHermitian.eq`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α] {
A : Matrix n n α}, A.IsHermitian → A.conjTranspose = A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsHermitian.adjugate [Fintype m] [DecidableEq m] {A : Matrix m m α} (hA : A.IsHermitian) :
    A.adjugate.IsHermitian := by simp [IsHermitian, adjugate_conjTranspose, hA.eq]

/-- Note that `IsSelfAdjoint.zpow` does not apply to matrices as they are not a division ring. -/
/-
**Matrix.IsHermitian.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} [inst : CommRing α] [inst_1 : StarRing α] 
[inst_2 : Fintype m] [inst_3 : DecidableEq m]   {A : Matrix m m α}, A.IsHermitia
n → ∀ (k : ℤ), (A ^ k).IsHermitian
参数：k : ℤ；A ^ k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.eq_1`：∀ {α : Type u_1} {n : Type u_4} [inst : Star α]
 (A : Matrix n n α), A.IsHermitian = (A.conjTranspose = A)
· 使用定理 `Matrix.conjTranspose_zpow`：∀ {n' : Type u_1} [inst : DecidableEq n'] [in
st_1 : Fintype n'] {R : Type u_2} [inst_2 : CommRing R]   [inst_3 : StarRing R] 
(A : Matrix n' …

--- 原说明 ---
Note that `IsSelfAdjoint.zpow` does not apply to matrices as they are not a divi
sion ring.
-/
theorem IsHermitian.zpow [Fintype m] [DecidableEq m] {A : Matrix m m α} (h : A.IsHermitian)
    (k : ℤ) :
    (A ^ k).IsHermitian := by
  rw [IsHermitian, conjTranspose_zpow, h]

section SchurComplement

/-- Notation for `Sum.elim`, scoped within the `Matrix` namespace. -/
scoped infixl:65 " ⊕ᵥ " => Sum.elim

/-
**Matrix.schur_complement_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem schur_complement_eq₁₁ [Fintype m] [DecidableEq m] [Fintype n] {A : Matrix m m α}
    (B : Matrix m n α) (D : Matrix n n α) (x : m → α) (y : n → α) [Invertible A]
    (hA : A.IsHermitian) :
    (star (x ⊕ᵥ y)) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      (star (x + (A⁻¹ * B) *ᵥ y)) ᵥ* A ⬝ᵥ (x + (A⁻¹ * B) *ᵥ y) +
        (star y) ᵥ* (D - Bᴴ * A⁻¹ * B) ⬝ᵥ y := by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hA.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel
/-
**Matrix.schur_complement_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem schur_complement_eq₂₂ [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m m α)
    (B : Matrix m n α) {D : Matrix n n α} (x : m → α) (y : n → α) [Invertible D]
    (hD : D.IsHermitian) :
    (star (x ⊕ᵥ y)) ᵥ* (Matrix.fromBlocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
      (star ((D⁻¹ * Bᴴ) *ᵥ x + y)) ᵥ* D ⬝ᵥ ((D⁻¹ * Bᴴ) *ᵥ x + y) +
        (star x) ᵥ* (A - B * D⁻¹ * Bᴴ) ⬝ᵥ x := by
  simp [Function.star_sumElim, vecMul_fromBlocks, add_vecMul,
    dotProduct_mulVec, vecMul_sub, Matrix.mul_assoc, hD.eq,
    conjTranspose_nonsing_inv, star_mulVec]
  abel

namespace IsHermitian

/-
**Matrix.IsHermitian.fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} [inst : InvolutiveStar α] {
A : Matrix m m α} {B : Matrix m n α}   {C : Matrix n m α} {D : Matrix n n α},   
A.IsHermitian → B.conjTranspose = C → D.IsHermitian → (Matrix.fromBlocks A B C D
).IsHermitian
参数：Matrix.fromBlocks A B C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.fromBlocks_conjTranspose`：fromBlocks_conjTranspose [Star α] (A : 
Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBl
ocks A B C D)ᴴ = from…
-/
theorem fromBlocks₁₁ [Fintype m] [DecidableEq m] {A : Matrix m m α} (B : Matrix m n α)
    (D : Matrix n n α) (hA : A.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (D - Bᴴ * A⁻¹ * B).IsHermitian := by
  have hBAB : (Bᴴ * A⁻¹ * B).IsHermitian := isHermitian_conjTranspose_mul_mul _ hA.inv
  rw [isHermitian_fromBlocks_iff]
  exact ⟨fun h ↦ h.2.2.2.sub hBAB, fun h ↦ ⟨hA, rfl, conjTranspose_conjTranspose B,
    sub_add_cancel D _ ▸ h.add hBAB⟩⟩
/-
**Matrix.IsHermitian.fromBlocks** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {α : Type u_1} {m : Type u_3} {n : Type u_4} [inst : InvolutiveStar α] {
A : Matrix m m α} {B : Matrix m n α}   {C : Matrix n m α} {D : Matrix n n α},   
A.IsHermitian → B.conjTranspose = C → D.IsHermitian → (Matrix.fromBlocks A B C D
).IsHermitian
参数：Matrix.fromBlocks A B C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.fromBlocks_conjTranspose`：fromBlocks_conjTranspose [Star α] (A : 
Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) : (fromBl
ocks A B C D)ᴴ = from…
-/
theorem fromBlocks₂₂ [Fintype n] [DecidableEq n] (A : Matrix m m α) (B : Matrix m n α)
    {D : Matrix n n α} (hD : D.IsHermitian) :
    (Matrix.fromBlocks A B Bᴴ D).IsHermitian ↔ (A - B * D⁻¹ * Bᴴ).IsHermitian := by
  rw [← isHermitian_submatrix_equiv (Equiv.sumComm n m), Equiv.sumComm_apply,
    fromBlocks_submatrix_sum_swap_sum_swap]
  convert! IsHermitian.fromBlocks₁₁ _ _ hD <;> simp

end IsHermitian

end SchurComplement

end CommRing
end Matrix

