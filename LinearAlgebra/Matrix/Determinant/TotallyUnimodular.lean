/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Vladimir Kolmogorov, Ivan Sergeev, Bhavik Mehta
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Sign.Basic

/-!
# Totally unimodular matrices

This file defines totally unimodular matrices and provides basic API for them.

## Main definitions

- `Matrix.IsTotallyUnimodular`: a matrix is totally unimodular iff every square submatrix
  (not necessarily contiguous) has determinant `0` or `1` or `-1`.

## Main results

- `Matrix.isTotallyUnimodular_iff`: a matrix is totally unimodular iff every square submatrix
  (possibly with repeated rows and/or repeated columns) has determinant `0` or `1` or `-1`.
- `Matrix.IsTotallyUnimodular.apply`: entry in a totally unimodular matrix is `0` or `1` or `-1`.

-/

@[expose] public section

namespace Matrix

variable {m m' n n' R : Type*} [CommRing R]

/-- `A.IsTotallyUnimodular` means that every square submatrix of `A` (not necessarily contiguous)
has determinant `0` or `1` or `-1`; that is, the determinant is in the range of `SignType.cast`. -/
/-
**Matrix.IsTotallyUnimodular** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsTotallyUnimodular (A : Matrix m n R) : Prop
参数：A : Matrix m n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`A.IsTotallyUnimodular` means that every square submatrix of `A` (not necessaril
y contiguous)
has determinant `0` or `1` or `-1`; that is, the determinant is in the range of 
`SignType.cast`.
-/
def IsTotallyUnimodular (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n, f.Injective → g.Injective →
    (A.submatrix f g).det ∈ Set.range SignType.cast
/-
**Matrix.isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔ foral
l k : Nat, forall f : Fin k -> m, forall g : Fin k -> n, (A.submatrix f g).det i
n Set.range SignType.cast
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SignType.coe_zero`：coe_zero : ↑(0 : SignType) = (0 : α)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.transpose_submatrix`：transpose_submatrix (A : Matrix m n α) (r : 
l -> m) (c : o -> n) : (A.submatrix r c)ᵀ = Aᵀ.submatrix c r
· 使用定理 `Matrix.det_zero_of_column_eq`：det_zero_of_column_eq (i_ne_j : i != j) (h
ij : forall k, M k i = M k j) : M.det = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  constructor <;> intro hA
  · intro k f g
    by_cases hfg : f.Injective ∧ g.Injective
    · exact hA k f g hfg.1 hfg.2
    · use 0
      rw [SignType.coe_zero, eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
      · rw [← det_transpose, transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]
  · intro _ _ _ _ _
    apply hA
/-
**Matrix.isTotallyUnimodular_iff_fintype.** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isTotallyUnimodular_iff_fintype.{w} (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι], ∀ f : ι → m, ∀ g : ι → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at hA
/-
**Matrix.IsTotallyUnimodular.apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsTotallyUn
imodular`。
形式化陈述：∀ {m : Type u_1} {n : Type u_3} {R : Type u_5} [inst : CommRing R] {A : Ma
trix m n R},   A.IsTotallyUnimodular → ∀ (i : m) (j : n), A i j ∈ Set.range Sign
Type.cast
参数：i : m；j : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_unique`：det_unique {n : Type*} [Unique n] [DecidableEq n] [Fi
ntype n] (A : Matrix n n R) : det A = A default default
· 使用引理 `Matrix.isTotallyUnimodular_iff`：isTotallyUnimodular_iff (A : Matrix m n 
R) : A.IsTotallyUnimodular ↔ forall k : Nat, forall f : Fin k -> m, forall g : F
in k -> n, (A.submat…
-/
lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n) :
    A i j ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff] at hA
  simpa using hA 1 (fun _ => i) (fun _ => j)
/-
**Matrix.IsTotallyUnimodular.submatrix** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsTotal
lyUnimodular`。
形式化陈述：∀ {m : Type u_1} {m' : Type u_2} {n : Type u_3} {n' : Type u_4} {R : Type 
u_5} [inst : CommRing R] {A : Matrix m n R}   (f : m' → m) (g : n' → n), A.IsTot
allyUnimodular → (A.submatrix f g).IsTotallyUnimodular
参数：f : m' → m；g : n' → n；A.submatrix f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
-/
lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (f : m' → m) (g : n' → n)
    (hA : A.IsTotallyUnimodular) :
    (A.submatrix f g).IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA
/-
**Matrix.IsTotallyUnimodular.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsTotal
lyUnimodular`。
形式化陈述：∀ {m : Type u_1} {n : Type u_3} {R : Type u_5} [inst : CommRing R] {A : Ma
trix m n R},   A.IsTotallyUnimodular → A.transpose.IsTotallyUnimodular
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
-/
lemma IsTotallyUnimodular.transpose {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    Aᵀ.IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA
/-
**Matrix.transpose_isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：transpose_isTotallyUnimodular_iff (A : Matrix m n R) : Aᵀ.IsTotallyUnimodu
lar ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsTotallyUnimodular.transpose`：∀ {m : Type u_1} {n : Type u_3} {R
 : Type u_5} [inst : CommRing R] {A : Matrix m n R},   A.IsTotallyUnimodular → A
.transpose.IsTotallyUnimod…
-/
lemma transpose_isTotallyUnimodular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor <;> apply IsTotallyUnimodular.transpose
/-
**Matrix.IsTotallyUnimodular.reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsTotally
Unimodular`。
形式化陈述：∀ {m : Type u_1} {m' : Type u_2} {n : Type u_3} {n' : Type u_4} {R : Type 
u_5} [inst : CommRing R] {A : Matrix m n R}   (em : m ≃ m') (en : n ≃ n'), A.IsT
otallyUnimodular → ((Matrix.reindex em en) A).IsTotallyUnimodular
参数：em : m ≃ m'；en : n ≃ n'；(Matrix.reindex em en) A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsTotallyUnimodular.submatrix`：∀ {m : Type u_1} {m' : Type u_2} {
n : Type u_3} {n' : Type u_4} {R : Type u_5} [inst : CommRing R] {A : Matrix m n
 R}   (f : m' → m) (g : n'…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma IsTotallyUnimodular.reindex {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
    (hA : A.IsTotallyUnimodular) :
    (A.reindex em en).IsTotallyUnimodular :=
  hA.submatrix _ _
/-
**Matrix.reindex_isTotallyUnimodular** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：reindex_isTotallyUnimodular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n')
 : (A.reindex em en).IsTotallyUnimodular ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R；em : m ≃ m'；en : n ≃ n'。
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
· 使用定理 `Matrix.IsTotallyUnimodular.reindex`：∀ {m : Type u_1} {m' : Type u_2} {n 
: Type u_3} {n' : Type u_4} {R : Type u_5} [inst : CommRing R] {A : Matrix m n R
}   (em : m ≃ m') (en : …
-/
lemma reindex_isTotallyUnimodular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    (A.reindex em en).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨fun hA => by simpa [Equiv.symm_apply_eq] using hA.reindex em.symm en.symm,
   fun hA => hA.reindex _ _⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `A` has no rows, then it is totally unimodular. -/
@[simp]
/-
**Matrix.emptyRows_isTotallyUnimodular** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：emptyRows_isTotallyUnimodular [IsEmpty m] (A : Matrix m n R) : A.IsTotally
Unimodular
参数：A : Matrix m n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.submatrix_empty`：submatrix_empty (A : Matrix m' n' α) (row : Fin 
0 -> m') (col : o' -> n') : submatrix A row col = of ![]
· 使用定理 `Matrix.det_fin_zero`：det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A
 = 1
· 使用定理 `SignType.coe_one`：coe_one : ↑(1 : SignType) = (1 : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
If `A` has no rows, then it is totally unimodular.
-/
lemma emptyRows_isTotallyUnimodular [IsEmpty m] (A : Matrix m n R) :
    A.IsTotallyUnimodular := by
  intro k f _ _ _
  cases k with
  | zero => use 1; rw [submatrix_empty, det_fin_zero, SignType.coe_one]
  | succ => exact (IsEmpty.false (f 0)).elim

/-- If `A` has no columns, then it is totally unimodular. -/
@[simp]
/-
**Matrix.emptyCols_isTotallyUnimodular** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：emptyCols_isTotallyUnimodular [IsEmpty n] (A : Matrix m n R) : A.IsTotally
Unimodular
参数：A : Matrix m n R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsTotallyUnimodular.transpose`：∀ {m : Type u_1} {n : Type u_3} {R
 : Type u_5} [inst : CommRing R] {A : Matrix m n R},   A.IsTotallyUnimodular → A
.transpose.IsTotallyUnimod…
· 使用引理 `Matrix.emptyRows_isTotallyUnimodular`：emptyRows_isTotallyUnimodular [IsE
mpty m] (A : Matrix m n R) : A.IsTotallyUnimodular

--- 原说明 ---
If `A` has no columns, then it is totally unimodular.
-/
lemma emptyCols_isTotallyUnimodular [IsEmpty n] (A : Matrix m n R) :
    A.IsTotallyUnimodular :=
  A.transpose.emptyRows_isTotallyUnimodular.transpose

set_option backward.isDefEq.respectTransparency false in
/-- If `A` is totally unimodular and each row of `B` is all zeros except for at most a single `1` or
a single `-1` then `fromRows A B` is totally unimodular. -/
/-
**Matrix.IsTotallyUnimodular.fromRows_unitlike** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
.IsTotallyUnimodular`。
形式化陈述：∀ {m : Type u_1} {m' : Type u_2} {n : Type u_3} {R : Type u_5} [inst : Com
mRing R] [inst_1 : DecidableEq n]   {A : Matrix m n R} {B : Matrix m' n R},   A.
IsTotallyUnimodular → (Nonempty n → ∀ (i : m'), ∃ j s, B i = Pi.single j ↑s) → (
A.fromRows B).IsTotallyUnimodular
参数：Nonempty n → ∀ (i : m'), ∃ j s, B i = Pi.single j ↑s；A.fromRows B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `Matrix.submatrix_empty`：submatrix_empty (A : Matrix m' n' α) (row : Fin 
0 -> m') (col : o' -> n') : submatrix A row col = of ![]
· 使用定理 `Matrix.det_fin_zero`：det_fin_zero {A : Matrix (Fin 0) (Fin 0) R} : det A
 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Matrix.det_succ_row`：det_succ_row {n : Nat} (A : Matrix (Fin n.succ) (Fi
n n.succ) R) (i : Fin n.succ) : det A = ∑ j : Fin n.succ, (-1) ^ (i + j : Nat) *
 A i j * …
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` is totally unimodular and each row of `B` is all zeros except for at most
 a single `1` or
a single `-1` then `fromRows A B` is totally unimodular.
-/
lemma IsTotallyUnimodular.fromRows_unitlike [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hA : A.IsTotallyUnimodular)
    (hB : Nonempty n → ∀ i : m', ∃ j : n, ∃ s : SignType, B i = Pi.single j s.cast) :
    (fromRows A B).IsTotallyUnimodular := by
  intro k f g hf hg
  induction k with
  | zero => use 1; simp
  | succ k ih =>
    specialize hB ⟨g 0⟩
    -- Either `f` is `inr` somewhere or `inl` everywhere
    obtain ⟨i, j, hfi⟩ | ⟨f', rfl⟩ : (∃ i j, f i = .inr j) ∨ (∃ f', f = .inl ∘ f') := by
      simp_rw [← Sum.isRight_iff, or_iff_not_imp_left, not_exists, Bool.not_eq_true,
        Sum.isRight_eq_false, Sum.isLeft_iff]
      intro hfr
      choose f' hf' using hfr
      exact ⟨f', funext hf'⟩
    · have hAB := det_succ_row ((fromRows A B).submatrix f g) i
      simp only [submatrix_apply, hfi, fromRows_apply_inr] at hAB
      obtain ⟨j', s, hj'⟩ := hB j
      · simp only [hj'] at hAB
        by_cases hj'' : ∃ x, g x = j'
        · obtain ⟨x, rfl⟩ := hj''
          rw [Fintype.sum_eq_single x fun y hxy => ?_, Pi.single_eq_same] at hAB
          · rw [hAB]
            change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
            refine mul_mem (mul_mem ?_ (Set.mem_range_self s)) ?_
            · apply pow_mem
              exact ⟨-1, by simp⟩
            · exact ih _ _
                (hf.comp Fin.succAbove_right_injective)
                (hg.comp Fin.succAbove_right_injective)
          · simp [Pi.single_eq_of_ne, hg.ne_iff.mpr hxy]
        · rw [not_exists] at hj''
          use 0
          simpa [hj''] using hAB.symm
    · rw [isTotallyUnimodular_iff] at hA
      apply hA

/-- If `A` is totally unimodular and each row of `B` is all zeros except for at most a single `1`,
then `fromRows A B` is totally unimodular. -/
/-
**Matrix.fromRows_isTotallyUnimodular_iff_rows** 是 Mathlib 中的一个引理，位于命名空间 `Matrix
`。
形式化陈述：fromRows_isTotallyUnimodular_iff_rows [DecidableEq n] {A : Matrix m n R} {
B : Matrix m' n R} (hB : Nonempty n -> forall i : m', exists j : n, exists s : S
ignType, B i = Pi.single j s.cast) : (fromRows A B).IsTotallyUnimodular ↔ A.IsTo
tallyUnimodular
参数：hB : Nonempty n -> forall i : m', exists j : n, exists s : SignType, B i = Pi
.single j s.cast。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsTotallyUnimodular.submatrix`：∀ {m : Type u_1} {m' : Type u_2} {
n : Type u_3} {n' : Type u_4} {R : Type u_5} [inst : CommRing R] {A : Matrix m n
 R}   (f : m' → m) (g : n'…
· 使用定理 `Matrix.IsTotallyUnimodular.fromRows_unitlike`：∀ {m : Type u_1} {m' : Typ
e u_2} {n : Type u_3} {R : Type u_5} [inst : CommRing R] [inst_1 : DecidableEq n
]   {A : Matrix m n R} {B : Matrix…

--- 原说明 ---
If `A` is totally unimodular and each row of `B` is all zeros except for at most
 a single `1`,
then `fromRows A B` is totally unimodular.
-/
lemma fromRows_isTotallyUnimodular_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : Nonempty n → ∀ i : m', ∃ j : n, ∃ s : SignType, B i = Pi.single j s.cast) :
    (fromRows A B).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨.submatrix Sum.inl id, fun hA => hA.fromRows_unitlike hB⟩
/-
**Matrix.fromRows_one_isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`
。
形式化陈述：fromRows_one_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) : 
(fromRows A (1 : Matrix n n R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.fromRows_isTotallyUnimodular_iff_rows`：fromRows_isTotallyUnimodul
ar_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R} (hB : Nonempt
y n -> forall i : m', exists j : n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromRows_one_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows A (1 : Matrix n n R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  fromRows_isTotallyUnimodular_iff_rows <| fun h i ↦
    ⟨i, 1, funext fun j ↦ by simp [one_apply, Pi.single_apply, eq_comm]⟩
/-
**Matrix.one_fromRows_isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`
。
形式化陈述：one_fromRows_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) : 
(fromRows (1 : Matrix n n R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Matrix.reindex_isTotallyUnimodular`：reindex_isTotallyUnimodular (A : Mat
rix m n R) (em : m ≃ m') (en : n ≃ n') : (A.reindex em en).IsTotallyUnimodular ↔
 A.IsTotallyUnimodular
· 使用引理 `Matrix.fromRows_one_isTotallyUnimodular_iff`：fromRows_one_isTotallyUnimo
dular_iff [DecidableEq n] (A : Matrix m n R) : (fromRows A (1 : Matrix n n R)).I
sTotallyUnimodular ↔ A.IsTotallyU…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_fromRows_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows (1 : Matrix n n R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  have hA :
    fromRows (1 : Matrix n n R) A =
      (fromRows A (1 : Matrix n n R)).reindex (Equiv.sumComm m n) (Equiv.refl n) := by
    aesop
  rw [hA, reindex_isTotallyUnimodular, fromRows_one_isTotallyUnimodular_iff]
/-
**Matrix.fromCols_one_isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`
。
形式化陈述：fromCols_one_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) : 
(fromCols A (1 : Matrix m m R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.transpose_isTotallyUnimodular_iff`：transpose_isTotallyUnimodular_
iff (A : Matrix m n R) : Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular
· 使用引理 `Matrix.transpose_fromCols`：transpose_fromCols (A₁ : Matrix m n₁ R) (A₂ :
 Matrix m n₂ R) : transpose (fromCols A₁ A₂) = fromRows (transpose A₁) (transpos
e A₂)
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用引理 `Matrix.fromRows_one_isTotallyUnimodular_iff`：fromRows_one_isTotallyUnimo
dular_iff [DecidableEq n] (A : Matrix m n R) : (fromRows A (1 : Matrix n n R)).I
sTotallyUnimodular ↔ A.IsTotallyU…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma fromCols_one_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols A (1 : Matrix m m R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_one,
    fromRows_one_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]
/-
**Matrix.one_fromCols_isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`
。
形式化陈述：one_fromCols_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) : 
(fromCols (1 : Matrix m m R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.transpose_isTotallyUnimodular_iff`：transpose_isTotallyUnimodular_
iff (A : Matrix m n R) : Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular
· 使用引理 `Matrix.transpose_fromCols`：transpose_fromCols (A₁ : Matrix m n₁ R) (A₂ :
 Matrix m n₂ R) : transpose (fromCols A₁ A₂) = fromRows (transpose A₁) (transpos
e A₂)
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用引理 `Matrix.one_fromRows_isTotallyUnimodular_iff`：one_fromRows_isTotallyUnimo
dular_iff [DecidableEq n] (A : Matrix m n R) : (fromRows (1 : Matrix n n R) A).I
sTotallyUnimodular ↔ A.IsTotallyU…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_fromCols_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols (1 : Matrix m m R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_one,
    one_fromRows_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

alias ⟨_, IsTotallyUnimodular.fromRows_one⟩ := fromRows_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromRows⟩ := one_fromRows_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.fromCols_one⟩ := fromCols_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromCols⟩ := one_fromCols_isTotallyUnimodular_iff
/-
**Matrix.fromRows_replicateRow0_isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空
间 `Matrix`。
形式化陈述：fromRows_replicateRow0_isTotallyUnimodular_iff (A : Matrix m n R) : (fromR
ows A (replicateRow m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Matrix.fromRows_isTotallyUnimodular_iff_rows`：fromRows_isTotallyUnimodul
ar_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R} (hB : Nonempt
y n -> forall i : m', exists j : n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromRows_replicateRow0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromRows A (replicateRow m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  classical
  refine fromRows_isTotallyUnimodular_iff_rows <| fun _ _ => ?_
  inhabit n
  refine ⟨default, 0, ?_⟩
  ext x
  simp [Pi.single_apply]
/-
**Matrix.fromCols_replicateCol0_isTotallyUnimodular_iff** 是 Mathlib 中的一个引理，位于命名空
间 `Matrix`。
形式化陈述：fromCols_replicateCol0_isTotallyUnimodular_iff (A : Matrix m n R) : (fromC
ols A (replicateCol n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular
参数：A : Matrix m n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.transpose_isTotallyUnimodular_iff`：transpose_isTotallyUnimodular_
iff (A : Matrix m n R) : Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular
· 使用引理 `Matrix.transpose_fromCols`：transpose_fromCols (A₁ : Matrix m n₁ R) (A₂ :
 Matrix m n₂ R) : transpose (fromCols A₁ A₂) = fromRows (transpose A₁) (transpos
e A₂)
· 使用定理 `Matrix.transpose_replicateCol`：transpose_replicateCol (v : m -> α) : (re
plicateCol ι v)ᵀ = replicateRow ι v
· 使用引理 `Matrix.fromRows_replicateRow0_isTotallyUnimodular_iff`：fromRows_replicat
eRow0_isTotallyUnimodular_iff (A : Matrix m n R) : (fromRows A (replicateRow m' 
0)).IsTotallyUnimodular ↔ A.IsTotallyUnimod…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma fromCols_replicateCol0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromCols A (replicateCol n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_replicateCol,
    fromRows_replicateRow0_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

end Matrix

