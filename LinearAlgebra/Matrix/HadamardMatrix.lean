/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Star.Unitary

/-!
# Hadamard matrices

This file defines `Matrix.IsHadamard`, a unified notion that specializes to the classical real
Hadamard matrices over `ℝ`/`ℤ` (where `star` is trivial and entries are `±1`) and to the complex
Hadamard matrices over `ℂ` (where entries have unit norm). Basic results: conjugate-transpose
closure, the order identity `n = s * star s` from constant row or column sums, the Sylvester
(Kronecker) construction, and the divisibility obstruction `4 ∣ n`.

## References

* [W. de Launey and D. L. Flannery, *Algebraic Design Theory*][deLauneyFlannery2011]
-/

@[expose] public section


variable {m n R : Type*}

namespace Matrix

open scoped Kronecker

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section Semiring
variable [Semiring R] [StarRing R]

/-- A square matrix over a `*`-semiring whose entries are unitary and whose rows and columns are
orthogonal with respect to the conjugate transpose:
`A * Aᴴ = n • 1` and `Aᴴ * A = n • 1`.

Over a commutative ring in which the order is regular, the one-sided condition from
[Definition 2.3.1][deLauneyFlannery2011] implies this predicate by
`IsHadamard.of_mul_conjTranspose`; over a ring with trivial star (e.g. `ℝ`, `ℤ`), the entry
condition becomes `A i j = 1 ∨ A i j = -1`. Over `ℂ`, the entry condition becomes `‖A i j‖ = 1`,
generalizing the fourth-root complex Hadamard matrices of
[Definition 2.7.1][deLauneyFlannery2011]. -/
/-
**Matrix.IsHadamard** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_2} →   {R : Type u_3} → [Fintype n] → [DecidableEq n] → [inst 
: Semiring R] → [StarRing R] → Matrix n n R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square matrix over a `*`-semiring whose entries are unitary and whose rows and
 columns are
orthogonal with respect to the conjugate transpose:
`A * Aᴴ = n • 1` and `Aᴴ * A = n • 1`.

Over a commutative ring in which the order is regular, the one-sided condition f
rom
[Definition 2.3.1][deLauneyFlannery2011] implies this predicate by
`IsHadamard.of_mul_conjTranspose`; over a ring with trivial star (e.g. `ℝ`, `ℤ`)
, the entry
condition becomes `A i j = 1 ∨ A i j = -1`. Over `ℂ`, the entry condition become
s `‖A i j‖ = 1`,
generalizing the fourth-root complex Hadamard matrices of
[Definition 2.7.1][deLauneyFlannery2011].
-/
@[mk_iff] structure IsHadamard (A : Matrix n n R) : Prop where
  apply_mem (i j : n) : A i j ∈ unitary R
  mul_conjTranspose : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R)
  conjTranspose_mul : Aᴴ * A = (Fintype.card n : R) • (1 : Matrix n n R)

variable {A : Matrix n n R}
/-
**Matrix.IsHadamard.isStarNormal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Semiring R] [inst_3 : StarRing R]   {A : Matrix n n R}, A.IsHadamard
 → IsStarNormal A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Matrix.star_eq_conjTranspose`：star_eq_conjTranspose [Star α] (M : Matrix
 m m α) : star M = Mᴴ
· 使用定理 `Matrix.IsHadamard.conjTranspose_mul`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
-/
theorem IsHadamard.isStarNormal (hA : A.IsHadamard) : IsStarNormal A where
  star_comm_self := by
    rw [commute_iff_eq, star_eq_conjTranspose, hA.conjTranspose_mul, hA.mul_conjTranspose]

/-- The conjugate transpose of a Hadamard matrix is Hadamard. -/
/-
**Matrix.IsHadamard.conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Semiring R] [inst_3 : StarRing R]   {A : Matrix n n R}, A.IsHadamard
 → A.conjTranspose.IsHadamard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.star_mem`：star_mem {U : R} (hU : U in unitary R) : star U in uni
tary R
· 使用定理 `Matrix.IsHadamard.apply_mem`：∀ {n : Type u_2} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]   {
A : Matrix n n R}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.IsHadamard.conjTranspose_mul`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…

--- 原说明 ---
The conjugate transpose of a Hadamard matrix is Hadamard.
-/
theorem IsHadamard.conjTranspose (hA : A.IsHadamard) : Aᴴ.IsHadamard := by
  exact ⟨fun i j => Unitary.star_mem (hA.apply_mem j i),
    by simpa using hA.conjTranspose_mul,
    by simpa using hA.mul_conjTranspose⟩

@[simp]
/-
**Matrix.isHadamard_conjTranspose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHadamard_conjTranspose_iff : Aᴴ.IsHadamard ↔ A.IsHadamard
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHadamard.congr_simp`：∀ {n : Type u_2} {R : Type u_3} [inst : Fi
ntype n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Semiring 
R] [inst_4 : StarR…
· 使用定理 `Matrix.conjTranspose_conjTranspose`：conjTranspose_conjTranspose [Involut
iveStar α] (M : Matrix m n α) : Mᴴᴴ = M
· 使用定理 `Matrix.IsHadamard.conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [inst :
 Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]
   {A : Matrix n n R}…
-/
theorem isHadamard_conjTranspose_iff : Aᴴ.IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.conjTranspose, (·.conjTranspose)⟩

/-- Permuting the rows and columns of a Hadamard matrix gives a Hadamard matrix. -/
/-
**Matrix.IsHadamard.reindex** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 
: Fintype n] [inst_2 : DecidableEq m]   [inst_3 : DecidableEq n] [inst_4 : Semir
ing R] [inst_5 : StarRing R] {A : Matrix n n R} (e₁ e₂ : n ≃ m),   A.IsHadamard 
→ ((Matrix.reindex e₁ e₂) A).IsHadamard
参数：e₁ e₂ : n ≃ m；(Matrix.reindex e₁ e₂) A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHadamard.apply_mem`：∀ {n : Type u_2} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]   {
A : Matrix n n R}…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_submatrix`：conjTranspose_submatrix [Star α] (A : Ma
trix m n α) (r : l -> m) (c : o -> n) : (A.submatrix r c)ᴴ = Aᴴ.submatrix c r
· 使用定理 `Matrix.submatrix_mul_equiv`：submatrix_mul_equiv [Fintype n] [Fintype o] 
[AddCommMonoid α] [Mul α] {p q : Type*} (M : Matrix m n α) (N : Matrix n p α) (e
₁ : l -> m) (e₂ …
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Matrix.submatrix_one_equiv`：submatrix_one_equiv [Zero α] [One α] [Decida
bleEq m] [DecidableEq l] (e : l ≃ m) : (1 : Matrix m m α).submatrix e e = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.IsHadamard.conjTranspose_mul`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…

--- 原说明 ---
Permuting the rows and columns of a Hadamard matrix gives a Hadamard matrix.
-/
theorem IsHadamard.reindex (e₁ e₂ : n ≃ m) (hA : A.IsHadamard) :
    (reindex e₁ e₂ A).IsHadamard := by
  refine ⟨fun i j => hA.apply_mem _ _, ?_, ?_⟩ <;>
    simp [reindex_apply, submatrix_mul_equiv, hA.mul_conjTranspose, hA.conjTranspose_mul,
      Fintype.card_congr e₁, submatrix_smul, Pi.smul_apply]

@[simp]
/-
**Matrix.isHadamard_submatrix_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHadamard_submatrix_equiv_iff (e₁ e₂ : m ≃ n) : (A.submatrix e₁ e₂).IsHad
amard ↔ A.IsHadamard
参数：e₁ e₂ : m ≃ n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHadamard.congr_simp`：∀ {n : Type u_2} {R : Type u_3} [inst : Fi
ntype n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Semiring 
R] [inst_4 : StarR…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Matrix.submatrix_submatrix`：submatrix_submatrix {l₂ o₂ : Type*} (A : Mat
rix m n α) (r₁ : l -> m) (c₁ : o -> n) (r₂ : l₂ -> l) (c₂ : o₂ -> o) : (A.submat
rix r₁ c₁).subma…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Matrix.submatrix_id_id`：submatrix_id_id (A : Matrix m n α) : A.submatrix
 id id = A
· 使用定理 `Matrix.IsHadamard.reindex`：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3
} [inst : Fintype m] [inst_1 : Fintype n] [inst_2 : DecidableEq m]   [inst_3 : D
ecidableEq n] […
-/
theorem isHadamard_submatrix_equiv_iff (e₁ e₂ : m ≃ n) :
    (A.submatrix e₁ e₂).IsHadamard ↔ A.IsHadamard :=
  ⟨fun h => by simpa using h.reindex e₁ e₂,
    fun h => by simpa [reindex_apply] using h.reindex e₁.symm e₂.symm⟩

/-- The Kronecker product of two Hadamard matrices is Hadamard. -/
/-
**Matrix.IsHadamard.kronecker** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {m : Type u_1} {n : Type u_2} {R : Type u_3} [inst : Fintype m] [inst_1 
: Fintype n] [inst_2 : DecidableEq m]   [inst_3 : DecidableEq n] [inst_4 : Semir
ing R] [inst_5 : StarRing R] {A : Matrix m m R} {B : Matrix n n R},   A.IsHadama
rd → B.IsHadamard → (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B).IsHadamard
参数：Matrix.kroneckerMap (fun x1 x2 => x1 * x2) A B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Matrix.IsHadamard.apply_mem`：∀ {n : Type u_2} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]   {
A : Matrix n n R}…
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_kronecker'`：conjTranspose_kronecker' [Mul R] [StarM
ul R] (x : Matrix l m R) (y : Matrix n p R) : (x otimesₖ y)ᴴ = (yᴴ otimesₖ xᴴ).s
ubmatrix Prod.swap Pr…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_irrel`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMon
oid M] (p : Prop) [inst_1 : Decidable p] (s : Finset ι) (f g : ι → M),   (∑ x ∈ 
s, if p th…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The Kronecker product of two Hadamard matrices is Hadamard.
-/
theorem IsHadamard.kronecker {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsHadamard) (hB : B.IsHadamard) : (A ⊗ₖ B).IsHadamard := by
  refine ⟨fun _ _ ↦ mul_mem (hA.apply_mem _ _) (hB.apply_mem _ _), ?_, ?_⟩ <;> ext ⟨i, i'⟩ ⟨j, j'⟩
  · calc
      _ = ∑ x₁, ∑ x₂, A i x₁ * (B i' x₂ * Bᴴ x₂ j') * Aᴴ x₁ j := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i' = j' then ∑ x, A i x * (Fintype.card n • Aᴴ) x j else 0 := by
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hB.mul_conjTranspose,
          one_apply, mul_assoc _ (Fintype.card n : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hA.mul_conjTranspose]
        simp [one_apply, ← Nat.cast_mul, mul_comm, ← ite_and, and_comm]
  · calc
      _ = ∑ x₁, ∑ x₂, Bᴴ i' x₂ * (Aᴴ i x₁ * A x₁ j) * B x₂ j' := by
        simp [conjTranspose_kronecker', mul_apply, mul_assoc, ← Finset.sum_product']
      _ = if i = j then ∑ x, Bᴴ i' x * (Fintype.card m • B) x j' else 0 := by
        rw [Finset.sum_comm]
        simp [← Finset.sum_mul, ← Finset.mul_sum, ← mul_apply, hA.conjTranspose_mul,
          one_apply, mul_assoc _ (Fintype.card m : R), -conjTranspose_apply]
      _ = _ := by
        simp only [← mul_apply, mul_smul_comm, hB.conjTranspose_mul]
        simp [one_apply, ← Nat.cast_mul, ← ite_and]

/-- A Hadamard matrix with constant column sum `s` has order `s * star s`, provided the order
is regular in `R`.

The row-sum form is `IsHadamard.card_eq_star_mul_of_const_row_sum`; over a ring with trivial
star the conclusion becomes `(Fintype.card n : R) = s ^ 2`, a slightly stronger form of
[Theorem 2.3.7][deLauneyFlannery2011]: only a constant sum hypothesis on one side is needed
under the two-sided orthogonality condition. -/
/-
**Matrix.IsHadamard.card_eq_mul_star_of_const_col_sum** 是 Mathlib 中的一个定理，位于命名空间 
`Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Semiring R] [inst_3 : StarRing R]   {A : Matrix n n R} {s : R},   A.
IsHadamard → IsRegular ↑(Fintype.card n) → (∀ (j : n), ∑ i, A i j = s) → ↑(Finty
pe.card n) = s * star s
参数：Fintype.card n；∀ (j : n), ∑ i, A i j = s；Fintype.card n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Matrix.vecMul_smul`：vecMul_smul [Fintype m] [DistribSMul R α] [SMulCommC
lass R α α] (v : m -> α) (b : R) (M : Matrix m n α) : v ᵥ* (b • M) = b • v ᵥ* M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `smul_dotProduct`：smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m 
-> α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecMul_one`：vecMul_one (v : m -> α) : v ᵥ* 1 = v
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.vecMul_vecMul`：vecMul_vecMul [Fintype n] [Fintype m] (v : m -> α)
 (M : Matrix m n α) (N : Matrix n o α) : v ᵥ* M ᵥ* N = v ᵥ* (M * N)
· 使用定理 `Matrix.dotProduct_mulVec`：dotProduct_mulVec [Fintype n] [Fintype m] [Non
UnitalSemiring R] (v : m -> R) (A : Matrix m n R) (w : n -> R) : v ⬝ᵥ A *ᵥ w = v
 ᵥ* A ⬝ᵥ w
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c

--- 原说明 ---
A Hadamard matrix with constant column sum `s` has order `s * star s`, provided 
the order
is regular in `R`.

The row-sum form is `IsHadamard.card_eq_star_mul_of_const_row_sum`; over a ring 
with trivial
star the conclusion becomes `(Fintype.card n : R) = s ^ 2`, a slightly stronger 
form of
[Theorem 2.3.7][deLauneyFlannery2011]: only a constant sum hypothesis on one sid
e is needed
under the two-sided orthogonality condition.
-/
theorem IsHadamard.card_eq_mul_star_of_const_col_sum {s : R}
    (hA : A.IsHadamard) (hcard : IsRegular (Fintype.card n : R))
    (hcol : ∀ j, ∑ i, A i j = s) : (Fintype.card n : R) = s * star s := by
  have hvcol : (1 : n → R) ᵥ* A = s • 1 := by
    ext j
    simpa [Matrix.vecMul, dotProduct] using hcol j
  have hconjcol : Aᴴ *ᵥ (1 : n → R) = star s • 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, ← star_sum, hcol i]
  have hleft : (1 : n → R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) ^ 2 := by
    rw [hA.mul_conjTranspose, Nat.cast_smul_eq_nsmul, vecMul_smul, smul_dotProduct]
    simp [dotProduct, pow_two]
  have hright : (1 : n → R) ᵥ* (A * Aᴴ) ⬝ᵥ 1 = (Fintype.card n : R) * (s * star s) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, hvcol, hconjcol]
    simp [dotProduct]
  exact hcard.left <| show (Fintype.card n : R) * (Fintype.card n : R) =
      (Fintype.card n : R) * (s * star s) by
    simpa [pow_two] using hleft.symm.trans hright

/-- A Hadamard matrix with constant row sum `s` has order `star s * s`, provided the order
is regular in `R`. This generalizes [Theorem 2.3.7][deLauneyFlannery2011]. -/
/-
**Matrix.IsHadamard.card_eq_star_mul_of_const_row_sum** 是 Mathlib 中的一个定理，位于命名空间 
`Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Semiring R] [inst_3 : StarRing R]   {A : Matrix n n R} {s : R},   A.
IsHadamard → IsRegular ↑(Fintype.card n) → (∀ (i : n), ∑ j, A i j = s) → ↑(Finty
pe.card n) = star s * s
参数：Fintype.card n；∀ (i : n), ∑ j, A i j = s；Fintype.card n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Matrix.IsHadamard.card_eq_mul_star_of_const_col_sum`：∀ {n : Type u_2} {R
 : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [
inst_3 : StarRing R]   {A : Matrix n n R}…
· 使用定理 `Matrix.IsHadamard.conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [inst :
 Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]
   {A : Matrix n n R}…

--- 原说明 ---
A Hadamard matrix with constant row sum `s` has order `star s * s`, provided the
 order
is regular in `R`. This generalizes [Theorem 2.3.7][deLauneyFlannery2011].
-/
theorem IsHadamard.card_eq_star_mul_of_const_row_sum {s : R}
    (hA : A.IsHadamard) (hcard : IsRegular (Fintype.card n : R))
    (hrow : ∀ i, ∑ j, A i j = s) : (Fintype.card n : R) = star s * s := by
  have hcol : ∀ j, ∑ i, Aᴴ i j = star s := fun j => by
    simp [conjTranspose_apply, ← star_sum, hrow j]
  simpa using hA.conjTranspose.card_eq_mul_star_of_const_col_sum hcard hcol

end Semiring

section CommSemiring
variable [CommSemiring R] [StarRing R] {A : Matrix n n R}

/-- The transpose of a Hadamard matrix is Hadamard.

Unlike `IsHadamard.conjTranspose` this requires commutativity: over a noncommutative ring the
transpose of a Hadamard matrix need not be Hadamard. -/
/-
**Matrix.IsHadamard.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommSemiring R]   [inst_3 : StarRing R] {A : Matrix n n R}, A.IsHada
mard → A.transpose.IsHadamard
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHadamard.apply_mem`：∀ {n : Type u_2} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]   {
A : Matrix n n R}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.conjTranspose_transpose_eq_transpose_conjTranspose`：conjTranspose
_transpose_eq_transpose_conjTranspose [Star α] (M : Matrix m n α) : Mᵀᴴ = Mᴴᵀ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.transpose_mul`：transpose_mul [AddCommMonoid α] [CommMagma α] [Fin
type n] (M : Matrix m n α) (N : Matrix n l α) : (M * N)ᵀ = Nᵀ * Mᵀ
· 使用定理 `Matrix.IsHadamard.conjTranspose_mul`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用定理 `Matrix.transpose_smul`：transpose_smul {R : Type*} [SMul R α] (c : R) (M 
: Matrix m n α) : (c • M)ᵀ = c • Mᵀ
· 使用定理 `Matrix.transpose_one`：transpose_one [DecidableEq n] [Zero α] [One α] : (
1 : Matrix n n α)ᵀ = 1
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…

--- 原说明 ---
The transpose of a Hadamard matrix is Hadamard.

Unlike `IsHadamard.conjTranspose` this requires commutativity: over a noncommuta
tive ring the
transpose of a Hadamard matrix need not be Hadamard.
-/
theorem IsHadamard.transpose (hA : A.IsHadamard) : Aᵀ.IsHadamard where
  apply_mem i j := hA.apply_mem j i
  mul_conjTranspose := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hA.conjTranspose_mul,
      transpose_smul, transpose_one]
  conjTranspose_mul := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hA.mul_conjTranspose,
      transpose_smul, transpose_one]

@[simp]
/-
**Matrix.isHadamard_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHadamard_transpose_iff : Aᵀ.IsHadamard ↔ A.IsHadamard
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHadamard.congr_simp`：∀ {n : Type u_2} {R : Type u_3} [inst : Fi
ntype n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Semiring 
R] [inst_4 : StarR…
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `Matrix.IsHadamard.transpose`：∀ {n : Type u_2} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : CommSemiring R]   [inst_3 : StarRing 
R] {A : Matrix n …
-/
theorem isHadamard_transpose_iff : Aᵀ.IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.transpose, (·.transpose)⟩

end CommSemiring

section Ring
variable [Ring R] [StarRing R] {A : Matrix n n R}

/-- Negating a Hadamard matrix gives a Hadamard matrix. -/
/-
**Matrix.IsHadamard.neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Ring R] [inst_3 : StarRing R]   {A : Matrix n n R}, A.IsHadamard → (
-A).IsHadamard
参数：-A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Matrix.conjTranspose_neg`：conjTranspose_neg [AddGroup α] [StarAddMonoid 
α] (M : Matrix m n α) : (-M)ᴴ = -Mᴴ

--- 原说明 ---
Negating a Hadamard matrix gives a Hadamard matrix.
-/
theorem IsHadamard.neg (hA : A.IsHadamard) : (-A).IsHadamard := by
  simpa [isHadamard_iff, Unitary.mem_iff] using hA

/-- A matrix is Hadamard iff its negation is. -/
@[simp]
/-
**Matrix.IsHadamard.neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Ring R] [inst_3 : StarRing R]   {A : Matrix n n R}, (-A).IsHadamard 
↔ A.IsHadamard
参数：-A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHadamard.congr_simp`：∀ {n : Type u_2} {R : Type u_3} [inst : Fi
ntype n] {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Semiring 
R] [inst_4 : StarR…
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Matrix.IsHadamard.neg`：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n
] [inst_1 : DecidableEq n] [inst_2 : Ring R] [inst_3 : StarRing R]   {A : Matrix
 n n R}, A.…

--- 原说明 ---
A matrix is Hadamard iff its negation is.
-/
theorem IsHadamard.neg_iff : (-A).IsHadamard ↔ A.IsHadamard :=
  ⟨fun hA => by simpa using hA.neg, (·.neg)⟩

end Ring

section CommRing
variable [CommRing R] [StarRing R] {A : Matrix n n R}

/-- The Hadamard determinant identity: `det A * star (det A) = (card n)^(card n)`. -/
/-
**Matrix.IsHadamard.det_mul_star_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamar
d`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommRing R] [inst_3 : StarRing R]   {A : Matrix n n R}, A.IsHadamard
 → A.det * star A.det = ↑(Fintype.card n) ^ Fintype.card n
参数：Fintype.card n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `Matrix.det_conjTranspose`：det_conjTranspose [StarRing R] (M : Matrix m m
 R) : det Mᴴ = star (det M)
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N

--- 原说明 ---
The Hadamard determinant identity: `det A * star (det A) = (card n)^(card n)`.
-/
theorem IsHadamard.det_mul_star_det (hA : A.IsHadamard) :
    A.det * star A.det = (Fintype.card n : R) ^ Fintype.card n := by
  have := congr_arg det hA.mul_conjTranspose
  rwa [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this

/-- The Hadamard determinant identity: `star (det A) * det A = (card n)^(card n)`. -/
/-
**Matrix.IsHadamard.star_det_mul_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamar
d`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommRing R] [inst_3 : StarRing R]   {A : Matrix n n R}, A.IsHadamard
 → star A.det * A.det = ↑(Fintype.card n) ^ Fintype.card n
参数：Fintype.card n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Matrix.IsHadamard.det_mul_star_det`：∀ {n : Type u_2} {R : Type u_3} [ins
t : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : StarRing
 R]   {A : Matrix n n R}…

--- 原说明 ---
The Hadamard determinant identity: `star (det A) * det A = (card n)^(card n)`.
-/
theorem IsHadamard.star_det_mul_det (hA : A.IsHadamard) :
    star A.det * A.det = (Fintype.card n : R) ^ Fintype.card n := by
  rw [mul_comm, hA.det_mul_star_det]

/-- A Hadamard matrix over a reduced commutative ring has nonzero determinant, provided the order
is nonzero in `R`. -/
/-
**Matrix.IsHadamard.det_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommRing R] [inst_3 : StarRing R]   {A : Matrix n n R} [IsReduced R]
, A.IsHadamard → ↑(Fintype.card n) ≠ 0 → A.det ≠ 0
参数：Fintype.card n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsHadamard.det_mul_star_det`：∀ {n : Type u_2} {R : Type u_3} [ins
t : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : StarRing
 R]   {A : Matrix n n R}…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
A Hadamard matrix over a reduced commutative ring has nonzero determinant, provi
ded the order
is nonzero in `R`.
-/
theorem IsHadamard.det_ne_zero [IsReduced R] (hA : A.IsHadamard)
    (hcard : (Fintype.card n : R) ≠ 0) : A.det ≠ 0 := fun h =>
  pow_ne_zero _ hcard <| by rw [← hA.det_mul_star_det, h, star_zero, zero_mul]

/-- The determinant of a Hadamard matrix is regular, provided the order is regular in `R`. -/
/-
**Matrix.IsHadamard.isRegular_det** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommRing R] [inst_3 : StarRing R]   {A : Matrix n n R}, A.IsHadamard
 → IsRegular ↑(Fintype.card n) → IsRegular A.det
参数：Fintype.card n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHadamard.det_mul_star_det`：∀ {n : Type u_2} {R : Type u_3} [ins
t : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : StarRing
 R]   {A : Matrix n n R}…
· 使用定理 `IsRegular.pow`：∀ {R : Type u_1} [inst : Monoid R] {a : R} (n : ℕ), IsReg
ular a → IsRegular (a ^ n)
· 使用定理 `IsRegular.of_mul_left`：IsRegular.of_mul_left (h : IsRegular (a * b)) : I
sRegular a

--- 原说明 ---
The determinant of a Hadamard matrix is regular, provided the order is regular i
n `R`.
-/
theorem IsHadamard.isRegular_det (hA : A.IsHadamard)
    (hcard : IsRegular (Fintype.card n : R)) : IsRegular A.det := by
  have : IsRegular (A.det * star A.det) := by
    rw [hA.det_mul_star_det]
    exact hcard.pow _
  exact this.of_mul_left

/-- Build a Hadamard matrix from the one-sided row-orthogonality condition, provided the order is
regular in `R`.

This is the matrix form of [Theorem 2.3.6][deLauneyFlannery2011]. -/
/-
**Matrix.IsHadamard.of_mul_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHad
amard`。
形式化陈述：∀ {n : Type u_2} {R : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : CommRing R] [inst_3 : StarRing R]   {A : Matrix n n R},   (∀ (i j : 
n), A i j ∈ unitary R) →     A * A.conjTranspose = ↑(Fintype.card n) • 1 → IsReg
ular ↑(Fintype.card n) → A.IsHadamard
参数：∀ (i j : n), A i j ∈ unitary R；Fintype.card n；Fintype.card n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.det_one`：det_one : det (1 : Matrix n n R) = 1
· 使用定理 `Matrix.det_smul`：det_smul (A : Matrix n n R) (c : R) : det (c • A) = c ^
 Fintype.card n * det A
· 使用定理 `Matrix.det_conjTranspose`：det_conjTranspose [StarRing R] (M : Matrix m m
 R) : det Mᴴ = star (det M)
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `IsRegular.pow`：∀ {R : Type u_1} [inst : Monoid R] {a : R} (n : ℕ), IsReg
ular a → IsRegular (a ^ n)
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `Matrix.isRegular_of_isLeftRegular_det`：isRegular_of_isLeftRegular_det {A
 : Matrix n n α} (hA : IsLeftRegular A.det) : IsRegular A
· 使用定理 `IsRegular.of_mul_left`：IsRegular.of_mul_left (h : IsRegular (a * b)) : I
sRegular a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
Build a Hadamard matrix from the one-sided row-orthogonality condition, provided
 the order is
regular in `R`.

This is the matrix form of [Theorem 2.3.6][deLauneyFlannery2011].
-/
theorem IsHadamard.of_mul_conjTranspose
    (hentry : ∀ i j, A i j ∈ unitary R)
    (hmul : A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R))
    (hcard : IsRegular (Fintype.card n : R)) : A.IsHadamard := by
  refine ⟨hentry, hmul, ?_⟩
  have hdet : IsRegular (A.det * star A.det) := by
    have := congr_arg det hmul
    rw [det_mul, det_conjTranspose, det_smul, det_one, mul_one] at this
    rw [this]
    exact hcard.pow _
  have hreg : IsLeftRegular A :=
    (isRegular_of_isLeftRegular_det hdet.of_mul_left.left).left
  exact hreg <| show A * (Aᴴ * A) = A * ((Fintype.card n : R) • 1) by
    rw [← mul_assoc, hmul, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
/-
**Matrix.isHadamard_iff_mul_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHadamard_iff_mul_conjTranspose (hcard : IsRegular (Fintype.card n : R)) 
: A.IsHadamard ↔ (forall i j, A i j in unitary R) ∧ A * Aᴴ = (Fintype.card n : R
) • (1 : Matrix n n R)
参数：hcard : IsRegular (Fintype.card n : R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsHadamard.apply_mem`：∀ {n : Type u_2} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]   {
A : Matrix n n R}…
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用定理 `Matrix.IsHadamard.of_mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} 
[inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : Star
Ring R]   {A : Matrix n n R}…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isHadamard_iff_mul_conjTranspose
    (hcard : IsRegular (Fintype.card n : R)) :
    A.IsHadamard ↔
      (∀ i j, A i j ∈ unitary R) ∧
        A * Aᴴ = (Fintype.card n : R) • (1 : Matrix n n R) :=
  ⟨fun hA => ⟨hA.apply_mem, hA.mul_conjTranspose⟩,
   fun hA => IsHadamard.of_mul_conjTranspose hA.1 hA.2 hcard⟩

end CommRing

/-- An integer Hadamard matrix of order greater than two has order divisible by four.

This is the standard divisibility obstruction in [Section 2.3][deLauneyFlannery2011]. -/
/-
**Matrix.IsHadamard.four_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHadamard`。
形式化陈述：∀ {n : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n] {A : Matrix n
 n ℤ},   A.IsHadamard → 2 < Fintype.card n → 4 ∣ Fintype.card n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Unitary.mem_iff_eq_one_or_eq_neg_one`：mem_iff_eq_one_or_eq_neg_one [Ring
 R] [StarRing R] [TrivialStar R] [NoZeroDivisors R] {a : R} : a in unitary R ↔ a
 = 1 ∨ a = -1
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Matrix.IsHadamard.apply_mem`：∀ {n : Type u_2} {R : Type u_3} [inst : Fin
type n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRing R]   {
A : Matrix n n R}…
· 使用定理 `Fintype.two_lt_card_iff`：∀ {α : Type u_1} [inst : Fintype α], 2 < Fintyp
e.card α ↔ ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.conjTranspose_eq_transpose_of_trivial`：conjTranspose_eq_transpose
_of_trivial [Star α] [TrivialStar α] (A : Matrix m n α) : Aᴴ = Aᵀ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Matrix.IsHadamard.mul_conjTranspose`：∀ {n : Type u_2} {R : Type u_3} [in
st : Fintype n] [inst_1 : DecidableEq n] [inst_2 : Semiring R] [inst_3 : StarRin
g R]   {A : Matrix n n R}…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
An integer Hadamard matrix of order greater than two has order divisible by four
.

This is the standard divisibility obstruction in [Section 2.3][deLauneyFlannery2
011].
-/
theorem IsHadamard.four_dvd_card {A : Matrix n n ℤ}
    (hA : A.IsHadamard) (hcard : 2 < Fintype.card n) : 4 ∣ Fintype.card n := by
  have hpm : ∀ i j, A i j = 1 ∨ A i j = -1 := fun i j =>
    Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
  obtain ⟨r, s, t, hrs, hrt, hst⟩ := Fintype.two_lt_card_iff.mp hcard
  have horth ⦃i k : n⦄ (hik : i ≠ k) : ∑ j, A i j * A k j = 0 := by
    simpa [Matrix.mul_apply, hik] using congr_fun (congr_fun hA.mul_conjTranspose i) k
  have hexpand : ∀ j, (1 + A s j * A r j) * (1 + A t j * A r j) =
      1 + A s j * A r j + A t j * A r j + A s j * A t j := fun j => by
    obtain hr | hr := hpm r j <;> simp [hr] <;> ring
  have hdvd : ∀ j, (4 : ℤ) ∣ (1 + A s j * A r j) * (1 + A t j * A r j) := fun j => by
    obtain hs | hs := hpm s j <;> obtain hr | hr := hpm r j <;>
      obtain ht | ht := hpm t j <;> simp [hs, hr, ht]
  have hsum : ∑ j, (1 + A s j * A r j) * (1 + A t j * A r j) = (Fintype.card n : ℤ) := by
    simp_rw [hexpand]
    simp [Finset.sum_add_distrib, horth hrs.symm, horth hrt.symm, horth hst]
  rw [← Int.ofNat_dvd, ← hsum]
  exact Finset.dvd_sum fun j _ => hdvd j

end Matrix

