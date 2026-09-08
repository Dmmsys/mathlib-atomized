/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Classification of elements of `GL (Fin 2) R`

Here we classify `2 × 2` matrices over the reals (or more generally over `R` where `R` is a
suitable ring, but `ℝ` is the motivating case), into the following classes:

* scalars
* parabolic elements (`Matrix.IsParabolic`) - one eigenvalue with non-semisimple generalized
  eigenspace
* hyperbolic elements (`Matrix.IsHyperbolic`) - two distinct real eigenvalues
* elliptic elements (`Matrix.IsElliptic`) - two distinct non-real complex eigenvalues

This classification is used (among other places) in classifying the fixed points of elements of
`GL(2, ℝ)⁺` acting on the upper half-plane. See [Wikipedia:SL2(R)#Classification_of_elements]
(https://en.wikipedia.org/wiki/SL2(R)#Classification_of_elements).
-/

@[expose] public section

open Polynomial

namespace Matrix

section CommRing

variable {R : Type*} [CommRing R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/-- A `2 × 2` matrix is *parabolic* if it is non-scalar and its discriminant is 0. -/
/-
**Matrix.IsParabolic** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsParabolic : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `2 × 2` matrix is *parabolic* if it is non-scalar and its discriminant is 0.
-/
def IsParabolic : Prop := m ∉ Set.range (scalar _) ∧ m.discr = 0

variable {m}

section conjugation

/-
**Matrix.isParabolic_conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {m : Matrix (Fin 2) (Fin 2) R} (g : G
L (Fin 2) R),   (↑g * m * (↑g)⁻¹).IsParabolic ↔ m.IsParabolic
参数：Fin 2；Fin 2；g : GL (Fin 2) R；↑g * m * (↑g)⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.discr_conj`：discr_conj (g : GL n R) (m : Matrix n n R) : (g.val *
 m * g.val⁻¹).discr = m.discr
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.smul_eq_mul_diagonal`：smul_eq_mul_diagonal [Fintype n] [Decidable
Eq n] (M : Matrix m n α) (a : α) : a • M = M * diagonal fun _ => a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isParabolic_conj_iff : (g.val * m * g.val⁻¹).IsParabolic ↔ IsParabolic m := by
  simp_rw [IsParabolic, discr_conj, Set.mem_range, ← Matrix.coe_units_inv,
    Units.eq_mul_inv_iff_mul_eq, scalar_apply, ← smul_eq_diagonal_mul, smul_eq_mul_diagonal,
    Units.mul_right_inj]
/-
**Matrix.isParabolic_conj'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {m : Matrix (Fin 2) (Fin 2) R} (g : G
L (Fin 2) R),   ((↑g)⁻¹ * m * ↑g).IsParabolic ↔ m.IsParabolic
参数：Fin 2；Fin 2；g : GL (Fin 2) R；(↑g)⁻¹ * m * ↑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.inv_inv_of_invertible`：inv_inv_of_invertible [Invertible A] : A⁻¹
⁻¹ = A
· 使用定理 `Matrix.isParabolic_conj_iff`：∀ {R : Type u_1} [inst : CommRing R] {m : M
atrix (Fin 2) (Fin 2) R} (g : GL (Fin 2) R),   (↑g * m * (↑g)⁻¹).IsParabolic ↔ m
.IsParabolic
-/
@[simp] lemma isParabolic_conj'_iff : (g.val⁻¹ * m * g.val).IsParabolic ↔ m.IsParabolic := by
  simpa using isParabolic_conj_iff g⁻¹
/-
**Matrix.IsParabolic.neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsParabolic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {m : Matrix (Fin 2) (Fin 2) R}, m.IsP
arabolic → (-m).IsParabolic
参数：Fin 2；Fin 2；-m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.coe_range`：coe_range : (f.range : Set S) = Set.range f
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.trace_neg`：trace_neg (A : Matrix n n R) : trace (-A) = -trace A
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsParabolic.neg (h : IsParabolic m) : IsParabolic (-m) := by
  constructor
  · rw [← RingHom.coe_range, SetLike.mem_coe, neg_mem_iff]
    exact h.1
  · -- TODO: prove `discr_neg` for a matrix of any size, use it here
    simpa [discr_fin_two, det_neg] using h.2
/-
**Matrix.IsParabolic.of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsParabolic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {m : Matrix (Fin 2) (Fin 2) R}, (-m).
IsParabolic → m.IsParabolic
参数：Fin 2；Fin 2；-m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Matrix.IsParabolic.neg`：∀ {R : Type u_1} [inst : CommRing R] {m : Matrix
 (Fin 2) (Fin 2) R}, m.IsParabolic → (-m).IsParabolic
-/
lemma IsParabolic.of_neg (h : IsParabolic (-m)) : IsParabolic m := by
  simpa using h.neg
/-
**Matrix.isParabolic_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {m : Matrix (Fin 2) (Fin 2) R}, (-m).
IsParabolic ↔ m.IsParabolic
参数：Fin 2；Fin 2；-m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsParabolic.of_neg`：∀ {R : Type u_1} [inst : CommRing R] {m : Mat
rix (Fin 2) (Fin 2) R}, (-m).IsParabolic → m.IsParabolic
· 使用定理 `Matrix.IsParabolic.neg`：∀ {R : Type u_1} [inst : CommRing R] {m : Matrix
 (Fin 2) (Fin 2) R}, m.IsParabolic → (-m).IsParabolic
-/
@[simp] lemma isParabolic_neg_iff : IsParabolic (-m) ↔ IsParabolic m := ⟨.of_neg, .neg⟩

end conjugation

/-
**Matrix.isParabolic_iff_of_upperTriangular** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isParabolic_iff_of_upperTriangular [IsReduced R] (hm : m 1 0 = 0) : m.IsPa
rabolic ↔ m 0 0 = m 1 1 ∧ m 0 1 != 0
参数：hm : m 1 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsParabolic.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (m : Matri
x (Fin 2) (Fin 2) R),   m.IsParabolic = (m ∉ Set.range ⇑(Matrix.scalar (Fin 2)) 
∧ m.discr = 0…
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
lemma isParabolic_iff_of_upperTriangular [IsReduced R] (hm : m 1 0 = 0) :
    m.IsParabolic ↔ m 0 0 = m 1 1 ∧ m 0 1 ≠ 0 := by
  rw [IsParabolic]
  have aux : m.discr = 0 ↔ m 0 0 = m 1 1 := by
    suffices m.discr = (m 0 0 - m 1 1) ^ 2 by
      rw [this, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    grind [discr_fin_two, trace_fin_two, det_fin_two]
  have (h : m 0 0 = m 1 1) : m ∈ Set.range (scalar _) ↔ m 0 1 = 0 := by
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro h'
      use m 1 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h', hm]
  tauto

end CommRing

section Field

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

/-
**Matrix.sub_scalar_sq_eq_discr** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：sub_scalar_sq_eq_discr [NeZero (2 : K)] : (m - scalar _ (m.trace / 2)) ^ 2
 = scalar _ (m.discr / 4)
参数：2 : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.diagonal_apply_eq`：diagonal_apply_eq [Zero α] (d : n -> α) (i : n
) : (diagonal d) i i = d i
· 使用定理 `Matrix.diagonal_apply_ne`：diagonal_apply_ne [Zero α] (d : n -> α) {i j :
 n} (h : i != j) : (diagonal d) i j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
（共 110 条，此处仅展示前 30 条）
-/
lemma sub_scalar_sq_eq_discr [NeZero (2 : K)] :
    (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.discr / 4) := by
  simp only [scalar_apply, trace_fin_two, discr_fin_two, trace_fin_two,
    det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field

variable (m) in
/-- The unique eigenvalue of a parabolic matrix (junk if `m` is not parabolic). -/
/-
**Matrix.parabolicEigenvalue** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：parabolicEigenvalue : K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique eigenvalue of a parabolic matrix (junk if `m` is not parabolic).
-/
def parabolicEigenvalue : K := m.trace / 2
/-
**Matrix.IsParabolic.sub_eigenvalue_sq_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
.IsParabolic`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {m : Matrix (Fin 2) (Fin 2) K} [NeZero 2
],   m.IsParabolic → (m - (Matrix.scalar (Fin 2)) m.parabolicEigenvalue) ^ 2 = 0
参数：Fin 2；Fin 2；m - (Matrix.scalar (Fin 2)) m.parabolicEigenvalue。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.sub_scalar_sq_eq_discr`：sub_scalar_sq_eq_discr [NeZero (2 : K)] :
 (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.discr / 4)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsParabolic.sub_eigenvalue_sq_eq_zero [NeZero (2 : K)] (hm : m.IsParabolic) :
    (m - scalar _ m.parabolicEigenvalue) ^ 2 = 0 := by
  simp [parabolicEigenvalue, -scalar_apply, sub_scalar_sq_eq_discr, hm.2]

/-- Characterization of parabolic elements: they have the form `a + m` where `a` is scalar and
`m` is nonzero and nilpotent. -/
/-
**Matrix.isParabolic_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isParabolic_iff_exists [NeZero (2 : K)] : m.IsParabolic ↔ exists a n, m = 
scalar _ a + n ∧ n != 0 ∧ n ^ 2 = 0
参数：2 : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Matrix.IsParabolic.sub_eigenvalue_sq_eq_zero`：∀ {K : Type u_1} [inst : F
ield K] {m : Matrix (Fin 2) (Fin 2) K} [NeZero 2],   m.IsParabolic → (m - (Matri
x.scalar (Fin 2)) m.parabolicEigen…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `Matrix.sub_scalar_sq_eq_discr`：sub_scalar_sq_eq_discr [NeZero (2 : K)] :
 (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.discr / 4)
· 使用定理 `Matrix.trace_add`：trace_add (A B : Matrix n n R) : trace (A + B) = trace
 A + trace B
· 使用定理 `Matrix.scalar_apply`：scalar_apply (a : α) : scalar n a = diagonal fun _ 
=> a
· 使用定理 `Matrix.trace_diagonal`：∀ {R : Type u_6} [inst : AddCommMonoid R] {o : Ty
pe u_8} [inst_1 : Fintype o] [inst_2 : DecidableEq o] (d : o → R),   (Matrix.dia
gonal d).tr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
Characterization of parabolic elements: they have the form `a + m` where `a` is 
scalar and
`m` is nonzero and nilpotent.
-/
lemma isParabolic_iff_exists [NeZero (2 : K)] :
    m.IsParabolic ↔ ∃ a n, m = scalar _ a + n ∧ n ≠ 0 ∧ n ^ 2 = 0 := by
  constructor
  · exact fun hm ↦ ⟨_, _, (add_sub_cancel ..).symm, sub_ne_zero.mpr fun h ↦ hm.1 ⟨_, h.symm⟩,
      hm.sub_eigenvalue_sq_eq_zero⟩
  · rintro ⟨a, n, hm, hn0, hnsq⟩
    constructor
    · refine fun ⟨b, hb⟩ ↦ hn0 ?_
      rw [← sub_eq_iff_eq_add'] at hm
      simpa only [← hm, ← hb, ← map_sub, ← map_pow, ← map_zero (scalar (Fin 2)), scalar_inj,
        sq_eq_zero_iff] using hnsq
    · suffices scalar (Fin 2) (m.discr / 4) = 0 by
        rw [← map_zero (scalar (Fin 2)), scalar_inj, div_eq_zero_iff] at this
        have : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using NeZero.ne _
        tauto
      rw [← sub_scalar_sq_eq_discr, hm, trace_add, scalar_apply, trace_diagonal]
      simp [mul_div_cancel_left₀ _ (NeZero.ne (2 : K)),
        (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, hnsq⟩).eq_zero, hnsq]

end Field

section Preorder

variable {R : Type*} [CommRing R] [Preorder R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/-- A `2 × 2` matrix is *hyperbolic* if its discriminant is strictly positive. -/
/-
**Matrix.IsHyperbolic** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsHyperbolic : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `2 × 2` matrix is *hyperbolic* if its discriminant is strictly positive.
-/
def IsHyperbolic : Prop := 0 < m.discr

/-- A `2 × 2` matrix is *elliptic* if its discriminant is strictly negative. -/
/-
**Matrix.IsElliptic** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：IsElliptic : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `2 × 2` matrix is *elliptic* if its discriminant is strictly negative.
-/
def IsElliptic : Prop := m.discr < 0

variable {m}
/-
**Matrix.isHyperbolic_conj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isHyperbolic_conj_iff : (g.val * m * g.val⁻¹).IsHyperbolic ↔ m.IsHyperboli
c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.discr_conj`：discr_conj (g : GL n R) (m : Matrix n n R) : (g.val *
 m * g.val⁻¹).discr = m.discr
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isHyperbolic_conj_iff : (g.val * m * g.val⁻¹).IsHyperbolic ↔ m.IsHyperbolic := by
  simp [IsHyperbolic]
/-
**Matrix.isHyperbolic_conj'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : Preorder R] {m : Matrix (Fi
n 2) (Fin 2) R} (g : GL (Fin 2) R),   ((↑g)⁻¹ * m * ↑g).IsHyperbolic ↔ m.IsHyper
bolic
参数：Fin 2；Fin 2；g : GL (Fin 2) R；(↑g)⁻¹ * m * ↑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.inv_inv_of_invertible`：inv_inv_of_invertible [Invertible A] : A⁻¹
⁻¹ = A
· 使用引理 `Matrix.isHyperbolic_conj_iff`：isHyperbolic_conj_iff : (g.val * m * g.val
⁻¹).IsHyperbolic ↔ m.IsHyperbolic
-/
lemma isHyperbolic_conj'_iff : (g.val⁻¹ * m * g.val).IsHyperbolic ↔ m.IsHyperbolic := by
  simpa using isHyperbolic_conj_iff g⁻¹
/-
**Matrix.isElliptic_conj_iff** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：isElliptic_conj_iff : (g.val * m * g.val⁻¹).IsElliptic ↔ m.IsElliptic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.discr_conj`：discr_conj (g : GL n R) (m : Matrix n n R) : (g.val *
 m * g.val⁻¹).discr = m.discr
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isElliptic_conj_iff : (g.val * m * g.val⁻¹).IsElliptic ↔ m.IsElliptic := by
  simp [IsElliptic]
/-
**Matrix.isElliptic_conj'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : Preorder R] {m : Matrix (Fi
n 2) (Fin 2) R} (g : GL (Fin 2) R),   ((↑g)⁻¹ * m * ↑g).IsElliptic ↔ m.IsEllipti
c
参数：Fin 2；Fin 2；g : GL (Fin 2) R；(↑g)⁻¹ * m * ↑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.inv_inv_of_invertible`：inv_inv_of_invertible [Invertible A] : A⁻¹
⁻¹ = A
· 使用引理 `Matrix.isElliptic_conj_iff`：isElliptic_conj_iff : (g.val * m * g.val⁻¹).
IsElliptic ↔ m.IsElliptic
-/
lemma isElliptic_conj'_iff : (g.val⁻¹ * m * g.val).IsElliptic ↔ m.IsElliptic := by
  simpa using isElliptic_conj_iff g⁻¹

@[simp]
/-
**Matrix.isHyperbolic_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isHyperbolic_neg_iff : (-m).IsHyperbolic ↔ m.IsHyperbolic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.trace_neg`：trace_neg (A : Matrix n n R) : trace (-A) = -trace A
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isHyperbolic_neg_iff : (-m).IsHyperbolic ↔ m.IsHyperbolic := by
  simp [IsHyperbolic, discr_fin_two, det_neg]

protected alias ⟨IsHyperbolic.of_neg, IsHyperbolic.neg⟩ := isHyperbolic_neg_iff

@[simp]
/-
**Matrix.isElliptic_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isElliptic_neg_iff : (-m).IsElliptic ↔ m.IsElliptic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `Matrix.trace_neg`：trace_neg (A : Matrix n n R) : trace (-A) = -trace A
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isElliptic_neg_iff : (-m).IsElliptic ↔ m.IsElliptic := by
  simp [IsElliptic, discr_fin_two, det_neg]

protected alias ⟨IsElliptic.of_neg, IsElliptic.neg⟩ := isElliptic_neg_iff

end Preorder

section LinearOrder

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R] {m : Matrix (Fin 2) (Fin 2) R}

/-
**Matrix.IsElliptic.bc_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsElliptic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : LinearOrder R] [IsOrderedRi
ng R] {m : Matrix (Fin 2) (Fin 2) R},   m.IsElliptic → m 0 1 * m 1 0 ≠ 0
参数：Fin 2；Fin 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Matrix.trace_fin_two`：trace_fin_two (A : Matrix (Fin 2) (Fin 2) R) : tra
ce A = A 0 0 + A 1 1
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `Matrix.IsElliptic.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : P
reorder R] (m : Matrix (Fin 2) (Fin 2) R), m.IsElliptic = (m.discr < 0)
· 使用定理 `Mathlib.Tactic.LinearCombination.le_of_le`：le_of_le [AddCommMonoid α] [P
artialOrder α] [IsOrderedCancelAddMonoid α] (p : (a : α) <= b) (H : a' + b <= b'
 + a) : a' <= b'
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Mathlib.Tactic.LinearCombination.le_rearrange`：le_rearrange {α : Type*} 
[AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b : α} (h : a - b <=
 0) : a <= b
· 使用定理 `Mathlib.Tactic.Ring.le_congr`：le_congr {α : Type*} [LE α] {a b c d : α} 
(h1 : a = b) (h2 : b <= c) (h3 : d = c) : a <= d
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 66 条，此处仅展示前 30 条）
-/
theorem IsElliptic.bc_ne_zero (hm : m.IsElliptic) : m 0 1 * m 1 0 ≠ 0 := by
  intro hc
  rw [IsElliptic, discr_fin_two, trace_fin_two, det_fin_two, hc] at hm
  refine hm.not_ge ?_
  linear_combination sq_nonneg (m 0 0 - m 1 1)
/-
**Matrix.IsElliptic.b_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsElliptic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : LinearOrder R] [IsOrderedRi
ng R] {m : Matrix (Fin 2) (Fin 2) R},   m.IsElliptic → m 0 1 ≠ 0
参数：Fin 2；Fin 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.IsElliptic.bc_ne_zero`：∀ {R : Type u_1} [inst : CommRing R] [inst
_1 : LinearOrder R] [IsOrderedRing R] {m : Matrix (Fin 2) (Fin 2) R},   m.IsElli
ptic → m 0 1 * m 1…
-/
theorem IsElliptic.b_ne_zero (hm : m.IsElliptic) : m 0 1 ≠ 0 :=
  left_ne_zero_of_mul hm.bc_ne_zero
/-
**Matrix.IsElliptic.c_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsElliptic`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : LinearOrder R] [IsOrderedRi
ng R] {m : Matrix (Fin 2) (Fin 2) R},   m.IsElliptic → m 1 0 ≠ 0
参数：Fin 2；Fin 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.IsElliptic.bc_ne_zero`：∀ {R : Type u_1} [inst : CommRing R] [inst
_1 : LinearOrder R] [IsOrderedRing R] {m : Matrix (Fin 2) (Fin 2) R},   m.IsElli
ptic → m 0 1 * m 1…
-/
theorem IsElliptic.c_ne_zero (hm : m.IsElliptic) : m 1 0 ≠ 0 :=
  right_ne_zero_of_mul hm.bc_ne_zero

end LinearOrder

namespace GeneralLinearGroup

section Ring

variable {R : Type*} [Ring R]

/-- The map sending `x` to `[1, x; 0, 1]` (bundled as an `AddChar`). -/
@[simps apply]
/-
**Matrix.GeneralLinearGroup.upperRightHom** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Gene
ralLinearGroup`。
形式化陈述：upperRightHom : AddChar R (GL (Fin 2) R) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map sending `x` to `[1, x; 0, 1]` (bundled as an `AddChar`).
-/
def upperRightHom : AddChar R (GL (Fin 2) R) where
  toFun x := ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  map_zero_eq_one' := by simp [Units.ext_iff, one_fin_two]
  map_add_eq_mul' a b := by simp [Units.ext_iff, add_comm]
/-
**Matrix.GeneralLinearGroup.injective_upperRightHom** 是 Mathlib 中的一个引理，位于命名空间 `M
atrix.GeneralLinearGroup`。
形式化陈述：injective_upperRightHom : Function.Injective (upperRightHom (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.upperRightHom_apply`：∀ {R : Type u_1} [inst : 
Ring R] (x : R),   Matrix.GeneralLinearGroup.upperRightHom x =     { val := !![1
, x; 0, 1], inv := !![1, -x; 0, 1],…
· 使用定理 `Matrix.one_fin_two`：one_fin_two : (1 : Matrix (Fin 2) (Fin 2) α) = !![1,
 0; 0, 1]
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma injective_upperRightHom : Function.Injective (upperRightHom (R := R)) := by
  refine (injective_iff_map_eq_zero (upperRightHom (R := R)).toAddMonoidHom).mpr ?_
  simp [Units.ext_iff, one_fin_two]

end Ring

variable {R K : Type*} [CommRing R] [Field K]

/-- Synonym of `Matrix.IsParabolic`, for dot-notation. -/
/-
**Matrix.GeneralLinearGroup.IsParabolic** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix.Gene
ralLinearGroup`。
形式化陈述：IsParabolic (g : GL (Fin 2) R) : Prop
参数：g : GL (Fin 2) R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Synonym of `Matrix.IsParabolic`, for dot-notation.
-/
abbrev IsParabolic (g : GL (Fin 2) R) : Prop := g.val.IsParabolic
/-
**Matrix.GeneralLinearGroup.isParabolic_conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matr
ix.GeneralLinearGroup`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (g h : GL (Fin 2) R), (g * h * g⁻¹).I
sParabolic ↔ h.IsParabolic
参数：g h : GL (Fin 2) R；g * h * g⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isParabolic_conj_iff (g h : GL (Fin 2) R) :
    IsParabolic (g * h * g⁻¹) ↔ IsParabolic h := by
  simp [IsParabolic]
/-
**Matrix.GeneralLinearGroup.isParabolic_conj_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Mat
rix.GeneralLinearGroup`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (g h : GL (Fin 2) R), (g⁻¹ * h * g).I
sParabolic ↔ h.IsParabolic
参数：g h : GL (Fin 2) R；g⁻¹ * h * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isParabolic_conj_iff' (g h : GL (Fin 2) R) :
    IsParabolic (g⁻¹ * h * g) ↔ IsParabolic h := by
  simp [IsParabolic]

/-- Synonym of `Matrix.IsElliptic`, for dot-notation. -/
/-
**Matrix.GeneralLinearGroup.IsElliptic** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix.Gener
alLinearGroup`。
形式化陈述：IsElliptic [Preorder R] (g : GL (Fin 2) R) : Prop
参数：g : GL (Fin 2) R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Synonym of `Matrix.IsElliptic`, for dot-notation.
-/
abbrev IsElliptic [Preorder R] (g : GL (Fin 2) R) : Prop := g.val.IsElliptic

/-- Synonym of `Matrix.IsHyperbolic`, for dot-notation. -/
/-
**Matrix.GeneralLinearGroup.IsHyperbolic** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix.Gen
eralLinearGroup`。
形式化陈述：IsHyperbolic [Preorder R] (g : GL (Fin 2) R) : Prop
参数：g : GL (Fin 2) R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Synonym of `Matrix.IsHyperbolic`, for dot-notation.
-/
abbrev IsHyperbolic [Preorder R] (g : GL (Fin 2) R) : Prop := g.val.IsHyperbolic

/-- Polynomial whose roots are the fixed points of `g` considered as a Möbius transformation.

See `Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff`. -/
/-
**Matrix.GeneralLinearGroup.fixpointPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `Matrix
.GeneralLinearGroup`。
形式化陈述：fixpointPolynomial (g : GL (Fin 2) R) : R[X]
参数：g : GL (Fin 2) R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Polynomial whose roots are the fixed points of `g` considered as a Möbius transf
ormation.

See `Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff`.
-/
noncomputable def fixpointPolynomial (g : GL (Fin 2) R) : R[X] :=
  C (g 1 0) * X ^ 2 + C (g 1 1 - g 0 0) * X - C (g 0 1)

/-- The fixed-point polynomial is identically zero iff `g` is scalar. -/
/-
**Matrix.GeneralLinearGroup.fixpointPolynomial_eq_zero_iff** 是 Mathlib 中的一个引理，位于
命名空间 `Matrix.GeneralLinearGroup`。
形式化陈述：fixpointPolynomial_eq_zero_iff {g : GL (Fin 2) R} : g.fixpointPolynomial =
 0 ↔ g.val in Set.range (Matrix.scalar _)
参数：Fin 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.fixpointPolynomial.eq_1`：∀ {R : Type u_1} [ins
t : CommRing R] (g : GL (Fin 2) R),   g.fixpointPolynomial =     Polynomial.C (↑
g 1 0) * Polynomial.X ^ 2 + Polynomial.…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The fixed-point polynomial is identically zero iff `g` is scalar.
-/
lemma fixpointPolynomial_eq_zero_iff {g : GL (Fin 2) R} :
    g.fixpointPolynomial = 0 ↔ g.val ∈ Set.range (Matrix.scalar _) := by
  rw [fixpointPolynomial]
  constructor
  · refine fun hP ↦ ⟨g 0 0, ?_⟩
    have hb : g 0 1 = 0 := by simpa using congr_arg (coeff · 0) hP
    have hc : g 1 0 = 0 := by simpa using congr_arg (coeff · 2) hP
    have hd : g 1 1 = g 0 0 := by simpa [sub_eq_zero] using congr_arg (coeff · 1) hP
    ext i j
    fin_cases i <;>
    fin_cases j <;>
    simp [hb, hc, hd]
  · rintro ⟨a, ha⟩
    simp [← ha]
/-
**Matrix.GeneralLinearGroup.parabolicEigenvalue_ne_zero** 是 Mathlib 中的一个引理，位于命名空
间 `Matrix.GeneralLinearGroup`。
形式化陈述：parabolicEigenvalue_ne_zero {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : IsPa
rabolic g) : g.val.parabolicEigenvalue != 0
参数：Fin 2；2 : K；hg : IsParabolic g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.discr_fin_two`：discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) : A.d
iscr = A.trace ^ 2 - 4 * A.det
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.parabolicEigenvalue.eq_1`：∀ {K : Type u_1} [inst : Field K] (m : 
Matrix (Fin 2) (Fin 2) K), m.parabolicEigenvalue = m.trace / 2
· 使用定理 `div_ne_zero_iff`：div_ne_zero_iff : a / b != 0 ↔ a != 0 ∧ b != 0
· 使用引理 `eq_true_intro`：eq_true_intro {a : Prop} (h : a) : a = True
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_zero_iff`：sq_eq_zero_iff : a ^ 2 = 0 ↔ a = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
lemma parabolicEigenvalue_ne_zero {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : IsParabolic g) :
    g.val.parabolicEigenvalue ≠ 0 := by
  have : g.val.trace ^ 2 = 4 * g.val.det := by simpa [sub_eq_zero, discr_fin_two] using hg.2
  rw [parabolicEigenvalue, div_ne_zero_iff, eq_true_intro (two_ne_zero' K), and_true,
    Ne, ← sq_eq_zero_iff, this, show (4 : K) = 2 ^ 2 by norm_num, mul_eq_zero,
    sq_eq_zero_iff, not_or]
  exact ⟨NeZero.ne _, g.det_ne_zero⟩

/-- A non-zero power of a parabolic element is parabolic. -/
/-
**Matrix.GeneralLinearGroup.IsParabolic.pow** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Ge
neralLinearGroup.IsParabolic`。
形式化陈述：∀ {K : Type u_2} [inst : Field K] {g : GL (Fin 2) K},   g.IsParabolic → ∀ 
[CharZero K] {n : ℕ}, n ≠ 0 → (g ^ n).IsParabolic
参数：Fin 2；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.GeneralLinearGroup.IsParabolic.eq_1`：∀ {R : Type u_1} [inst : Com
mRing R] (g : GL (Fin 2) R), g.IsParabolic = (↑g).IsParabolic
· 使用引理 `Matrix.isParabolic_iff_exists`：isParabolic_iff_exists [NeZero (2 : K)] :
 m.IsParabolic ↔ exists a n, m = scalar _ a + n ∧ n != 0 ∧ n ^ 2 = 0
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Matrix.smul_mul`：smul_mul [Fintype n] [Monoid R] [DistribMulAction R α] 
[IsScalarTower R α α] (a : R) (M : Matrix m n α) (N : Matrix n l α) : (a • M) * 
N = a…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
A non-zero power of a parabolic element is parabolic.
-/
lemma IsParabolic.pow {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
    {n : ℕ} (hn : n ≠ 0) : IsParabolic (g ^ n) := by
  rw [IsParabolic, isParabolic_iff_exists] at hg ⊢
  obtain ⟨a, m, hg, hm0, hmsq⟩ := hg
  refine ⟨a ^ n, (n * a ^ (n - 1)) • m, ?_, ?_, by simp [smul_pow, hmsq]⟩
  · rw [Units.val_pow_eq_pow_val, hg]
    rw [← Nat.one_le_iff_ne_zero] at hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn IH =>
      simp only [pow_succ, IH, add_mul, Nat.add_sub_cancel, mul_add, ← map_mul, add_assoc]
      simp only [scalar_apply, ← smul_eq_mul_diagonal, ← mul_smul,
        ← smul_eq_diagonal_mul, smul_mul, ← sq, hmsq, smul_zero, add_zero, ← add_smul,
        Nat.cast_add_one, add_mul, one_mul]
      rw [(by lia : n = n - 1 + 1), pow_succ, (by lia : n - 1 + 1 = n)]
      ring_nf
  · suffices a ≠ 0 by simp [this, hm0, hn]
    refine fun ha ↦ (g ^ 2).det_ne_zero ?_
    rw [ha, map_zero, zero_add] at hg
    rw [← hg] at hmsq
    rw [Units.val_pow_eq_pow_val, hmsq, det_zero]
/-
**Matrix.GeneralLinearGroup.isParabolic_iff_of_upperTriangular** 是 Mathlib 中的一个引
理，位于命名空间 `Matrix.GeneralLinearGroup`。
形式化陈述：isParabolic_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) : g
.IsParabolic ↔ g 0 0 = g 1 1 ∧ g 0 1 != 0
参数：Fin 2；hg : g 1 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Matrix.isParabolic_iff_of_upperTriangular`：isParabolic_iff_of_upperTrian
gular [IsReduced R] (hm : m 1 0 = 0) : m.IsParabolic ↔ m 0 0 = m 1 1 ∧ m 0 1 != 
0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma isParabolic_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) :
    g.IsParabolic ↔ g 0 0 = g 1 1 ∧ g 0 1 ≠ 0 :=
  Matrix.isParabolic_iff_of_upperTriangular hg

/-- Specialized version of `isParabolic_iff_of_upperTriangular` intended for use with
discrete subgroups of `GL(2, ℝ)`. -/
/-
**Matrix.GeneralLinearGroup.isParabolic_iff_of_upperTriangular_of_det** 是 Mathli
b 中的一个引理，位于命名空间 `Matrix.GeneralLinearGroup`。
形式化陈述：isParabolic_iff_of_upperTriangular_of_det [LinearOrder K] [IsStrictOrdered
Ring K] {g : GL (Fin 2) K} (h_det : g.det = 1 ∨ g.det = -1) (hg10 : g 1 0 = 0) :
 g.IsParabolic ↔ (exists x != 0, g = upperRightHom x) ∨ (exists x != (0 : K), g 
= -upperRightHom x)
参数：Fin 2；h_det : g.det = 1 ∨ g.det = -1；hg10 : g 1 0 = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.GeneralLinearGroup.isParabolic_iff_of_upperTriangular`：isParaboli
c_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) : g.IsParabolic ↔ g
 0 0 = g 1 1 ∧ g 0 1 != 0
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
Specialized version of `isParabolic_iff_of_upperTriangular` intended for use wit
h
discrete subgroups of `GL(2, ℝ)`.
-/
lemma isParabolic_iff_of_upperTriangular_of_det [LinearOrder K] [IsStrictOrderedRing K]
    {g : GL (Fin 2) K} (h_det : g.det = 1 ∨ g.det = -1) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (∃ x ≠ 0, g = upperRightHom x) ∨ (∃ x ≠ (0 : K), g = -upperRightHom x) := by
  rw [isParabolic_iff_of_upperTriangular hg10]
  constructor
  · rintro ⟨hg00, hg01⟩
    have : g 1 1 ^ 2 = 1 := by
      have : g.det = g 1 1 ^ 2 := by rw [val_det_apply, det_fin_two, hg10, hg00]; ring
      simp only [Units.ext_iff, Units.val_one, Units.val_neg, this] at h_det
      exact h_det.resolve_right (neg_one_lt_zero.trans_le <| sq_nonneg _).ne'
    apply (sq_eq_one_iff.mp this).imp <;> intro hg11 <;> simp only [Units.ext_iff]
    · refine ⟨g 0 1, hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
    · refine ⟨-g 0 1, neg_eq_zero.not.mpr hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;>
    simpa using hx

end GeneralLinearGroup

end Matrix

