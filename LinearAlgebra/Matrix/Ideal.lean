/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Wojciech Nawrocki
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.GroupTheory.Congruence.BigOperators
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Ideals in a matrix ring

This file defines left (resp. two-sided) ideals in a matrix semiring (resp. ring)
over left (resp. two-sided) ideals in the base semiring (resp. ring).
We also characterize Jacobson radicals of ideals in such rings.

## Main results

* `TwoSidedIdeal.equivMatrix` and `TwoSidedIdeal.orderIsoMatrix`
  establish an order isomorphism between two-sided ideals in $R$ and those in $Mₙ(R)$.
* `TwoSidedIdeal.jacobson_matrix` shows that $J(Mₙ(I)) = Mₙ(J(I))$
  for any two-sided ideal $I ≤ R$.
-/

@[expose] public section

/-! ### Left ideals in a matrix semiring -/

namespace Ideal
open Matrix

variable {R : Type*} [Semiring R]
         (n : Type*) [Fintype n] [DecidableEq n]

/-- The left ideal of matrices with entries in `I ≤ R`. -/
/-
**Ideal.matrix** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：matrix (I : Ideal R) : Ideal (Matrix n n R) where __
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left ideal of matrices with entries in `I ≤ R`.
-/
def matrix (I : Ideal R) : Ideal (Matrix n n R) where
  __ := I.toAddSubmonoid.matrix
  smul_mem' M N hN := by
    intro i j
    rw [smul_eq_mul, mul_apply]
    apply sum_mem
    intro k _
    apply I.mul_mem_left _ (hN k j)

@[simp]
/-
**Ideal.mem_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_matrix (I : Ideal R) (M : Matrix n n R) : M in I.matrix n ↔ forall i j
, M i j in I
参数：I : Ideal R；M : Matrix n n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_matrix (I : Ideal R) (M : Matrix n n R) :
    M ∈ I.matrix n ↔ ∀ i j, M i j ∈ I := by rfl
/-
**Ideal.matrix_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：matrix_monotone : Monotone (matrix (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem matrix_monotone : Monotone (matrix (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)
/-
**Ideal.matrix_strictMono_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：matrix_strictMono_of_nonempty [Nonempty n] : StrictMono (matrix (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `Ideal.matrix_monotone`：matrix_monotone : Monotone (matrix (R
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem matrix_strictMono_of_nonempty [Nonempty n] :
    StrictMono (matrix (R := R) n) :=
  matrix_monotone n |>.strictMono_of_injective <| fun I J eq => by
    ext x
    have : (∀ _ _, x ∈ I) ↔ (∀ _ _, x ∈ J) := congr((Matrix.of fun _ _ => x) ∈ $eq)
    simpa only [forall_const] using this

@[simp]
/-
**Ideal.matrix_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：matrix_bot : (⊥ : Ideal R).matrix n = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem matrix_bot : (⊥ : Ideal R).matrix n = ⊥ := by
  ext M
  simp only [mem_matrix, mem_bot]
  constructor
  · intro H; ext; apply H
  · intro H; simp [H]

@[simp]
/-
**Ideal.matrix_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：matrix_top : (⊤ : Ideal R).matrix n = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem matrix_top : (⊤ : Ideal R).matrix n = ⊤ := by
  ext; simp

end Ideal

/-! ### Jacobson radicals of left ideals in a matrix ring -/

namespace Ideal
open Matrix

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

/-- A standard basis matrix is in $J(Mₙ(I))$
as long as its one possibly non-zero entry is in $J(I)$. -/
/-
**Ideal.single_mem_jacobson_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：single_mem_jacobson_matrix (I : Ideal R) : forall x in I.jacobson, forall 
(i j : n), single i j x in (I.matrix n).jacobson
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `Matrix.sum_apply`：sum_apply [AddCommMonoid α] (i : m) (j : n) (s : Finse
t β) (g : β -> Matrix m n α) : (∑ c in s, g c) i j = ∑ c in s, g c i j
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
A standard basis matrix is in $J(Mₙ(I))$
as long as its one possibly non-zero entry is in $J(I)$.
-/
theorem single_mem_jacobson_matrix (I : Ideal R) :
    ∀ x ∈ I.jacobson, ∀ (i j : n), single i j x ∈ (I.matrix n).jacobson := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  simp_rw [Ideal.mem_jacobson_iff]
  intro x xIJ p q M
  have ⟨z, zMx⟩ := xIJ (M q p)
  let N : Matrix n n R := 1 - ∑ i, single i q (if i = q then 1 - z else (M i p) * x * z)
  use N
  intro i j
  obtain rfl | qj := eq_or_ne q j
  · by_cases iq : i = q
    · simp [iq, N, zMx, single, mul_apply, sum_apply, ite_and, sub_mul]
    · convert! I.mul_mem_left (-M i p * x) zMx
      simp [iq, N, single, mul_apply, sum_apply, ite_and, sub_mul]
      simp [sub_add, mul_add, mul_sub, mul_assoc]
  · simp [N, qj, sum_apply, mul_apply]

/-- For any left ideal $I ≤ R$, we have $Mₙ(J(I)) ≤ J(Mₙ(I))$. -/
/-
**Ideal.matrix_jacobson_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：matrix_jacobson_le (I : Ideal R) : I.jacobson.matrix n <= (I.matrix n).jac
obson
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.matrix_eq_sum_single`：matrix_eq_sum_single [AddCommMonoid α] [Fin
type m] [Fintype n] (x : Matrix m n α) : x = ∑ i : m, ∑ j : n, single i j (x i j
)
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Ideal.single_mem_jacobson_matrix`：single_mem_jacobson_matrix (I : Ideal 
R) : forall x in I.jacobson, forall (i j : n), single i j x in (I.matrix n).jaco
bson

--- 原说明 ---
For any left ideal $I ≤ R$, we have $Mₙ(J(I)) ≤ J(Mₙ(I))$.
-/
theorem matrix_jacobson_le (I : Ideal R) :
    I.jacobson.matrix n ≤ (I.matrix n).jacobson := by
  intro M MI
  rw [matrix_eq_sum_single M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  apply single_mem_jacobson_matrix I _ (MI i j)

end Ideal

/-! ### Two-sided ideals in a matrix ring -/

namespace RingCon
variable {R n : Type*}

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R] [Fintype n]
variable (n)

/-- The ring congruence of matrices with entries related by `c`. -/
/-
**RingCon.matrix** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：matrix (c : RingCon R) : RingCon (Matrix n n R) where r M N
参数：c : RingCon R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring congruence of matrices with entries related by `c`.
-/
def matrix (c : RingCon R) : RingCon (Matrix n n R) where
  r M N := ∀ i j, c (M i j) (N i j)
  -- note: kept `fun` to distinguish `RingCon`'s binders from `r`'s binders.
  iseqv.refl _ := fun _ _ ↦ c.refl _
  iseqv.symm h := fun _ _ ↦ c.symm <| h _ _
  iseqv.trans h₁ h₂ := fun _ _ ↦ c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ ↦ c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun _ _ ↦ c.finsetSum _ fun _ _ => c.mul (h₁ _ _) (h₂ _ _)

@[simp low]
/-
**RingCon.matrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_apply {c : RingCon R} {M N : Matrix n n R} : c.matrix n M N ↔ foral
l i j, c (M i j) (N i j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem matrix_apply {c : RingCon R} {M N : Matrix n n R} :
    c.matrix n M N ↔ ∀ i j, c (M i j) (N i j) :=
  Iff.rfl

@[simp]
/-
**RingCon.matrix_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_apply_single [DecidableEq n] {c : RingCon R} {i j : n} {x y : R} : 
c.matrix n (Matrix.single i j x) (Matrix.single i j y) ↔ c x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem matrix_apply_single [DecidableEq n] {c : RingCon R} {i j : n} {x y : R} :
    c.matrix n (Matrix.single i j x) (Matrix.single i j y) ↔ c x y := by
  refine ⟨fun h ↦ by simpa using h i j, fun h i' j' ↦ ?_⟩
  obtain hi | rfl := ne_or_eq i i'
  · simpa [hi] using c.refl 0
  obtain hj | rfl := ne_or_eq j j'
  · simpa [hj] using c.refl _
  simpa using h
/-
**RingCon.matrix_monotone** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_monotone : Monotone (matrix (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem matrix_monotone : Monotone (matrix (R := R) n) :=
  fun _ _ hc _ _ h _ _ ↦ hc (h _ _)
/-
**RingCon.matrix_injective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_injective [Nonempty n] : Function.Injective (matrix (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext`：ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c =
 d
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem matrix_injective [Nonempty n] : Function.Injective (matrix (R := R) n) :=
  fun I J eq ↦ RingCon.ext fun r s ↦ by
    have := congr_fun (DFunLike.congr_fun eq (Matrix.of fun _ _ ↦ r)) (Matrix.of fun _ _ ↦ s)
    simpa using this
/-
**RingCon.matrix_strictMono_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_strictMono_of_nonempty [Nonempty n] : StrictMono (matrix (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `RingCon.matrix_monotone`：matrix_monotone : Monotone (matrix (R
· 使用定理 `RingCon.matrix_injective`：matrix_injective [Nonempty n] : Function.Injec
tive (matrix (R
-/
theorem matrix_strictMono_of_nonempty [Nonempty n] :
    StrictMono (matrix (R := R) n) :=
  matrix_monotone n |>.strictMono_of_injective <| matrix_injective _

@[simp]
/-
**RingCon.matrix_bot** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_bot : (⊥ : RingCon R).matrix n = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
-/
theorem matrix_bot : (⊥ : RingCon R).matrix n = ⊥ :=
  eq_bot_iff.2 fun _ _ h ↦ Matrix.ext h

@[simp]
/-
**RingCon.matrix_top** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_top : (⊤ : RingCon R).matrix n = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
-/
theorem matrix_top : (⊤ : RingCon R).matrix n = ⊤ :=
  eq_top_iff.2 fun _ _ _ _ _ ↦ by simp

open Matrix

variable {n}

/-- The congruence relation induced by `c` on `single i j`. -/
/-
**RingCon.ofMatrix** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) : RingCon R where r 
x y
参数：c : RingCon (Matrix n n R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruence relation induced by `c` on `single i j`.
-/
def ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) : RingCon R where
  r x y := ∀ i j, c (single i j x) (single i j y)
  iseqv.refl _ := fun _ _ ↦ c.refl _
  iseqv.symm h := fun _ _ ↦ c.symm <| h _ _
  iseqv.trans h₁ h₂ := fun _ _ ↦ c.trans (h₁ _ _) (h₂ _ _)
  add' h₁ h₂ := fun _ _ ↦ by simpa [single_add] using c.add (h₁ _ _) (h₂ _ _)
  mul' h₁ h₂ := fun i j ↦ by simpa using c.mul (h₁ i i) (h₂ i j)

@[simp]
/-
**RingCon.ofMatrix_rel** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ofMatrix_rel [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} : ofMa
trix c x y ↔ forall i j, c (single i j x) (single i j y)
参数：Matrix n n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofMatrix_rel [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} :
    ofMatrix c x y ↔ ∀ i j, c (single i j x) (single i j y) :=
  Iff.rfl
/-
**RingCon.ofMatrix_matrix** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} {n : Type u_2} [inst : NonUnitalNonAssocSemiring R] [inst
_1 : Fintype n] [inst_2 : DecidableEq n]   [Nonempty n] (c : RingCon R), (RingCo
n.matrix n c).ofMatrix = c
参数：c : RingCon R；RingCon.matrix n c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext`：ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c =
 d
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `RingCon.matrix_apply_single`：matrix_apply_single [DecidableEq n] {c : Ri
ngCon R} {i j : n} {x y : R} : c.matrix n (Matrix.single i j x) (Matrix.single i
 j y) ↔ c x y
-/
@[simp] theorem ofMatrix_matrix [DecidableEq n] [Nonempty n] (c : RingCon R) :
    ofMatrix (matrix n c) = c := by
  ext x y
  constructor
  · intro h
    inhabit n
    simpa using h default default default default
  · intro h i j
    rwa [matrix_apply_single]

end NonUnitalNonAssocSemiring

section NonAssocSemiring
variable [NonAssocSemiring R] [Fintype n]
open Matrix

/-- Note that this does not apply to a non-unital ring, with counterexample where the elementwise
congruence relation `!![⊤,⊤;⊤,(· ≡ · [PMOD 4])]` is a ring congruence over
`Matrix (Fin 2) (Fin 2) 2ℤ`. -/
@[simp]
/-
**RingCon.matrix_ofMatrix** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：matrix_ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) : matrix n (o
fMatrix c) = c
参数：c : RingCon (Matrix n n R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext`：ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c =
 d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.matrix_eq_sum_single`：matrix_eq_sum_single [AddCommMonoid α] [Fin
type m] [Fintype n] (x : Matrix m n α) : x = ∑ i : m, ∑ j : n, single i j (x i j
)
· 使用定理 `AddCon.finsetSum`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCommMonoid 
M] (c : AddCon M) (s : Finset ι) {f g : ι → M},   (∀ i ∈ s, c (f i) (g i)) → c (
s.sum …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.single_mul_mul_single`：single_mul_mul_single [Fintype n] (i : l) 
(i' : m) (j' : n) (j : o) (a : α) (x : Matrix m n α) (b : α) : single i i' a * x
 * single j' j b =…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RingCon.mul`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w * y) (x * z)
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x

--- 原说明 ---
Note that this does not apply to a non-unital ring, with counterexample where th
e elementwise
congruence relation `!![⊤,⊤;⊤,(· ≡ · [PMOD 4])]` is a ring congruence over
`Matrix (Fin 2) (Fin 2) 2ℤ`.
-/
theorem matrix_ofMatrix [DecidableEq n] (c : RingCon (Matrix n n R)) :
    matrix n (ofMatrix c) = c := by
  ext x y
  constructor
  · intro h
    rw [matrix_eq_sum_single x, matrix_eq_sum_single y]
    refine c.finsetSum _ fun i _ ↦ c.finsetSum _ fun j _ ↦ h i j i j
  · intro h i' j' i j
    simpa using c.mul (c.mul (c.refl <| single i i' 1) h) (c.refl <| single j' j 1)

/-- A version of `ofMatrix_rel` for a single matrix index, rather than all indices. -/
/-
**RingCon.ofMatrix_rel'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ofMatrix_rel' [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} (i j 
: n) : ofMatrix c x y ↔ c (single i j x) (single i j y)
参数：Matrix n n R；i j : n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.single_mul_single_same`：single_mul_single_same (i : l) (j : m) (k
 : n) (d : α) : single i j c * single j k d = single i k (c * d)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RingCon.mul`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w * y) (x * z)
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x

--- 原说明 ---
A version of `ofMatrix_rel` for a single matrix index, rather than all indices.
-/
theorem ofMatrix_rel' [DecidableEq n] {c : RingCon (Matrix n n R)} {x y : R} (i j : n) :
    ofMatrix c x y ↔ c (single i j x) (single i j y) := by
  refine ⟨fun h ↦ h i j, fun h i' j' ↦ ?_⟩
  simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)
/-
**RingCon.coe_ofMatrix_eq_relationMap** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_ofMatrix_eq_relationMap [DecidableEq n] {c : RingCon (Matrix n n R)} (
i j : n) : ⇑(ofMatrix c) = Relation.Map c (· i j) (· i j)
参数：Matrix n n R；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Matrix.single_mul_mul_single`：single_mul_mul_single [Fintype n] (i : l) 
(i' : m) (j' : n) (j : o) (a : α) (x : Matrix m n α) (b : α) : single i i' a * x
 * single j' j b =…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RingCon.mul`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingC
on R) {w x y z : R}, c w x → c y z → c (w * y) (x * z)
· 使用定理 `RingCon.refl`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : Ring
Con R) (x : R), c x x
-/
theorem coe_ofMatrix_eq_relationMap [DecidableEq n] {c : RingCon (Matrix n n R)} (i j : n) :
    ⇑(ofMatrix c) = Relation.Map c (· i j) (· i j) := by
  ext x y
  constructor
  · intro h
    refine ⟨_,_, h i j, ?_⟩
    simp
  · rintro ⟨X, Y, h, rfl, rfl⟩ i' j'
    simpa using c.mul (c.mul (c.refl <| single i' i 1) h) (c.refl <| single j j' 1)

end NonAssocSemiring

end RingCon

namespace TwoSidedIdeal
open Matrix

variable {R : Type*} (n : Type*)

section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R] [Fintype n]

/-- The two-sided ideal of matrices with entries in `I ≤ R`. -/
@[simps]
/-
**TwoSidedIdeal.matrix** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：matrix (I : TwoSidedIdeal R) : TwoSidedIdeal (Matrix n n R) where ringCon
参数：I : TwoSidedIdeal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The two-sided ideal of matrices with entries in `I ≤ R`.
-/
def matrix (I : TwoSidedIdeal R) : TwoSidedIdeal (Matrix n n R) where
  ringCon := I.ringCon.matrix n

@[simp]
/-
**TwoSidedIdeal.mem_matrix** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：mem_matrix (I : TwoSidedIdeal R) (M : Matrix n n R) : M in I.matrix n ↔ fo
rall i j, M i j in I
参数：I : TwoSidedIdeal R；M : Matrix n n R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_matrix (I : TwoSidedIdeal R) (M : Matrix n n R) :
    M ∈ I.matrix n ↔ ∀ i j, M i j ∈ I := Iff.rfl
/-
**TwoSidedIdeal.matrix_monotone** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：matrix_monotone : Monotone (matrix (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem matrix_monotone : Monotone (matrix (R := R) n) :=
  fun _ _ IJ _ MI i j => IJ (MI i j)
/-
**TwoSidedIdeal.matrix_strictMono_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `TwoSide
dIdeal`。
形式化陈述：matrix_strictMono_of_nonempty [h : Nonempty n] : StrictMono (matrix (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `TwoSidedIdeal.matrix_monotone`：matrix_monotone : Monotone (matrix (R
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `TwoSidedIdeal.ofRingCon.inj`：∀ {R : Type u_1} {inst : NonUnitalNonAssocR
ing R} {ringCon ringCon_1 : RingCon R},   { ringCon := ringCon } = { ringCon := 
ringCon_1 } → rin…
· 使用定理 `RingCon.matrix_injective`：matrix_injective [Nonempty n] : Function.Injec
tive (matrix (R
· 使用引理 `TwoSidedIdeal.ringCon_injective`：ringCon_injective : Function.Injective 
(TwoSidedIdeal.ringCon (R
-/
theorem matrix_strictMono_of_nonempty [h : Nonempty n] :
    StrictMono (matrix (R := R) n) :=
  matrix_monotone n |>.strictMono_of_injective <|
    .comp (fun _ _ => ofRingCon.inj) <| (RingCon.matrix_injective n).comp ringCon_injective

@[simp]
/-
**TwoSidedIdeal.matrix_bot** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：matrix_bot : (⊥ : TwoSidedIdeal R).matrix n = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.ringCon_injective`：ringCon_injective : Function.Injective 
(TwoSidedIdeal.ringCon (R
· 使用定理 `RingCon.matrix_bot`：matrix_bot : (⊥ : RingCon R).matrix n = ⊥
-/
theorem matrix_bot : (⊥ : TwoSidedIdeal R).matrix n = ⊥ :=
  ringCon_injective <| RingCon.matrix_bot _

@[simp]
/-
**TwoSidedIdeal.matrix_top** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：matrix_top : (⊤ : TwoSidedIdeal R).matrix n = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.ringCon_injective`：ringCon_injective : Function.Injective 
(TwoSidedIdeal.ringCon (R
· 使用定理 `RingCon.matrix_top`：matrix_top : (⊤ : RingCon R).matrix n = ⊤
-/
theorem matrix_top : (⊤ : TwoSidedIdeal R).matrix n = ⊤ :=
  ringCon_injective <| RingCon.matrix_top _

end NonUnitalNonAssocRing

section NonAssocRing
variable [NonAssocRing R] [Fintype n] [Nonempty n] [DecidableEq n]

variable {n}

/--
Two-sided ideals in $R$ correspond bijectively to those in $Mₙ(R)$.
Given an ideal $I ≤ R$, we send it to $Mₙ(I)$.
Given an ideal $J ≤ Mₙ(R)$, we send it to $\{Nᵢⱼ ∣ ∃ N ∈ J\}$.
-/
@[simps]
/-
**TwoSidedIdeal.equivMatrix** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：equivMatrix : TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix n n R) where toFun I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two-sided ideals in $R$ correspond bijectively to those in $Mₙ(R)$.
Given an ideal $I ≤ R$, we send it to $Mₙ(I)$.
Given an ideal $J ≤ Mₙ(R)$, we send it to $\{Nᵢⱼ ∣ ∃ N ∈ J\}$.
-/
def equivMatrix : TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix n n R) where
  toFun I := I.matrix n
  invFun J := { ringCon := J.ringCon.ofMatrix }
  right_inv _ := ringCon_injective <| RingCon.matrix_ofMatrix _
  left_inv _ := ringCon_injective <| RingCon.ofMatrix_matrix _
/-
**TwoSidedIdeal.coe_equivMatrix_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedId
eal`。
形式化陈述：coe_equivMatrix_symm_apply (I : TwoSidedIdeal (Matrix n n R)) (i j : n) : 
equivMatrix.symm I = {N i j | N in I}
参数：I : TwoSidedIdeal (Matrix n n R)；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.single_zero`：single_zero (i : m) (j : n) : single i j (0 : α) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用定理 `TwoSidedIdeal.equivMatrix_symm_apply_ringCon`：∀ {R : Type u_1} {n : Type
 u_2} [inst : NonAssocRing R] [inst_1 : Fintype n] [inst_2 : Nonempty n]   [inst
_3 : DecidableEq n] (J : TwoSidedI…
· 使用定理 `RingCon.coe_ofMatrix_eq_relationMap`：coe_ofMatrix_eq_relationMap [Decida
bleEq n] {c : RingCon (Matrix n n R)} (i j : n) : ⇑(ofMatrix c) = Relation.Map c
 (· i j) (· i j)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem coe_equivMatrix_symm_apply (I : TwoSidedIdeal (Matrix n n R)) (i j : n) :
    equivMatrix.symm I = {N i j | N ∈ I} := by
  ext r
  constructor
  · intro h
    exact ⟨single i j r, by simpa using! h i j, by simp⟩
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, mem_iff, equivMatrix_symm_apply_ringCon,
      RingCon.coe_ofMatrix_eq_relationMap i j]
    exact ⟨n, 0, (I.mem_iff n).mp hn, rfl, rfl⟩

/--
Two-sided ideals in $R$ are order-isomorphic with those in $Mₙ(R)$.
See also `equivMatrix`.
-/
@[simps!]
/-
**TwoSidedIdeal.orderIsoMatrix** 是 Mathlib 中的一个定义，位于命名空间 `TwoSidedIdeal`。
形式化陈述：orderIsoMatrix : TwoSidedIdeal R ≃o TwoSidedIdeal (Matrix n n R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two-sided ideals in $R$ are order-isomorphic with those in $Mₙ(R)$.
See also `equivMatrix`.
-/
def orderIsoMatrix : TwoSidedIdeal R ≃o TwoSidedIdeal (Matrix n n R) where
  __ := equivMatrix
  map_rel_iff' {I J} := by
    simp only [equivMatrix_apply]
    constructor
    · intro le x xI
      specialize @le (of fun _ _ => x) (by simp [xI])
      simpa using le
    · intro IJ M MI i j
      exact IJ <| MI i j

end NonAssocRing

section Ring
variable [Ring R] [Fintype n]

/-
**TwoSidedIdeal.asIdeal_matrix** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：asIdeal_matrix [DecidableEq n] (I : TwoSidedIdeal R) : asIdeal (I.matrix n
) = (asIdeal I).matrix n
参数：I : TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem asIdeal_matrix [DecidableEq n] (I : TwoSidedIdeal R) :
    asIdeal (I.matrix n) = (asIdeal I).matrix n := by
  ext; simp

end Ring

end TwoSidedIdeal

/-! ### Jacobson radicals of two-sided ideals in a matrix ring -/

namespace TwoSidedIdeal
open Matrix

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

/-
**TwoSidedIdeal.jacobson_matrix_le** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobson_matrix_le (I : TwoSidedIdeal R) :
    (I.matrix n).jacobson ≤ I.jacobson.matrix n := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  intro M Mmem p q
  simp only [zero_apply, ← mem_iff]
  rw [mem_jacobson_iff]
  replace Mmem := mul_mem_right _ _ (single q p 1) Mmem
  rw [mem_jacobson_iff] at Mmem
  intro y
  specialize Mmem (y • single p p 1)
  have ⟨N, NxMI⟩ := Mmem
  use N p p
  simpa [mul_apply, single, ite_and] using! NxMI p p

/-- For any two-sided ideal $I ≤ R$, we have $J(Mₙ(I)) = Mₙ(J(I))$. -/
/-
**TwoSidedIdeal.jacobson_matrix** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：jacobson_matrix (I : TwoSidedIdeal R) : (I.matrix n).jacobson = I.jacobson
.matrix n
参数：I : TwoSidedIdeal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `_private.Mathlib.LinearAlgebra.Matrix.Ideal.0.TwoSidedIdeal.jacobson_mat
rix_le`：∀ {R : Type u_1} [inst : Ring R] {n : Type u_2} [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (I : TwoSidedIdeal R),   (TwoSidedIdeal.matrix…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.asIdeal_jacobson`：asIdeal_jacobson (I : TwoSidedIdeal R) :
 asIdeal I.jacobson = (asIdeal I).jacobson
· 使用定理 `TwoSidedIdeal.asIdeal_matrix`：asIdeal_matrix [DecidableEq n] (I : TwoSid
edIdeal R) : asIdeal (I.matrix n) = (asIdeal I).matrix n

--- 原说明 ---
For any two-sided ideal $I ≤ R$, we have $J(Mₙ(I)) = Mₙ(J(I))$.
-/
theorem jacobson_matrix (I : TwoSidedIdeal R) :
    (I.matrix n).jacobson = I.jacobson.matrix n := by
  apply le_antisymm
  · apply jacobson_matrix_le
  · change asIdeal (I.matrix n).jacobson ≥ asIdeal (I.jacobson.matrix n)
    simp [asIdeal_jacobson, asIdeal_matrix, Ideal.matrix_jacobson_le]
/-
**TwoSidedIdeal.matrix_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：matrix_jacobson_bot : (⊥ : TwoSidedIdeal R).jacobson.matrix n = (⊥ : TwoSi
dedIdeal (Matrix n n R)).jacobson
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TwoSidedIdeal.jacobson_matrix`：jacobson_matrix (I : TwoSidedIdeal R) : (
I.matrix n).jacobson = I.jacobson.matrix n
· 使用定理 `TwoSidedIdeal.matrix_bot`：matrix_bot : (⊥ : TwoSidedIdeal R).matrix n = 
⊥
-/
theorem matrix_jacobson_bot :
    (⊥ : TwoSidedIdeal R).jacobson.matrix n = (⊥ : TwoSidedIdeal (Matrix n n R)).jacobson :=
  matrix_bot n (R := R) ▸ (jacobson_matrix _).symm

end TwoSidedIdeal

