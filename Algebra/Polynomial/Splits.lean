/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Chris Hughes
-/
module

public import Mathlib.Algebra.Order.SuccPred.WithBot
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Split polynomials

A polynomial `f : R[X]` splits if it is a product of constant and monic linear polynomials.

## Main definitions

* `Polynomial.Splits f`: A predicate on a polynomial `f` saying that `f` is a product of
  constant and monic linear polynomials.

-/

@[expose] public section

variable {R : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/-- A polynomial `Splits` if it is a product of constant and monic linear polynomials. -/
/-
**Polynomial.Splits** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：Splits (f : R[X]) : Prop
参数：f : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polynomial `Splits` if it is a product of constant and monic linear polynomial
s.
-/
def Splits (f : R[X]) : Prop := f ∈ Submonoid.closure ({C a | a : R} ∪ {X + C a | a : R})

@[simp, aesop safe apply]
/-
**Polynomial.Splits.C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Polynomial.C a).Splits
参数：a : R；Polynomial.C a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_closure_of_mem`：mem_closure_of_mem {s : Set M} {x : M} (hx
 : x in s) : x in closure s
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
-/
protected theorem Splits.C (a : R) : Splits (C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_left _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
/-
**Polynomial.Splits.zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], Polynomial.Splits 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.Splits.C`：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Poly
nomial.C a).Splits
-/
protected theorem Splits.zero : Splits (0 : R[X]) := by
  simpa using Splits.C (0 : R)

@[simp, aesop safe apply]
/-
**Polynomial.Splits.one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], Polynomial.Splits 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.C`：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Poly
nomial.C a).Splits
-/
protected theorem Splits.one : Splits (1 : R[X]) :=
  Splits.C (1 : R)

@[simp, aesop safe apply]
/-
**Polynomial.Splits.X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Polynomial.X + Polynomial.C
 a).Splits
参数：a : R；Polynomial.X + Polynomial.C a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_closure_of_mem`：mem_closure_of_mem {s : Set M} {x : M} (hx
 : x in s) : x in closure s
· 使用定理 `Set.mem_union_right`：mem_union_right {x : α} {b : Set α} (a : Set α) : x
 in b -> x in a union b
-/
theorem Splits.X_add_C (a : R) : Splits (X + C a) :=
  Submonoid.mem_closure_of_mem (Set.mem_union_right _ ⟨a, rfl⟩)

@[simp, aesop safe apply]
/-
**Polynomial.Splits.X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R], Polynomial.X.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.Splits.X_add_C`：∀ {R : Type u_1} [inst : Semiring R] (a : R),
 (Polynomial.X + Polynomial.C a).Splits
-/
protected theorem Splits.X : Splits (X : R[X]) := by
  simpa using Splits.X_add_C (0 : R)

@[simp, aesop safe apply]
/-
**Polynomial.Splits.mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f g : Polynomial R}, f.Splits → g.Sp
lits → (f * g).Splits
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
protected theorem Splits.mul {f g : R[X]} (hf : Splits f) (hg : Splits g) :
    Splits (f * g) :=
  mul_mem hf hg
/-
**Polynomial.Splits.C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.Splits → ∀ (a :
 R), (Polynomial.C a * f).Splits
参数：a : R；Polynomial.C a * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.C`：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Poly
nomial.C a).Splits
-/
protected theorem Splits.C_mul {f : R[X]} (hf : Splits f) (a : R) : Splits (C a * f) :=
  (Splits.C a).mul hf

@[simp, aesop safe apply]
/-
**Polynomial.Splits.listProd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {l : List (Polynomial R)}, (∀ f ∈ l, 
f.Splits) → l.prod.Splits
参数：Polynomial R；∀ f ∈ l, f.Splits。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem Splits.listProd {l : List R[X]} (h : ∀ f ∈ l, Splits f) : Splits l.prod :=
  list_prod_mem h

@[simp, aesop safe apply]
/-
**Polynomial.Splits.pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.Splits → ∀ (n :
 ℕ), (f ^ n).Splits
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
protected theorem Splits.pow {f : R[X]} (hf : Splits f) (n : ℕ) : Splits (f ^ n) :=
  pow_mem hf n
/-
**Polynomial.Splits.X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), (Polynomial.X ^ n).Splits
参数：n : ℕ；Polynomial.X ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.pow`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R}, f.Splits → ∀ (n : ℕ), (f ^ n).Splits
· 使用定理 `Polynomial.Splits.X`：∀ {R : Type u_1} [inst : Semiring R], Polynomial.X.
Splits
-/
theorem Splits.X_pow (n : ℕ) : Splits (X ^ n : R[X]) :=
  Splits.X.pow n
/-
**Polynomial.Splits.C_mul_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (a : R) (n : ℕ), (Polynomial.C a * Po
lynomial.X ^ n).Splits
参数：a : R；n : ℕ；Polynomial.C a * Polynomial.X ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.C_mul`：∀ {R : Type u_1} [inst : Semiring R] {f : Polyn
omial R}, f.Splits → ∀ (a : R), (Polynomial.C a * f).Splits
· 使用定理 `Polynomial.Splits.X_pow`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), (
Polynomial.X ^ n).Splits
-/
theorem Splits.C_mul_X_pow (a : R) (n : ℕ) : Splits (C a * X ^ n) :=
  (Splits.X_pow n).C_mul a

@[simp, aesop safe apply]
/-
**Polynomial.Splits.monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ) (a : R), ((Polynomial.monomia
l n) a).Splits
参数：n : ℕ；a : R；(Polynomial.monomial n) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Splits.monomial (n : ℕ) (a : R) : Splits (monomial n a) := by
  simp [← C_mul_X_pow_eq_monomial]
/-
**Polynomial.Splits.map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R},   f.Splits → ∀ {S
 : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Polynomial.map i f).Splits
参数：i : R →+* S；Polynomial.map i f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
-/
protected theorem Splits.map {f : R[X]} (hf : Splits f) {S : Type*} [Semiring S] (i : R →+* S) :
    Splits (map i f) := by
  induction hf using Submonoid.closure_induction <;> aesop
/-
**Polynomial.Splits.of_natDegree_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.S
plits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.natDegree = 0 →
 f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Splits.of_natDegree_eq_zero {f : R[X]} (hf : natDegree f = 0) :
    Splits f := by
  rw [← (natDegree_eq_zero.mp hf).choose_spec]; aesop

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_eq_zero := Splits.of_natDegree_eq_zero
/-
**Polynomial.Splits.of_degree_le_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Spli
ts`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.degree ≤ 0 → f.
Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_eq_zero`：∀ {R : Type u_1} [inst : Semirin
g R] {f : Polynomial R}, f.natDegree = 0 → f.Splits
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
-/
theorem Splits.of_degree_le_zero {f : R[X]} (hf : degree f ≤ 0) :
    Splits f :=
  .of_natDegree_eq_zero (natDegree_eq_zero_iff_degree_le_zero.mpr hf)

@[deprecated (since := "2026-06-06")] alias splits_of_degree_le_zero := Splits.of_degree_le_zero
/-
**Polynomial._root_.IsUnit.splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsUnit.splits [NoZeroDivisors R] {f : R[X]} (hf : IsUnit f) : Splits f :=
  .of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hf)
/-
**Polynomial.Splits.of_natDegree_le_one_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 →
 ∀ (h : Invertible f.leadingCoeff), f.Splits
参数：h : Invertible f.leadingCoeff。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_eq_X_add_C_of_natDegree_le_one`：exists_eq_X_add_C_of_n
atDegree_le_one (h : natDegree p <= 1) : exists a b, p = C a * X + C b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_C_mul_X`：natDegree_C_mul_X (a : R) (ha : a != 0) : 
natDegree (C a * X) = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_invOf_cancel_left`：mul_invOf_cancel_left [Invertible a] : a * (⅟a * 
b) = b
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.C`：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Poly
nomial.C a).Splits
· 使用定理 `Polynomial.Splits.X_add_C`：∀ {R : Type u_1} [inst : Semiring R] (a : R),
 (Polynomial.X + Polynomial.C a).Splits
-/
theorem Splits.of_natDegree_le_one_of_invertible {f : R[X]}
    (hf : f.natDegree ≤ 1) (h : Invertible f.leadingCoeff) : f.Splits := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · replace h : Invertible a := by simpa [leadingCoeff, ha] using h
    rw [← mul_invOf_cancel_left a b, C_mul, ← mul_add]
    exact (Splits.C a).mul (Splits.X_add_C _)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_invertible := Splits.of_natDegree_le_one_of_invertible
/-
**Polynomial.Splits.of_degree_le_one_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.degree ≤ 1 → ∀ 
(h : Invertible f.leadingCoeff), f.Splits
参数：h : Invertible f.leadingCoeff。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_le_one_of_invertible`：∀ {R : Type u_1} [i
nst : Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → ∀ (h : Invertible f.lead
ingCoeff), f.Splits
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem Splits.of_degree_le_one_of_invertible {f : R[X]}
    (hf : f.degree ≤ 1) (h : Invertible f.leadingCoeff) : f.Splits :=
  .of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_invertible := Splits.of_degree_le_one_of_invertible
/-
**Polynomial.Splits.of_natDegree_le_one_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 →
 f.Monic → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_le_one_of_invertible`：∀ {R : Type u_1} [i
nst : Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → ∀ (h : Invertible f.lead
ingCoeff), f.Splits
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
-/
theorem Splits.of_natDegree_le_one_of_monic {f : R[X]} (hf : f.natDegree ≤ 1) (h : Monic f) :
    f.Splits :=
  .of_natDegree_le_one_of_invertible hf (h.leadingCoeff ▸ invertibleOne)

@[deprecated (since := "2026-06-06")]
alias splits_of_natDegree_le_one_of_monic := Splits.of_natDegree_le_one_of_monic
/-
**Polynomial.Splits.of_degree_le_one_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {f : Polynomial R}, f.degree ≤ 1 → f.
Monic → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_le_one_of_monic`：∀ {R : Type u_1} [inst :
 Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → f.Monic → f.Splits
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem Splits.of_degree_le_one_of_monic {f : R[X]} (hf : f.degree ≤ 1) (h : Monic f) :
    f.Splits :=
  .of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hf) h

@[deprecated (since := "2026-06-06")]
alias splits_of_degree_le_one_of_monic := Splits.of_degree_le_one_of_monic

end Semiring

section CommSemiring

variable [CommSemiring R]

@[simp, aesop safe apply]
/-
**Polynomial.Splits.multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {m : Multiset (Polynomial R)}, (∀
 f ∈ m, f.Splits) → m.prod.Splits
参数：Polynomial R；∀ f ∈ m, f.Splits。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem Splits.multisetProd {m : Multiset R[X]} (hm : ∀ f ∈ m, Splits f) : Splits m.prod :=
  multiset_prod_mem _ hm

@[simp, aesop safe apply]
/-
**Polynomial.Splits.prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Type u_2} {f : ι → Polynomia
l R} {s : Finset ι},   (∀ i ∈ s, (f i).Splits) → (∏ i ∈ s, f i).Splits
参数：∀ i ∈ s, (f i).Splits；∏ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
protected theorem Splits.prod {ι : Type*} {f : ι → R[X]} {s : Finset ι}
    (h : ∀ i ∈ s, Splits (f i)) : Splits (∏ i ∈ s, f i) :=
  prod_mem h
/-
**Polynomial.Splits.taylor** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {p : Polynomial R}, p.Splits → ∀ 
(r : R), ((Polynomial.taylor r) p).Splits
参数：r : R；(Polynomial.taylor r) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.Splits.X_add_C`：∀ {R : Type u_1} [inst : Semiring R] (a : R),
 (Polynomial.X + Polynomial.C a).Splits
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.taylor_C`：taylor_C (x : R) : taylor r (C x) = C x
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.taylor_X`：taylor_X : taylor r X = X + C r
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Polynomial.taylor_one`：taylor_one : taylor r (1 : R[X]) = C 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.taylor_mul`：taylor_mul (p q : R[X]) : taylor r (p * q) = tayl
or r p * taylor r q
-/
lemma Splits.taylor {p : R[X]} (hp : p.Splits) (r : R) : (p.taylor r).Splits := by
  have (i : _) : (X + C r + C i).Splits := by simpa [add_assoc] using Splits.X_add_C (r + i)
  induction hp using Submonoid.closure_induction <;> aesop

/-- See `splits_iff_exists_multiset` for the version with subtraction. -/
/-
**Polynomial.splits_iff_exists_multiset'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_iff_exists_multiset' {f : R[X]} : Splits f ↔ exists m : Multiset R,
 f = C f.leadingCoeff * (m.map (X + C ·)).prod
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MonoidHom.coe_mrange`：coe_mrange (f : F) : (mrange f : Set N) = Set.rang
e f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.mem_sup`：mem_sup {s t : Submonoid N} {x : N} : x in s ⊔ t ↔ ex
ists y in s, exists z in t, y * z = x
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用定理 `Polynomial.Splits.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Polyno
mial R),   f.Splits = (f ∈ Submonoid.closure ({x | ∃ a, Polynomial.C a = x} ∪ {x
 | ∃ a, Poly…
· 使用定理 `Submonoid.exists_multiset_of_mem_closure`：exists_multiset_of_mem_closure
 {M : Type*} [CommMonoid M] {s : Set M} {x : M} (hx : x in closure s) : exists l
 : Multiset M, (forall y in l,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.leadingCoeff_mul_monic`：leadingCoeff_mul_monic {p q : R[X]} (
hq : Monic q) : leadingCoeff (p * q) = leadingCoeff p
· 使用定理 `Polynomial.monic_multiset_prod_of_monic`：monic_multiset_prod_of_monic (t
 : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i)) : Monic (t.map 
f).prod
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.C`：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Poly
nomial.C a).Splits
· 使用定理 `Polynomial.Splits.multisetProd`：∀ {R : Type u_1} [inst : CommSemiring R]
 {m : Multiset (Polynomial R)}, (∀ f ∈ m, f.Splits) → m.prod.Splits

--- 原说明 ---
See `splits_iff_exists_multiset` for the version with subtraction.
-/
theorem splits_iff_exists_multiset' {f : R[X]} :
    Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X + C ·)).prod := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · let S : Submonoid R[X] := MonoidHom.mrange C
    have hS : S = {C a | a : R} := MonoidHom.coe_mrange C
    rw [Splits, Submonoid.closure_union, ← hS, Submonoid.closure_eq, Submonoid.mem_sup] at hf
    obtain ⟨-, ⟨a, rfl⟩, g, hg, rfl⟩ := hf
    obtain ⟨mg, hmg, rfl⟩ := Submonoid.exists_multiset_of_mem_closure hg
    choose! j hj using hmg
    have hmg : mg = (mg.map j).map (X + C ·) := by simp [Multiset.map_congr rfl hj]
    rw [hmg, leadingCoeff_mul_monic, leadingCoeff_C]
    · use mg.map j
    · rw [hmg]
      apply monic_multiset_prod_of_monic
      simp [monic_X_add_C]
  · rintro ⟨m, hm⟩
    exact hm ▸ (Splits.C _).mul (.multisetProd (by simp [Splits.X_add_C]))
/-
**Polynomial.Splits.natDegree_le_one_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f : Polynomial R}, f.Splits → Ir
reducible f → f.natDegree ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_exists_multiset'`：splits_iff_exists_multiset' {f :
 R[X]} : Splits f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X + C 
·)).prod
· 使用定理 `Multiset.empty_or_exists_mem`：empty_or_exists_mem (s : Multiset α) : s =
 0 ∨ exists a, a in s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
（共 32 条，此处仅展示前 30 条）
-/
theorem Splits.natDegree_le_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : natDegree f ≤ 1 := by
  nontriviality R
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rcases m.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · rw [hm]
    simp
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons, Multiset.prod_cons] at hm
    rw [hm] at h
    simp only [irreducible_mul_iff, IsUnit.mul_iff, not_isUnit_X_add_C, false_and, and_false,
      or_false, false_or, ← Multiset.prod_toList, List.prod_isUnit_iff] at h
    have : m = 0 := by simpa [not_isUnit_X_add_C, ← Multiset.eq_zero_iff_forall_notMem] using h.1.2
    grw [hm, this, natDegree_mul_le]
    simp
/-
**Polynomial.Splits.degree_le_one_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f : Polynomial R}, f.Splits → Ir
reducible f → f.degree ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
· 使用定理 `Polynomial.Splits.natDegree_le_one_of_irreducible`：∀ {R : Type u_1} [ins
t : CommSemiring R] {f : Polynomial R}, f.Splits → Irreducible f → f.natDegree ≤
 1
-/
theorem Splits.degree_le_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : degree f ≤ 1 :=
  degree_le_of_natDegree_le (hf.natDegree_le_one_of_irreducible h)
/-
**Polynomial.Splits.comp_of_natDegree_le_one_of_invertible** 是 Mathlib 中的一个定理，位于
命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f g : Polynomial R},   f.Splits 
→ g.natDegree ≤ 1 → ∀ (h : Invertible g.leadingCoeff), (f.comp g).Splits
参数：h : Invertible g.leadingCoeff；f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.comp_C`：comp_C : p.comp (C a) = C (p.eval a)
· 使用定理 `Polynomial.splits_iff_exists_multiset'`：splits_iff_exists_multiset' {f :
 R[X]} : Splits f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X + C 
·)).prod
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.multiset_prod_comp`：multiset_prod_comp (s : Multiset R[X]) (q
 : R[X]) : s.prod.comp q = (s.map fun p : R[X] => p.comp q).prod
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.C`：∀ {R : Type u_1} [inst : Semiring R] (a : R), (Poly
nomial.C a).Splits
· 使用定理 `Polynomial.Splits.multisetProd`：∀ {R : Type u_1} [inst : CommSemiring R]
 {m : Multiset (Polynomial R)}, (∀ f ∈ m, f.Splits) → m.prod.Splits
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Splits.of_natDegree_le_one_of_invertible`：∀ {R : Type u_1} [i
nst : Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → ∀ (h : Invertible f.lead
ingCoeff), f.Splits
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
-/
theorem Splits.comp_of_natDegree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.natDegree ≤ 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits := by
  rcases lt_or_eq_of_le hg with hg | hg
  · rw [eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hg)]
    simp
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset'.mp hf
  rw [hm, mul_comp, C_comp, multiset_prod_comp]
  refine (Splits.C _).mul (multisetProd ?_)
  simp only [Multiset.mem_map]
  rintro - ⟨-, ⟨a, -, rfl⟩, rfl⟩
  apply of_natDegree_le_one_of_invertible (by simpa)
  rw [leadingCoeff, hg] at h
  simpa [leadingCoeff, hg]
/-
**Polynomial.Splits.comp_of_degree_le_one_of_invertible** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f g : Polynomial R},   f.Splits 
→ g.degree ≤ 1 → ∀ (h : Invertible g.leadingCoeff), (f.comp g).Splits
参数：h : Invertible g.leadingCoeff；f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one_of_invertible`：∀ {R : Type u_
1} [inst : CommSemiring R] {f g : Polynomial R},   f.Splits → g.natDegree ≤ 1 → 
∀ (h : Invertible g.leadingCoeff), (f.comp g).…
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem Splits.comp_of_degree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.degree ≤ 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hg) h
/-
**Polynomial.Splits.comp_of_natDegree_le_one_of_monic** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f g : Polynomial R}, f.Splits → 
g.natDegree ≤ 1 → g.Monic → (f.comp g).Splits
参数：f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one_of_invertible`：∀ {R : Type u_
1} [inst : CommSemiring R] {f g : Polynomial R},   f.Splits → g.natDegree ≤ 1 → 
∀ (h : Invertible g.leadingCoeff), (f.comp g).…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
-/
theorem Splits.comp_of_natDegree_le_one_of_monic {f g : R[X]} (hf : f.Splits)
    (hg : g.natDegree ≤ 1) (h : Monic g) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_invertible hg (h.leadingCoeff ▸ invertibleOne)
/-
**Polynomial.Splits.comp_of_degree_le_one_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f g : Polynomial R}, f.Splits → 
g.degree ≤ 1 → g.Monic → (f.comp g).Splits
参数：f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one_of_monic`：∀ {R : Type u_1} [i
nst : CommSemiring R] {f g : Polynomial R}, f.Splits → g.natDegree ≤ 1 → g.Monic
 → (f.comp g).Splits
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem Splits.comp_of_degree_le_one_of_monic {f g : R[X]} (hf : f.Splits)
    (hg : g.degree ≤ 1) (h : Monic g) : (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_le_of_degree_le hg) h
/-
**Polynomial.Splits.comp_X_add_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f : Polynomial R},   f.Splits → 
∀ (a : R), (f.comp (Polynomial.X + Polynomial.C a)).Splits
参数：a : R；f.comp (Polynomial.X + Polynomial.C a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one_of_monic`：∀ {R : Type u_1} [i
nst : CommSemiring R] {f g : Polynomial R}, f.Splits → g.natDegree ≤ 1 → g.Monic
 → (f.comp g).Splits
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_X_le`：natDegree_X_le : (X : R[X]).natDegree <= 1
· 使用定理 `Polynomial.monic_X_add_C`：monic_X_add_C (x : R) : Monic (X + C x)
-/
theorem Splits.comp_X_add_C {f : R[X]} (hf : f.Splits) (a : R) : (f.comp (X + C a)).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_add_C.trans_le natDegree_X_le) (monic_X_add_C a)
/-
**Polynomial.Splits.of_algHom** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f : Polynomial R} {A : Type u_2}
 {B : Type u_3} [inst_1 : Semiring A]   [inst_2 : Semiring B] [inst_3 : Algebra 
R A] [inst_4 : Algebra R B],   (Polynomial.map (algebraMap R A) f).Splits → ∀ (e
 : A →ₐ[R] B), (Polynomial.map (algebraMap R B) f).Splits
参数：Polynomial.map (algebraMap R A) f；e : A →ₐ[R] B；Polynomial.map (algebraMap R 
B) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
-/
theorem Splits.of_algHom {f : R[X]} {A B : Type*} [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (hf : Splits (f.map (algebraMap R A))) (e : A →ₐ[R] B) :
    Splits (f.map (algebraMap R B)) := by
  rw [← e.comp_algebraMap, ← map_map]
  apply hf.map
/-
**Polynomial.Splits.of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Split
s`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {f : Polynomial R} {A : Type u_2}
 (B : Type u_3) [inst_1 : CommSemiring A]   [inst_2 : Semiring B] [inst_3 : Alge
bra R A] [inst_4 : Algebra R B] [inst_5 : Algebra A B] [IsScalarTower R A B],   
(Polynomial.map (algebraMap R A) f).Splits → (Polynomial.map (algebraMap R B) f)
.Splits
参数：B : Type u_3；Polynomial.map (algebraMap R A) f；Polynomial.map (algebraMap R B
) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_algHom`：∀ {R : Type u_1} [inst : CommSemiring R] {f
 : Polynomial R} {A : Type u_2} {B : Type u_3} [inst_1 : Semiring A]   [inst_2 :
 Semiring B] [ins…
-/
theorem Splits.of_isScalarTower {f : R[X]} {A : Type*} (B : Type*) [CommSemiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (hf : Splits (f.map (algebraMap R A))) : Splits (f.map (algebraMap R B)) :=
  hf.of_algHom (IsScalarTower.toAlgHom R A B)

end CommSemiring

section Ring

variable [Ring R]

@[simp, aesop safe apply]
/-
**Polynomial.Splits.X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] (a : R), (Polynomial.X - Polynomial.C a).
Splits
参数：a : R；Polynomial.X - Polynomial.C a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.Splits.X_add_C`：∀ {R : Type u_1} [inst : Semiring R] (a : R),
 (Polynomial.X + Polynomial.C a).Splits
-/
theorem Splits.X_sub_C (a : R) : Splits (X - C a) := by
  simpa using! Splits.X_add_C (-a)

@[aesop safe apply]
/-
**Polynomial.Splits.neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {f : Polynomial R}, f.Splits → (-f).Split
s
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.C_neg`：C_neg : C (-a) = -C a
· 使用定理 `Polynomial.Splits.C_mul`：∀ {R : Type u_1} [inst : Semiring R] {f : Polyn
omial R}, f.Splits → ∀ (a : R), (Polynomial.C a * f).Splits
-/
protected theorem Splits.neg {f : R[X]} (hf : Splits f) : Splits (-f) := by
  rw [← neg_one_mul, ← C_1, ← C_neg]
  exact hf.C_mul (-1)

@[simp]
/-
**Polynomial.splits_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_neg_iff {f : R[X]} : Splits (-f) ↔ Splits f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.neg`：∀ {R : Type u_1} [inst : Ring R] {f : Polynomial 
R}, f.Splits → (-f).Splits
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem splits_neg_iff {f : R[X]} : Splits (-f) ↔ Splits f :=
  ⟨fun hf ↦ neg_neg f ▸ hf.neg, .neg⟩
/-
**Polynomial.Splits.comp_neg_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {f : Polynomial R}, f.Splits → (f.comp (-
Polynomial.X)).Splits
参数：f.comp (-Polynomial.X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Polynomial.Splits.neg`：∀ {R : Type u_1} [inst : Ring R] {f : Polynomial 
R}, f.Splits → (-f).Splits
· 使用定理 `Polynomial.Splits.X_sub_C`：∀ {R : Type u_1} [inst : Ring R] (a : R), (Po
lynomial.X - Polynomial.C a).Splits
· 使用定理 `Polynomial.one_comp`：one_comp : comp (1 : R[X]) p = 1
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.mul_comp_neg_X`：mul_comp_neg_X {R : Type*} [Ring R] (p q : R[
X]) : (p * q).comp (-X) = p.comp (-X) * q.comp (-X)
-/
theorem Splits.comp_neg_X {f : R[X]} (hf : f.Splits) : (f.comp (-X)).Splits := by
  refine Submonoid.closure_induction ?_ (by simp)
    (fun f g _ _ hf hg ↦ mul_comp_neg_X f g ▸ hf.mul hg) hf
  · rintro f (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · simp
    · rw [add_comp, X_comp, C_comp, neg_add_eq_sub, ← neg_sub]
      exact (X_sub_C a).neg

end Ring

section CommRing

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

/-
**Polynomial.splits_iff_exists_multiset** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_iff_exists_multiset : Splits f ↔ exists m : Multiset R, f = C f.lea
dingCoeff * (m.map (X - C ·)).prod
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Polynomial.splits_iff_exists_multiset'`：splits_iff_exists_multiset' {f :
 R[X]} : Splits f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X + C 
·)).prod
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
theorem splits_iff_exists_multiset :
    Splits f ↔ ∃ m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod := by
  refine splits_iff_exists_multiset'.trans ⟨?_, ?_⟩ <;>
    rintro ⟨m, hm⟩ <;> exact ⟨m.map (- ·), by simpa⟩
/-
**Polynomial.Splits.exists_eval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Sp
lits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R}, f.Splits → f.degr
ee ≠ 0 → ∃ a, Polynomial.eval a f = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Multiset.empty_or_exists_mem`：empty_or_exists_mem (s : Multiset α) : s =
 0 ∨ exists a, a in s
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Multiset.prod_zero`：prod_zero : @prod M _ 0 = 1
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem Splits.exists_eval_eq_zero (hf : Splits f) (hf0 : degree f ≠ 0) :
    ∃ a, eval a f = 0 := by
  obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, by rw [hm]; simp⟩

/-- Pick a root of a polynomial that splits. -/
/-
**Polynomial.rootOfSplits** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：rootOfSplits (hf : f.Splits) (hfd : f.degree != 0) : R
参数：hf : f.Splits；hfd : f.degree != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0

--- 原说明 ---
Pick a root of a polynomial that splits.
-/
noncomputable def rootOfSplits (hf : f.Splits) (hfd : f.degree ≠ 0) : R :=
  Classical.choose <| hf.exists_eval_eq_zero hfd

@[simp]
/-
**Polynomial.eval_rootOfSplits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_rootOfSplits (hf : f.Splits) (hfd : f.degree != 0) : f.eval (rootOfSp
lits hf hfd) = 0
参数：hf : f.Splits；hfd : f.degree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
-/
theorem eval_rootOfSplits (hf : f.Splits) (hfd : f.degree ≠ 0) :
    f.eval (rootOfSplits hf hfd) = 0 :=
  Classical.choose_spec <| hf.exists_eval_eq_zero hfd
/-
**Polynomial.Splits.comp_X_sub_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R},   f.Splits → ∀ (a
 : R), (f.comp (Polynomial.X - Polynomial.C a)).Splits
参数：a : R；f.comp (Polynomial.X - Polynomial.C a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one_of_monic`：∀ {R : Type u_1} [i
nst : CommSemiring R] {f g : Polynomial R}, f.Splits → g.natDegree ≤ 1 → g.Monic
 → (f.comp g).Splits
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X_le`：natDegree_X_le : (X : R[X]).natDegree <= 1
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
-/
theorem Splits.comp_X_sub_C (hf : f.Splits) (a : R) : (f.comp (X - C a)).Splits :=
  hf.comp_of_natDegree_le_one_of_monic (natDegree_sub_C.trans_le natDegree_X_le) (monic_X_sub_C a)

variable [IsDomain R]
/-
**Polynomial.Splits.eq_prod_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f = Polynomial.C f.leadingCoeff * (Multiset.map (fun x => Poly
nomial.X - Polynomial.C x) f.roots).prod
参数：Multiset.map (fun x => Polynomial.X - Polynomial.C x) f.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `Polynomial.roots_C_mul`：roots_C_mul (p : R[X]) (ha : a != 0) : (C a * p)
.roots = p.roots
· 使用定理 `Polynomial.roots_multiset_prod_X_sub_C`：roots_multiset_prod_X_sub_C (s :
 Multiset R) : (s.map fun a => X - C a).prod.roots = s
-/
theorem Splits.eq_prod_roots (hf : Splits f) :
    f = C f.leadingCoeff * (f.roots.map (X - C ·)).prod := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · obtain ⟨m, hm⟩ := splits_iff_exists_multiset.mp hf
    suffices hf : f.roots = m by rwa [hf]
    rw [hm, roots_C_mul _ hf0, roots_multiset_prod_X_sub_C]
/-
**Polynomial.Splits.eq_prod_roots_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f.Monic → f = (Multiset.map (fun x => Polynomial.X - Polynomia
l.C x) f.roots).prod
参数：Multiset.map (fun x => Polynomial.X - Polynomial.C x) f.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Splits.eq_prod_roots_of_monic (hf : Splits f) (hm : f.Monic) :
    f = (f.roots.map (X - C ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots, hm.leadingCoeff, C_1, one_mul]
/-
**Polynomial.Splits.eval_eq_prod_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Spl
its`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → ∀ (x : R), Polynomial.eval x f = f.leadingCoeff * (Multiset.ma
p (fun x_1 => x - x_1) f.roots).prod
参数：x : R；Multiset.map (fun x_1 => x - x_1) f.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_multiset_prod`：eval_multiset_prod (s : Multiset R[X]) (x
 : R) : eval x s.prod = (s.map (eval x)).prod
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.eval_eq_prod_roots (hf : Splits f) (x : R) :
    f.eval x = f.leadingCoeff * (f.roots.map (x - ·)).prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [eval_multiset_prod]
/-
**Polynomial.Splits.eval_eq_prod_roots_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f.Monic → ∀ (x : R), Polynomial.eval x f = (Multiset.map (fun 
x_1 => x - x_1) f.roots).prod
参数：x : R；Multiset.map (fun x_1 => x - x_1) f.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eval_eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing 
R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → ∀ (x : R), Polynomial.
eval x f = f.leadingCoeff …
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.eval_eq_prod_roots_of_monic (hf : Splits f) (hm : Monic f) (x : R) :
    f.eval x = (f.roots.map (x - ·)).prod := by
  simp [hf.eval_eq_prod_roots, hm]

omit [IsDomain R] in
/-
**Polynomial.Splits.aeval_eq_prod_aroots_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} {A : Type u_2} [in
st_1 : CommRing A] [inst_2 : IsDomain A]   [inst_3 : Algebra R A],   (Polynomial
.map (algebraMap R A) f).Splits →     f.Monic → ∀ (x : A), (Polynomial.aeval x) 
f = (Multiset.map (fun x_1 => x - x_1) (f.aroots A)).prod
参数：Polynomial.map (algebraMap R A) f；x : A；Polynomial.aeval x；Multiset.map (fun 
x_1 => x - x_1) (f.aroots A)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eval_eq_prod_roots_of_monic`：∀ {R : Type u_1} [inst : 
CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic → ∀ (
x : R), Polynomial.eval x f = (Mult…
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.aeval_eq_prod_aroots_of_monic
    (hf : (f.map (algebraMap R A)).Splits) (hm : Monic f) (x : A) :
    f.aeval x = ((f.aroots A).map (x - ·)).prod := by
  simp [hf.eval_eq_prod_roots_of_monic (hm.map (algebraMap R A)), ← eval_map_algebraMap]
/-
**Polynomial.Splits.eval_derivative** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits
`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R] [inst_2 : DecidableEq R],   f.Splits →     ∀ (x : R),       Polynomial.eval 
x (Polynomial.derivative f) =         f.leadingCoeff *           (Multiset.map (
fun a => (Multiset.map (fun x_1 => x - x_1) (f.roots.erase a)).prod) f.roots).su
m
参数：x : R；Polynomial.derivative f；Multiset.map (fun a => (Multiset.map (fun x_1 =
> x - x_1) (f.roots.erase a)).prod) f.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.derivative_mul`：derivative_mul {f g : R[X]} : derivative (f *
 g) = derivative f * g + f * derivative g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.derivative_prod`：derivative_prod [DecidableEq ι] {s : Multise
t ι} {f : ι -> R[X]} : derivative (Multiset.map f s).prod = (Multiset.map (fun i
 => (Multiset.ma…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_multisetSum`：eval_multisetSum (s : Multiset R[X]) (x : R
) : eval x s.sum = (s.map (eval x)).sum
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Polynomial.eval_multiset_prod`：eval_multiset_prod (s : Multiset R[X]) (x
 : R) : eval x s.prod = (s.map (eval x)).prod
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.eval_derivative [DecidableEq R] (hf : f.Splits) (x : R) :
    eval x f.derivative = f.leadingCoeff *
      (f.roots.map fun a ↦ ((f.roots.erase a).map (x - ·)).prod).sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [derivative_prod, eval_multisetSum, eval_multiset_prod]

/-- Let `f` be a monic polynomial over that splits. Let `x` be a root of `f`.
Then $f'(r) = \prod_{a}(x-a)$, where the product in the RHS is taken over all roots of `f`,
with the multiplicity of `x` reduced by one. -/
/-
**Polynomial.Splits.eval_root_derivative** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.S
plits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R] [inst_2 : DecidableEq R],   f.Splits →     f.Monic →       ∀ {x : R},       
  x ∈ f.roots →           Polynomial.eval x (Polynomial.derivative f) = (Multise
t.map (fun x_1 => x - x_1) (f.roots.erase x)).prod
参数：Polynomial.derivative f；Multiset.map (fun x_1 => x - x_1) (f.roots.erase x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_multiset_prod_X_sub_C_derivative`：eval_multiset_prod_X_s
ub_C_derivative [DecidableEq R] {S : Multiset R} {r : R} (hr : r in S) : eval r 
(derivative (Multiset.map (fun a => X …
· 使用定理 `Polynomial.Splits.eq_prod_roots_of_monic`：∀ {R : Type u_1} [inst : CommR
ing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic → f = (Mul
tiset.map (fun x => Polynomial…

--- 原说明 ---
Let `f` be a monic polynomial over that splits. Let `x` be a root of `f`.
Then $f'(r) = \prod_{a}(x-a)$, where the product in the RHS is taken over all ro
ots of `f`,
with the multiplicity of `x` reduced by one.
-/
theorem Splits.eval_root_derivative [DecidableEq R] (hf : f.Splits) (hm : f.Monic) {x : R}
    (hx : x ∈ f.roots) : eval x f.derivative = ((f.roots.erase x).map (x - ·)).prod := by
  rw [← eval_multiset_prod_X_sub_C_derivative hx, ← hf.eq_prod_roots_of_monic hm]

omit [IsDomain R] in
/-
**Polynomial.Splits.of_splits_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} {S : Type u_4} [in
st_1 : CommRing S] [inst_2 : IsDomain S]   {i : R →+* S},   Function.Injective ⇑
i → (Polynomial.map i f).Splits → (∀ a ∈ (Polynomial.map i f).roots, a ∈ i.range
) → f.Splits
参数：Polynomial.map i f；∀ a ∈ (Polynomial.map i f).roots, a ∈ i.range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `Polynomial.leadingCoeff_map_of_injective`：leadingCoeff_map_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).leadin
gCoeff = f p.leadingCoeff
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.map_pmap`：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, 
p a -> β) (s) : forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.map_multiset_prod`：∀ {R : Type u} {S : Type v} [inst : CommSe
miring R] [inst_1 : CommSemiring S] (f : R →+* S)   (m : Multiset (Polynomial R)
), Polynomial.map …
· 使用定理 `Multiset.pmap.congr_simp`：∀ {α : Type u_1} {β : Type v} {p : α → Prop} (
f f_1 : (a : α) → p a → β),   f = f_1 → ∀ (s s_1 : Multiset α) (e_s : s = s_1) (
a : ∀ a ∈ s, p…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Multiset.pmap_eq_map`：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Mult
iset α) : forall H, @pmap _ _ p (fun a _ => f a) s H = map f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Splits.of_splits_map_of_injective {S : Type*} [CommRing S] [IsDomain S] {i : R →+* S}
    (hi : Function.Injective i) (hf : Splits (f.map i))
    (hi : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Splits f := by
  choose j hj using hi
  rw [splits_iff_exists_multiset]
  refine ⟨(f.map i).roots.pmap j fun _ ↦ id, map_injective i hi ?_⟩
  conv_lhs => rw [hf.eq_prod_roots, leadingCoeff_map_of_injective hi]
  simp [Multiset.pmap_eq_map, hj, Multiset.map_pmap, Polynomial.map_multiset_prod]
/-
**Polynomial.Splits.mem_lift_of_roots_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits →     f.Monic → ∀ {S : Type u_4} [inst_2 : Ring S] (i : S →+* R)
, (∀ a ∈ f.roots, a ∈ i.range) → f ∈ Polynomial.lifts i
参数：i : S →+* R；∀ a ∈ f.roots, a ∈ i.range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots_of_monic`：∀ {R : Type u_1} [inst : CommR
ing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic → f = (Mul
tiset.map (fun x => Polynomial…
· 使用定理 `Polynomial.lifts_iff_liftsRing`：lifts_iff_liftsRing (p : S[X]) : p in li
fts f ↔ p in liftsRing f
· 使用定理 `Subring.multiset_prod_mem`：∀ {R : Type u_1} [inst : CommRing R] (s : Sub
ring R) (m : Multiset R), (∀ a ∈ m, a ∈ s) → m.prod ∈ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Subring.sub_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x - y ∈ s
· 使用定理 `Polynomial.X_mem_lifts`：X_mem_lifts (f : R ->+* S) : (X : S[X]) in lifts
 f
· 使用定理 `Polynomial.C'_mem_lifts`：∀ {R : Type u} [inst : Semiring R] {S : Type v}
 [inst_1 : Semiring S] {f : R →+* S} {s : S},   s ∈ Set.range ⇑f → Polynomial.C 
s ∈ Polynomia…
-/
theorem Splits.mem_lift_of_roots_mem_range (hf : f.Splits) (hm : f.Monic)
    {S : Type*} [Ring S] (i : S →+* R) (hr : ∀ a ∈ f.roots, a ∈ i.range) :
    f ∈ Polynomial.lifts i := by
  rw [hf.eq_prod_roots_of_monic hm, lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun g hg => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hg
  exact Subring.sub_mem _ (X_mem_lifts i) (C'_mem_lifts (hr x hx))
/-
**Polynomial.Splits.eq_X_sub_C_of_single_root** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → ∀ {x : R}, f.roots = {x} → f = Polynomial.C f.leadingCoeff * (
Polynomial.X - Polynomial.C x)
参数：Polynomial.X - Polynomial.C x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.eq_X_sub_C_of_single_root (hf : Splits f) {x : R} (hr : f.roots = {x}) :
    f = C f.leadingCoeff * (X - C x) := by
  rw [hf.eq_prod_roots, hr]
  simp
/-
**Polynomial.Splits.natDegree_eq_card_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R], f.Splits → f.natDegree = f.roots.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.roots_zero`：roots_zero : (0 : R[X]).roots = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `Polynomial.natDegree_C_mul`：natDegree_C_mul (a0 : a != 0) : (C a * p).na
tDegree = p.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card`：natDegree_multiset_p
rod_X_sub_C_eq_card (s : Multiset R) : (s.map (X - C ·)).prod.natDegree = Multis
et.card s
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem Splits.natDegree_eq_card_roots (hf : Splits f) :
    f.natDegree = f.roots.card := by
  by_cases hf0 : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf0]
  · conv_lhs => rw [hf.eq_prod_roots, natDegree_C_mul hf0, natDegree_multiset_prod_X_sub_C_eq_card]
/-
**Polynomial.Splits.degree_eq_card_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.S
plits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f ≠ 0 → f.degree = ↑f.roots.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_eq_iff_natDegree_eq`：degree_eq_iff_natDegree_eq {p : R
[X]} {n : Nat} (hp : p != 0) : p.degree = n ↔ p.natDegree = n
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
-/
theorem Splits.degree_eq_card_roots (hf : Splits f) (hf0 : f ≠ 0) :
    f.degree = f.roots.card :=
  (degree_eq_iff_natDegree_eq hf0).mpr hf.natDegree_eq_card_roots

/-- A polynomial splits if and only if it has as many roots as its degree. -/
/-
**Polynomial.splits_iff_card_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_iff_card_roots : Splits f ↔ f.roots.card = f.natDegree
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`：C_leadingCoeff_mul_
prod_multiset_X_sub_C (hroots : Multiset.card p.roots = p.natDegree) : C p.leadi
ngCoeff * (p.roots.map fun a => X - C a).…

--- 原说明 ---
A polynomial splits if and only if it has as many roots as its degree.
-/
theorem splits_iff_card_roots : Splits f ↔ f.roots.card = f.natDegree :=
  ⟨fun h ↦ h.natDegree_eq_card_roots.symm, fun h ↦ splits_iff_exists_multiset.mpr
    ⟨f.roots, (C_leadingCoeff_mul_prod_multiset_X_sub_C h).symm⟩⟩
/-
**Polynomial.Splits.roots_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R], f.Splits → f.natDegree ≠ 0 → f.roots ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
-/
theorem Splits.roots_ne_zero (hf : Splits f) (hf0 : natDegree f ≠ 0) :
    f.roots ≠ 0 := by
  simpa [hf.natDegree_eq_card_roots] using hf0
/-
**Polynomial.Splits.roots_map_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.S
plits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] {S : Type u_4} 
[inst_2 : CommRing S] [inst_3 : IsDomain S]   {f : Polynomial R},   f.Splits → ∀
 {φ : R →+* S}, Polynomial.map φ f ≠ 0 → (Polynomial.map φ f).roots = Multiset.m
ap (⇑φ) f.roots
参数：Polynomial.map φ f；⇑φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.roots_C`：roots_C (x : R) : (C x).roots = 0
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.roots_X_add_C`：roots_X_add_C (r : R) : roots (X + C r) = {-r}
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `Polynomial.roots_one`：roots_one : (1 : R[X]).roots = ∅
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
-/
theorem Splits.roots_map_of_ne_zero {S : Type*} [CommRing S] [IsDomain S]
    {f : R[X]} (hf : Splits f) {φ : R →+* S} (hφ : f.map φ ≠ 0) :
    (f.map φ).roots = f.roots.map φ := by
  induction hf using Submonoid.closure_induction with
  | mem p hp => obtain (⟨r, rfl⟩ | ⟨a, rfl⟩) := hp <;> simp
  | one => simp
  | mul x y _ _ hx hy => simp_all [roots_mul, show x * y ≠ 0 by aesop]
/-
**Polynomial.Splits.roots_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R] {S : Type u_4} [inst_2 : CommRing S]   [inst_3 : IsDomain S],   f.Splits → ∀
 {i : R →+* S}, Function.Injective ⇑i → (Polynomial.map i f).roots = Multiset.ma
p (⇑i) f.roots
参数：Polynomial.map i f；⇑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.roots_map_of_injective_of_card_eq_natDegree`：roots_map_of_inj
ective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]} {f : A ->+* B} 
(hf : Function.Injective f) (hroots : Multis…
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
-/
theorem Splits.roots_map_of_injective {S : Type*} [CommRing S] [IsDomain S]
    (hf : f.Splits) {i : R →+* S} (hi : Function.Injective i) : (f.map i).roots = f.roots.map i :=
  (roots_map_of_injective_of_card_eq_natDegree hi hf.natDegree_eq_card_roots.symm).symm

omit [IsDomain R] in
/-
**Polynomial.Splits.image_rootSet_of_map_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} {A : Type u_2} {B 
: Type u_3} [inst_1 : CommRing A]   [inst_2 : CommRing B] [inst_3 : IsDomain A] 
[inst_4 : IsDomain B] [inst_5 : Algebra R A] [inst_6 : Algebra R B],   (Polynomi
al.map (algebraMap R A) f).Splits →     ∀ (φ : A →ₐ[R] B), Polynomial.map (algeb
raMap R B) f ≠ 0 → ⇑φ '' f.rootSet A = f.rootSet B
参数：Polynomial.map (algebraMap R A) f；φ : A →ₐ[R] B；algebraMap R B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Polynomial.Splits.roots_map_of_ne_zero`：∀ {R : Type u_1} [inst : CommRin
g R] [inst_1 : IsDomain R] {S : Type u_4} [inst_2 : CommRing S] [inst_3 : IsDoma
in S]   {f : Polynomial R}, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.toFinset_map`：Multiset.toFinset_map [DecidableEq α] [DecidableE
q β] (f : α -> β) (m : Multiset α) : (m.map f).toFinset = m.toFinset.image f
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.image_rootSet_of_map_ne_zero (hf : (f.map (algebraMap R A)).Splits)
    (φ : A →ₐ[R] B) (hφ : f.map (algebraMap R B) ≠ 0) : φ '' f.rootSet A = f.rootSet B := by
  classical
  replace hφ : (f.map (algebraMap R A)).map (φ : A →+* B) ≠ 0 := by
    rwa [map_map, φ.comp_algebraMap]
  replace hf := hf.roots_map_of_ne_zero hφ
  rw [map_map, φ.comp_algebraMap] at hf
  simp [rootSet, aroots, hf, Multiset.toFinset_map]
/-
**Polynomial.Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f.coeff 0 = (-1) ^ f.natDegree * f.leadingCoeff * f.roots.prod
参数：-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_zero_eq_eval_zero`：coeff_zero_eq_eval_zero (p : R[X]) :
 coeff p 0 = p.eval 0
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_multiset_prod`：eval_multiset_prod (s : Multiset R[X]) (x
 : R) : eval x s.prod = (s.map (eval x)).prod
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Multiset.prod_map_neg`：∀ {M : Type u_2} [inst : CommMonoid M] [inst_1 : 
HasDistribNeg M] (s : Multiset M),   (Multiset.map Neg.neg s).prod = (-1) ^ s.ca
rd * s.prod
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Splits.natDegree_eq_card_roots`：∀ {R : Type u_1} [inst : Comm
Ring R] {f : Polynomial R} [inst_1 : IsDomain R], f.Splits → f.natDegree = f.roo
ts.card
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots (hf : Splits f) :
    f.coeff 0 = (-1) ^ f.natDegree * f.leadingCoeff * f.roots.prod := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [coeff_zero_eq_eval_zero, eval_multiset_prod, hf.natDegree_eq_card_roots,
    mul_assoc, mul_left_comm]

/-- If `f` is a monic polynomial that splits, then `coeff f 0` equals the product of the roots. -/
/-
**Polynomial.Splits.coeff_zero_eq_prod_roots_of_monic** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f.Monic → f.coeff 0 = (-1) ^ f.natDegree * f.roots.prod
参数：-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots`：∀ {R : Type
 u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits →
 f.coeff 0 = (-1) ^ f.natDegree * f.leadingCoeff …
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is a monic polynomial that splits, then `coeff f 0` equals the product of
 the roots.
-/
theorem Splits.coeff_zero_eq_prod_roots_of_monic (hf : Splits f) (hm : Monic f) :
    coeff f 0 = (-1) ^ f.natDegree * f.roots.prod := by
  simp [hf.coeff_zero_eq_leadingCoeff_mul_prod_roots, hm]
/-
**Polynomial.Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff** 是 Mathlib 中的一个
定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f.nextCoeff = -f.leadingCoeff * f.roots.sum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.nextCoeff_C_mul`：nextCoeff_C_mul : (C a * p).nextCoeff = a * 
p.nextCoeff
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Polynomial.Monic.nextCoeff_multiset_prod`：∀ {R : Type u} {ι : Type y} [i
nst : CommSemiring R] (t : Multiset ι) (f : ι → Polynomial R),   (∀ i ∈ t, (f i)
.Monic) → (Multiset.map f t).p…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.nextCoeff_X_sub_C`：nextCoeff_X_sub_C [Ring S] (c : S) : nextC
oeff (X - C c) = -c
· 使用定理 `Multiset.sum_map_neg'`：∀ {G : Type u_4} [inst : SubtractionCommMonoid G]
 (m : Multiset G), (Multiset.map Neg.neg m).sum = -m.sum
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff (hf : Splits f) :
    f.nextCoeff = -f.leadingCoeff * f.roots.sum := by
  conv_lhs => rw [hf.eq_prod_roots]
  simp [Multiset.sum_map_neg', monic_X_sub_C, Monic.nextCoeff_multiset_prod]

/-- If `f` is a monic polynomial that splits, then `f.nextCoeff` equals the negative of the sum
of the roots. -/
/-
**Polynomial.Splits.nextCoeff_eq_neg_sum_roots_of_monic** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain
 R],   f.Splits → f.Monic → f.nextCoeff = -f.roots.sum
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff`：∀ {R : Ty
pe u_1} [inst : CommRing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits
 → f.nextCoeff = -f.leadingCoeff * f.roots.sum
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `f` is a monic polynomial that splits, then `f.nextCoeff` equals the negative
 of the sum
of the roots.
-/
theorem Splits.nextCoeff_eq_neg_sum_roots_of_monic (hf : Splits f) (hm : Monic f) :
    f.nextCoeff = -f.roots.sum := by
  simp [hf.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff, hm]
/-
**Polynomial.splits_X_sub_C_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_X_sub_C_mul_iff {a : R} : Splits ((X - C a) * f) ↔ Splits f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `Polynomial.instIsLeftCancelMulZeroOfIsCancelAdd`：∀ {R : Type u} [inst : 
Semiring R] [IsCancelAdd R] [IsLeftCancelMulZero R], IsLeftCancelMulZero (Polyno
mial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Polynomial.roots_mul`：roots_mul {p q : R[X]} (hpq : p * q != 0) : (p * q
).roots = p.roots + q.roots
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.leadingCoeff_X_sub_C`：leadingCoeff_X_sub_C [Ring S] (r : S) :
 (X - C r).leadingCoeff = 1
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 36 条，此处仅展示前 30 条）
-/
theorem splits_X_sub_C_mul_iff {a : R} : Splits ((X - C a) * f) ↔ Splits f := by
  refine ⟨fun hf ↦ ?_, ((Splits.X_sub_C _).mul ·)⟩
  by_cases hf₀ : f = 0
  · aesop
  have := hf.eq_prod_roots
  rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul,
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hf₀), roots_X_sub_C,
    Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons, mul_left_comm] at this
  rw [mul_left_cancel₀ (X_sub_C_ne_zero _) this]
  aesop
/-
**Polynomial.splits_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_mul (hf₀ : f != 0) (hg₀ : g != 0) : Splits (f * g) ↔ Splits f ∧ Spl
its g
参数：hf₀ : f != 0；hg₀ : g != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_eq_zero`：∀ {R : Type u_1} [inst : Semirin
g R] {f : Polynomial R}, f.natDegree = 0 → f.Splits
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_eq_zero_iff`：∀ {n m : ℕ}, n + m = 0 ↔ n = 0 ∧ m = 0
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `Polynomial.degree_ne_of_natDegree_ne`：degree_ne_of_natDegree_ne {n : Nat
} : p.natDegree != n -> degree p != n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.dvd_iff_isRoot`：dvd_iff_isRoot : X - C a ∣ p ↔ IsRoot p a
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Nat.succ_inj`：∀ {a b : ℕ}, a.succ = b.succ ↔ a = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_X_sub_C_mul_iff`：splits_X_sub_C_mul_iff {a : R} : Spli
ts ((X - C a) * f) ↔ Splits f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 39 条，此处仅展示前 30 条）
-/
theorem splits_mul (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) :
    Splits (f * g) ↔ Splits f ∧ Splits g := by
  refine ⟨fun h ↦ ?_, and_imp.mpr .mul⟩
  generalize hp : f * g = p at *
  generalize hn : p.natDegree = n
  induction n generalizing p f g with
  | zero =>
    rw [← hp, natDegree_mul hf₀ hg₀, Nat.add_eq_zero_iff] at hn
    exact ⟨.of_natDegree_eq_zero hn.1, .of_natDegree_eq_zero hn.2⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := Splits.exists_eval_eq_zero h (degree_ne_of_natDegree_ne <| hn ▸ by simp)
    have := dvd_iff_isRoot.mpr ha
    rw [← hp, (prime_X_sub_C a).dvd_mul] at this
    wlog hf : X - C a ∣ f with hf2
    · exact .symm <| hf2 n ih hg₀ hf₀ p ((mul_comm g f).trans hp) h hn a ha this.symm <|
        this.resolve_left hf
    obtain ⟨f, rfl⟩ := hf
    rw [mul_assoc] at hp; subst hp
    rw [natDegree_mul (by aesop) (by aesop), natDegree_X_sub_C, add_comm, Nat.succ_inj] at hn
    have := ih (by aesop) hg₀ (f * g) rfl (splits_X_sub_C_mul_iff.mp h) hn
    aesop

@[deprecated (since := "2026-06-08")] alias splits_mul_iff := splits_mul
/-
**Polynomial.splits_mul'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：splits_mul' : (f * g).Splits ↔ (f.Splits ∨ g = 0) ∧ (g.Splits ∨ f = 0) whe
re mp hpq
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
lemma splits_mul' : (f * g).Splits ↔ (f.Splits ∨ g = 0) ∧ (g.Splits ∨ f = 0) where
  mp hpq := by grind [splits_mul]
  mpr := by rintro ⟨hp | rfl, hq | rfl⟩ <;> simp [*]
/-
**Polynomial.splits_mul_iff_left** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：splits_mul_iff_left (hg₀ : g != 0) (hg : g.Splits) : (f * g).Splits ↔ f.Sp
lits
参数：hg₀ : g != 0；hg : g.Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma splits_mul_iff_left (hg₀ : g ≠ 0) (hg : g.Splits) : (f * g).Splits ↔ f.Splits := by
  simp [splits_mul', *]
/-
**Polynomial.splits_mul_iff_right** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：splits_mul_iff_right (hf₀ : f != 0) (hg : f.Splits) : (f * g).Splits ↔ g.S
plits
参数：hf₀ : f != 0；hg : f.Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma splits_mul_iff_right (hf₀ : f ≠ 0) (hg : f.Splits) : (f * g).Splits ↔ g.Splits := by
  simp [splits_mul', *]
/-
**Polynomial.splits_X_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [IsDomain R], (Pol
ynomial.X * f).Splits ↔ f.Splits
参数：Polynomial.X * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma splits_X_mul : (X * f).Splits ↔ f.Splits := by simp [splits_mul']
/-
**Polynomial.splits_mul_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [IsDomain R], (f *
 Polynomial.X).Splits ↔ f.Splits
参数：f * Polynomial.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma splits_mul_X : (f * X).Splits ↔ f.Splits := by simp [mul_comm f]

alias ⟨Splits.of_X_mul, _⟩ := splits_X_mul
alias ⟨Splits.of_mul_X, _⟩ := splits_mul_X
/-
**Polynomial.Splits.of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f g : Polynomial R} [IsDomain R], g.
Splits → g ≠ 0 → f ∣ g → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_mul`：splits_mul (hf₀ : f != 0) (hg₀ : g != 0) : Splits
 (f * g) ↔ Splits f ∧ Splits g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Splits.of_dvd (hg : Splits g) (hg₀ : g ≠ 0) (hfg : f ∣ g) : Splits f := by
  obtain ⟨g, rfl⟩ := hfg
  exact ((splits_mul (by simp_all) (by simp_all)).mp hg).1
/-
**Polynomial.splits_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_prod_iff {ι : Type*} {f : ι -> R[X]} {s : Finset ι} (hf : forall i 
in s, f i != 0) : (∏ x in s, f x).Splits ↔ forall x in s, (f x).Splits
参数：hf : forall i in s, f i != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `Polynomial.Splits.prod`：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Ty
pe u_2} {f : ι → Polynomial R} {s : Finset ι},   (∀ i ∈ s, (f i).Splits) → (∏ i 
∈ s, f i).Sp…
-/
theorem splits_prod_iff {ι : Type*} {f : ι → R[X]} {s : Finset ι} (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ x ∈ s, f x).Splits ↔ ∀ x ∈ s, (f x).Splits :=
  ⟨fun h _ hx ↦ h.of_dvd (Finset.prod_ne_zero_iff.mpr hf) (Finset.dvd_prod_of_mem f hx),
    Splits.prod⟩

@[deprecated "Use `Splits.degree_le_one_of_irreducible` instead." (since := "2026-01-13")]
/-
**Polynomial.Splits.splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R} [IsDomain R],   f.
Splits → f = 0 ∨ ∀ {g : Polynomial R}, Irreducible g → g ∣ f → g.degree ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Polynomial.degree_le_of_natDegree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.natDegree ≤ n → p.degree ≤ ↑n
· 使用定理 `Polynomial.Splits.natDegree_le_one_of_irreducible`：∀ {R : Type u_1} [ins
t : CommSemiring R] {f : Polynomial R}, f.Splits → Irreducible f → f.natDegree ≤
 1
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
-/
theorem Splits.splits (hf : Splits f) :
    f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g ≤ 1 :=
  or_iff_not_imp_left.mpr fun hf0 _ hg hgf ↦ degree_le_of_natDegree_le <|
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg
/-
**Polynomial.map_sub_sprod_roots_eq_prod_map_eval** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial`。
形式化陈述：map_sub_sprod_roots_eq_prod_map_eval (s : Multiset R) (g : R[X]) (hg : g.M
onic) (hg' : g.Splits) : ((s ×ˢ g.roots).map fun ij => ij.1 - ij.2).prod = (s.ma
p g.eval).prod
参数：s : Multiset R；g : R[X]；hg : g.Monic；hg' : g.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.eval_multiset_prod`：eval_multiset_prod (s : Multiset R[X]) (x
 : R) : eval x s.prod = (s.map (eval x)).prod
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Multiset.prod_map_product_eq_prod_prod`：prod_map_product_eq_prod_prod {M
 : Type*} [CommMonoid M] (s : Multiset α) (t : Multiset β) (f : α × β -> M) : ((
s ×ˢ t).map f).prod = (s.map…
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_sub_sprod_roots_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((s ×ˢ g.roots).map fun ij ↦ ij.1 - ij.2).prod = (s.map g.eval).prod := by
  have := hg'.eq_prod_roots
  rw [hg.leadingCoeff, map_one, one_mul] at this
  conv_rhs => rw [this]
  simp_rw [eval_multiset_prod, Multiset.prod_map_product_eq_prod_prod, Multiset.map_map]
  congr! with x hx
  ext; simp

set_option backward.isDefEq.respectTransparency false in
/-
**Polynomial.map_sub_roots_sprod_eq_prod_map_eval** 是 Mathlib 中的一个引理，位于命名空间 `Pol
ynomial`。
形式化陈述：map_sub_roots_sprod_eq_prod_map_eval (s : Multiset R) (g : R[X]) (hg : g.M
onic) (hg' : g.Splits) : ((g.roots ×ˢ s).map fun ij => ij.1 - ij.2).prod = (-1) 
^ (s.card * g.roots.card) * (s.map g.eval).prod
参数：s : Multiset R；g : R[X]；hg : g.Monic；hg' : g.Splits。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_swap_product`：∀ {α : Type u_1} {β : Type v} (s : Multiset α
) (t : Multiset β), Multiset.map Prod.swap (s ×ˢ t) = t ×ˢ s
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.card_product`：card_product : card (s ×ˢ t) = card s * card t
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用引理 `Polynomial.map_sub_sprod_roots_eq_prod_map_eval`：map_sub_sprod_roots_eq_
prod_map_eval (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) : ((s 
×ˢ g.roots).map fun ij => ij.1 - ij.2…
-/
lemma map_sub_roots_sprod_eq_prod_map_eval
    (s : Multiset R) (g : R[X]) (hg : g.Monic) (hg' : g.Splits) :
    ((g.roots ×ˢ s).map fun ij ↦ ij.1 - ij.2).prod =
      (-1) ^ (s.card * g.roots.card) * (s.map g.eval).prod := by
  trans ((s ×ˢ g.roots).map fun ij ↦ (-1) * (ij.1 - ij.2)).prod
  · rw [← Multiset.map_swap_product, Multiset.map_map]; simp
  · rw [Multiset.prod_map_mul]; simp [map_sub_sprod_roots_eq_prod_map_eval _ _ hg hg']

end CommRing

section DivisionSemiring

variable [DivisionSemiring R]

/-
**Polynomial.Splits.of_natDegree_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Sp
lits`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionSemiring R] {f : Polynomial R}, f.natDegr
ee ≤ 1 → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_eq_X_add_C_of_natDegree_le_one`：exists_eq_X_add_C_of_n
atDegree_le_one (h : natDegree p <= 1) : exists a b, p = C a * X + C b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.Splits.C_mul`：∀ {R : Type u_1} [inst : Semiring R] {f : Polyn
omial R}, f.Splits → ∀ (a : R), (Polynomial.C a * f).Splits
· 使用定理 `Polynomial.Splits.X_add_C`：∀ {R : Type u_1} [inst : Semiring R] (a : R),
 (Polynomial.X + Polynomial.C a).Splits
-/
theorem Splits.of_natDegree_le_one {f : R[X]} (hf : natDegree f ≤ 1) : Splits f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · simp_all
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a
/-
**Polynomial.Splits.of_natDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Sp
lits`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionSemiring R] {f : Polynomial R}, f.natDegr
ee = 1 → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_le_one`：∀ {R : Type u_1} [inst : Division
Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → f.Splits
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem Splits.of_natDegree_eq_one {f : R[X]} (hf : natDegree f = 1) : Splits f :=
  of_natDegree_le_one hf.le
/-
**Polynomial.Splits.of_degree_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Split
s`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionSemiring R] {f : Polynomial R}, f.degree 
≤ 1 → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_natDegree_le_one`：∀ {R : Type u_1} [inst : Division
Semiring R] {f : Polynomial R}, f.natDegree ≤ 1 → f.Splits
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem Splits.of_degree_le_one {f : R[X]} (hf : degree f ≤ 1) : Splits f :=
  of_natDegree_le_one (natDegree_le_of_degree_le hf)
/-
**Polynomial.Splits.of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Split
s`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionSemiring R] {f : Polynomial R}, f.degree 
= 1 → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_degree_le_one`：∀ {R : Type u_1} [inst : DivisionSem
iring R] {f : Polynomial R}, f.degree ≤ 1 → f.Splits
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem Splits.of_degree_eq_one {f : R[X]} (hf : degree f = 1) : Splits f :=
  of_degree_le_one hf.le

end DivisionSemiring

section Field

section

variable {S : Type*} [Field R] [CommRing S] [IsDomain S]

/-
**Polynomial.Splits.of_splits_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Field R] [inst_1 : CommRing S] [in
st_2 : IsDomain S] {f : Polynomial R}   (i : R →+* S), (Polynomial.map i f).Spli
ts → (∀ a ∈ (Polynomial.map i f).roots, a ∈ i.range) → f.Splits
参数：i : R →+* S；Polynomial.map i f；∀ a ∈ (Polynomial.map i f).roots, a ∈ i.range。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.of_splits_map_of_injective`：∀ {R : Type u_1} [inst : C
ommRing R] {f : Polynomial R} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : IsD
omain S]   {i : R →+* S},   Functi…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem Splits.of_splits_map {f : R[X]} (i : R →+* S)
    (hf : Splits (f.map i)) (hi : ∀ a ∈ (f.map i).roots, a ∈ i.range) : Splits f :=
  hf.of_splits_map_of_injective i.injective hi
/-
**Polynomial.Splits.roots_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Field R] [inst_1 : CommRing S] [in
st_2 : IsDomain S] {f : Polynomial R},   f.Splits → ∀ (i : R →+* S), (Polynomial
.map i f).roots = Multiset.map (⇑i) f.roots
参数：i : R →+* S；Polynomial.map i f；⇑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.roots_map_of_injective`：∀ {R : Type u_1} [inst : CommR
ing R] {f : Polynomial R} [inst_1 : IsDomain R] {S : Type u_4} [inst_2 : CommRin
g S]   [inst_3 : IsDomain S], …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem Splits.roots_map {f : R[X]} (hf : f.Splits) (i : R →+* S) :
    (f.map i).roots = f.roots.map i :=
  hf.roots_map_of_injective i.injective
/-
**Polynomial.Splits.mem_range_of_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Sp
lits`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Field R] [inst_1 : CommRing S] [Is
Domain S] {f : Polynomial R},   f.Splits → f ≠ 0 → ∀ {i : R →+* S} {x : S}, (Pol
ynomial.map i f).IsRoot x → x ∈ i.range
参数：Polynomial.map i f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Polynomial.Splits.roots_map`：∀ {R : Type u_1} {S : Type u_2} [inst : Fie
ld R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R},   f.Splits
 → ∀ (i : R →+* S…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem Splits.mem_range_of_isRoot {f : R[X]}
    (hf : f.Splits) (hf0 : f ≠ 0) {i : R →+* S} {x : S} (hx : (f.map i).IsRoot x) :
    x ∈ i.range := by
  rw [← mem_roots (map_ne_zero hf0), hf.roots_map, Multiset.mem_map] at hx
  obtain ⟨x, -, hx⟩ := hx
  exact ⟨x, hx⟩
/-
**Polynomial.Splits.aeval_eq_prod_aroots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.S
plits`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Field R] [inst_1 : CommRing S] [in
st_2 : IsDomain S] [inst_3 : Algebra R S]   {f : Polynomial R},   (Polynomial.ma
p (algebraMap R S) f).Splits →     ∀ (x : S),       (Polynomial.aeval x) f = (al
gebraMap R S) f.leadingCoeff * (Multiset.map (fun x_1 => x - x_1) (f.aroots S)).
prod
参数：Polynomial.map (algebraMap R S) f；x : S；Polynomial.aeval x；algebraMap R S；Mul
tiset.map (fun x_1 => x - x_1) (f.aroots S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eval_eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing 
R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → ∀ (x : R), Polynomial.
eval x f = f.leadingCoeff …
· 使用定理 `Polynomial.leadingCoeff_map`：leadingCoeff_map (f : R ->+* S) : (p.map f)
.leadingCoeff = f p.leadingCoeff
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Splits.aeval_eq_prod_aroots [Algebra R S]
    {f : R[X]} (hf : (f.map (algebraMap R S)).Splits) (x : S) :
    f.aeval x = algebraMap R S f.leadingCoeff * ((f.aroots S).map (x - ·)).prod := by
  simp [← eval_map_algebraMap, hf.eval_eq_prod_roots]

end

section

variable {A B : Type*} [CommRing R] [Field A] [Algebra R A]
  [CommRing B] [IsDomain B] [Algebra R B] {f : R[X]}

/-
**Polynomial.Splits.image_rootSet** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : Field A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : IsDomain B]
 [inst_5 : Algebra R B] {f : Polynomial R},   (Polynomial.map (algebraMap R A) f
).Splits → ∀ (g : A →ₐ[R] B), ⇑g '' f.rootSet A = f.rootSet B
参数：Polynomial.map (algebraMap R A) f；g : A →ₐ[R] B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Multiset.toFinset_map`：Multiset.toFinset_map [DecidableEq α] [DecidableE
q β] (f : α -> β) (m : Multiset α) : (m.map f).toFinset = m.toFinset.image f
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用定理 `Polynomial.Splits.roots_map`：∀ {R : Type u_1} {S : Type u_2} [inst : Fie
ld R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R},   f.Splits
 → ∀ (i : R →+* S…
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
-/
theorem Splits.image_rootSet (hf : (f.map (algebraMap R A)).Splits)
    (g : A →ₐ[R] B) : g '' f.rootSet A = f.rootSet B := by
  classical
  rw [rootSet, ← Finset.coe_image, ← Multiset.toFinset_map, ← g.coe_toRingHom,
    ← hf.roots_map, map_map, g.comp_algebraMap, ← rootSet]
/-
**Polynomial.Splits.adjoin_rootSet_eq_range** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l.Splits`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : Field A] [inst_2 : Algebra R A]   [inst_3 : CommRing B] [inst_4 : IsDomain B]
 [inst_5 : Algebra R B] {f : Polynomial R},   (Polynomial.map (algebraMap R A) f
).Splits →     ∀ (g : A →ₐ[R] B), Algebra.adjoin R (f.rootSet B) = g.range ↔ Alg
ebra.adjoin R (f.rootSet A) = ⊤
参数：Polynomial.map (algebraMap R A) f；g : A →ₐ[R] B；f.rootSet B；f.rootSet A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.image_rootSet`：∀ {R : Type u_1} {A : Type u_2} {B : Ty
pe u_3} [inst : CommRing R] [inst_1 : Field A] [inst_2 : Algebra R A]   [inst_3 
: CommRing B] [inst_4…
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subalgebra.map_injective`：map_injective {f : A ->ₐ[R] B} (hf : Function.
Injective f) : Function.Injective (map f)
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem Splits.adjoin_rootSet_eq_range
    (hf : (f.map (algebraMap R A)).Splits) (g : A →ₐ[R] B) :
    Algebra.adjoin R (f.rootSet B) = g.range ↔ Algebra.adjoin R (f.rootSet A) = ⊤ := by
  rw [← hf.image_rootSet g, Algebra.adjoin_image, ← Algebra.map_top]
  exact (Subalgebra.map_injective g.injective).eq_iff

end

section

variable {A B : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [CommRing B]
  [IsDomain B] [Algebra R B] [Algebra A B] [FaithfulSMul A B] [IsScalarTower R A B] {f : R[X]}

/-
**Polynomial.Splits.map_aroots_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Splits`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : IsDomain A]   [inst_3 : Algebra R A] [inst_4 : CommRing
 B] [inst_5 : IsDomain B] [inst_6 : Algebra R B] [inst_7 : Algebra A B]   [Faith
fulSMul A B] [IsScalarTower R A B] {f : Polynomial R},   (Polynomial.map (algebr
aMap R A) f).Splits → Multiset.map (⇑(algebraMap A B)) (f.aroots A) = f.aroots B
参数：Polynomial.map (algebraMap R A) f；⇑(algebraMap A B)；f.aroots A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aroots_map`：aroots_map (p : T[X]) [CommRing S] [Algebra T S] 
[Algebra S R] [Algebra T R] [IsScalarTower T S R] : (p.map (algebraMap T S)).aro
ots R = p.a…
· 使用定理 `Polynomial.aroots.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynomi
al T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Alg
ebra T S], p…
· 使用定理 `Polynomial.Splits.roots_map_of_injective`：∀ {R : Type u_1} [inst : CommR
ing R] {f : Polynomial R} [inst_1 : IsDomain R] {S : Type u_4} [inst_2 : CommRin
g S]   [inst_3 : IsDomain S], …
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem Splits.map_aroots_algebraMap (hf : (f.map (algebraMap R A)).Splits) :
    (f.aroots A).map (algebraMap A B) = f.aroots B := by
  rw [← aroots_map B A, aroots, aroots,
    hf.roots_map_of_injective (FaithfulSMul.algebraMap_injective A B)]
/-
**Polynomial.Splits.image_rootSet_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Splits`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : IsDomain A]   [inst_3 : Algebra R A] [inst_4 : CommRing
 B] [inst_5 : IsDomain B] [inst_6 : Algebra R B] [inst_7 : Algebra A B]   [Faith
fulSMul A B] [IsScalarTower R A B] {f : Polynomial R},   (Polynomial.map (algebr
aMap R A) f).Splits → ⇑(algebraMap A B) '' f.rootSet A = f.rootSet B
参数：Polynomial.map (algebraMap R A) f；algebraMap A B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.rootSet.eq_1`：∀ {T : Type w} [inst : CommRing T] (p : Polynom
ial T) (S : Type u_1) [inst_1 : CommRing S] [inst_2 : IsDomain S]   [inst_3 : Al
gebra T S], p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Multiset.toFinset_map`：Multiset.toFinset_map [DecidableEq α] [DecidableE
q β] (f : α -> β) (m : Multiset α) : (m.map f).toFinset = m.toFinset.image f
· 使用定理 `Polynomial.Splits.map_aroots_algebraMap`：∀ {R : Type u_1} {A : Type u_2}
 {B : Type u_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : IsDomain A] 
  [inst_3 : Algebra R A] [ins…
-/
theorem Splits.image_rootSet_algebraMap (hf : (f.map (algebraMap R A)).Splits) :
    (algebraMap A B) '' f.rootSet A = f.rootSet B := by
  classical
  rw [rootSet, ← Finset.coe_image, ← Multiset.toFinset_map, hf.map_aroots_algebraMap, ← rootSet]

end

variable [Field R] {f g : R[X]}

/-
**Polynomial.Splits.dvd_of_roots_le_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f g : Polynomial R}, f.Splits → f ≠ 0 →
 f.roots ≤ g.roots → f ∣ g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `Polynomial.C_mul_dvd`：C_mul_dvd (ha : a != 0) : C a * p ∣ q ↔ p ∣ q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Multiset.prod_dvd_prod_of_le`：prod_dvd_prod_of_le (h : s <= t) : s.prod 
∣ t.prod
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
· 使用定理 `Polynomial.prod_multiset_X_sub_C_dvd`：prod_multiset_X_sub_C_dvd (p : R[X
]) : (p.roots.map fun a => X - C a).prod ∣ p
-/
theorem Splits.dvd_of_roots_le_roots (hp : f.Splits) (hp0 : f ≠ 0) (hq : f.roots ≤ g.roots) :
    f ∣ g := by
  rw [hp.eq_prod_roots, C_mul_dvd (leadingCoeff_ne_zero.2 hp0)]
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hq)).trans
    (prod_multiset_X_sub_C_dvd _)
/-
**Polynomial.Splits.dvd_iff_roots_le_roots** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f g : Polynomial R}, f.Splits → f ≠ 0 →
 g ≠ 0 → (f ∣ g ↔ f.roots ≤ g.roots)
参数：f ∣ g ↔ f.roots ≤ g.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.roots.le_of_dvd`：∀ {R : Type u} [inst : CommRing R] [inst_1 :
 IsDomain R] {p q : Polynomial R}, q ≠ 0 → p ∣ q → p.roots ≤ q.roots
· 使用定理 `Polynomial.Splits.dvd_of_roots_le_roots`：∀ {R : Type u_1} [inst : Field 
R] {f g : Polynomial R}, f.Splits → f ≠ 0 → f.roots ≤ g.roots → f ∣ g
-/
theorem Splits.dvd_iff_roots_le_roots (hf : f.Splits) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    f ∣ g ↔ f.roots ≤ g.roots :=
  ⟨roots.le_of_dvd hg0, hf.dvd_of_roots_le_roots hf0⟩
/-
**Polynomial.Splits.comp_of_natDegree_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f g : Polynomial R}, f.Splits → g.natDe
gree ≤ 1 → (f.comp g).Splits
参数：f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.comp_zero`：comp_zero : p.comp (0 : R[X]) = C (p.eval 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one_of_invertible`：∀ {R : Type u_
1} [inst : CommSemiring R] {f g : Polynomial R},   f.Splits → g.natDegree ≤ 1 → 
∀ (h : Invertible g.leadingCoeff), (f.comp g).…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
-/
theorem Splits.comp_of_natDegree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.natDegree ≤ 1) :
    (f.comp g).Splits := by
  rcases eq_or_ne g 0 with rfl | hg0
  · simp
  · exact Splits.comp_of_natDegree_le_one_of_invertible hf hg
      (invertibleOfNonzero (leadingCoeff_ne_zero.mpr hg0))
/-
**Polynomial.Splits.comp_of_degree_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f g : Polynomial R}, f.Splits → g.degre
e ≤ 1 → (f.comp g).Splits
参数：f.comp g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one`：∀ {R : Type u_1} [inst : Fie
ld R] {f g : Polynomial R}, f.Splits → g.natDegree ≤ 1 → (f.comp g).Splits
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem Splits.comp_of_degree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.degree ≤ 1) :
    (f.comp g).Splits :=
  hf.comp_of_natDegree_le_one (natDegree_le_of_degree_le hg)
/-
**Polynomial.splits_iff_comp_splits_of_natDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：splits_iff_comp_splits_of_natDegree_eq_one {f g : R[X]} (hg : g.natDegree 
= 1) : f.Splits ↔ (f.comp g).Splits
参数：hg : g.natDegree = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Splits.comp_of_natDegree_le_one`：∀ {R : Type u_1} [inst : Fie
ld R] {f g : Polynomial R}, f.Splits → g.natDegree ≤ 1 → (f.comp g).Splits
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.exists_eq_X_add_C_of_natDegree_le_one`：exists_eq_X_add_C_of_n
atDegree_le_one (h : natDegree p <= 1) : exists a b, p = C a * X + C b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.comp_assoc`：comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : 
R[X]) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ)
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_comp`：mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]
) : (p * q).comp r = p.comp r * q.comp r
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.X_comp`：X_comp : X.comp p = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.C_mul`：C_mul : C (a * b) = C a * C b
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Polynomial.comp_X`：comp_X : p.comp X = p
（共 39 条，此处仅展示前 30 条）
-/
theorem splits_iff_comp_splits_of_natDegree_eq_one {f g : R[X]} (hg : g.natDegree = 1) :
    f.Splits ↔ (f.comp g).Splits := by
  refine ⟨fun hf ↦ hf.comp_of_natDegree_le_one hg.le, fun hf ↦ ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hg.le
  have ha : a ≠ 0 := by contrapose! hg; simp [hg]
  have : f = (f.comp (C a * X + C b)).comp ((C a⁻¹ * (X - C b))) := by
    simp only [comp_assoc, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul, sub_add_cancel, comp_X]
  rw [this]
  refine Splits.comp_of_natDegree_le_one hf ?_
  rw [natDegree_C_mul (mt inv_eq_zero.mp ha), natDegree_X_sub_C]
/-
**Polynomial.splits_iff_comp_splits_of_degree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：splits_iff_comp_splits_of_degree_eq_one {f g : R[X]} (hg : g.degree = 1) :
 f.Splits ↔ (f.comp g).Splits
参数：hg : g.degree = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.splits_iff_comp_splits_of_natDegree_eq_one`：splits_iff_comp_s
plits_of_natDegree_eq_one {f g : R[X]} (hg : g.natDegree = 1) : f.Splits ↔ (f.co
mp g).Splits
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
-/
theorem splits_iff_comp_splits_of_degree_eq_one {f g : R[X]} (hg : g.degree = 1) :
    f.Splits ↔ (f.comp g).Splits :=
  splits_iff_comp_splits_of_natDegree_eq_one (natDegree_eq_of_degree_eq_some hg)
/-
**Polynomial.Splits.degree_eq_one_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f : Polynomial R}, f.Splits → Irreducib
le f → f.degree = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.Splits.degree_le_one_of_irreducible`：∀ {R : Type u_1} [inst :
 CommSemiring R] {f : Polynomial R}, f.Splits → Irreducible f → f.degree ≤ 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `WithBot.one_le_iff_pos`：one_le_iff_pos {α : Type*} [PartialOrder α] [Add
MonoidWithOne α] [ZeroLEOneClass α] [NeZero (1 : α)] [SuccAddOrder α] (a : WithB
ot α) : 1 <=…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
-/
theorem Splits.degree_eq_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : degree f = 1 :=
  le_antisymm (hf.degree_le_one_of_irreducible h)
    ((WithBot.one_le_iff_pos _).mpr (degree_pos_of_irreducible h))
/-
**Polynomial.Splits.natDegree_eq_one_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f : Polynomial R}, f.Splits → Irreducib
le f → f.natDegree = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.Splits.degree_eq_one_of_irreducible`：∀ {R : Type u_1} [inst :
 Field R] {f : Polynomial R}, f.Splits → Irreducible f → f.degree = 1
-/
theorem Splits.natDegree_eq_one_of_irreducible {f : R[X]} (hf : Splits f)
    (h : Irreducible f) : natDegree f = 1 :=
  natDegree_eq_of_degree_eq_some (hf.degree_eq_one_of_irreducible h)
/-
**Polynomial.Splits.eval_derivative_eq_eval_mul_sum** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f : Polynomial R},   f.Splits →     ∀ {
x : R},       Polynomial.eval x f ≠ 0 →         Polynomial.eval x (Polynomial.de
rivative f) =           Polynomial.eval x f * (Multiset.map (fun z => 1 / (x - z
)) f.roots).sum
参数：Polynomial.derivative f；Multiset.map (fun z => 1 / (x - z)) f.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Splits.eval_derivative`：∀ {R : Type u_1} [inst : CommRing R] 
{f : Polynomial R} [inst_1 : IsDomain R] [inst_2 : DecidableEq R],   f.Splits → 
    ∀ (x : R),       Po…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Splits.eval_eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing 
R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → ∀ (x : R), Polynomial.
eval x f = f.leadingCoeff …
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_map_erase`：prod_map_erase [DecidableEq ι] {a : ι} (h : a i
n m) : f a * ((m.erase a).map f).prod = (m.map f).prod
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem Splits.eval_derivative_eq_eval_mul_sum (hf : Splits f) {x : R} (hx : f.eval x ≠ 0) :
    f.derivative.eval x = f.eval x * (f.roots.map fun z ↦ 1 / (x - z)).sum := by
  classical
  simp only [hf.eval_derivative, hf.eval_eq_prod_roots, ← Multiset.sum_map_mul_left, mul_assoc]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz ↦ ?_)
  rw [← Multiset.prod_map_erase hz, mul_one_div, mul_div_cancel_left₀]
  aesop (add simp sub_eq_zero)
/-
**Polynomial.Splits.eval_derivative_div_eval_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f : Polynomial R},   f.Splits →     ∀ {
x : R},       Polynomial.eval x f ≠ 0 →         Polynomial.eval x (Polynomial.de
rivative f) / Polynomial.eval x f =           (Multiset.map (fun z => 1 / (x - z
)) f.roots).sum
参数：Polynomial.derivative f；Multiset.map (fun z => 1 / (x - z)) f.roots。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Splits.eval_derivative_eq_eval_mul_sum`：∀ {R : Type u_1} [ins
t : Field R] {f : Polynomial R},   f.Splits →     ∀ {x : R},       Polynomial.ev
al x f ≠ 0 →         Polynomial.eval x …
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `EuclideanDomain.toMulDivCancelClass`：∀ {R : Type u} [inst : EuclideanDom
ain R], MulDivCancelClass R
-/
theorem Splits.eval_derivative_div_eval_of_ne_zero (hf : Splits f) {x : R} (hx : f.eval x ≠ 0) :
    f.derivative.eval x / f.eval x = (f.roots.map fun z ↦ 1 / (x - z)).sum := by
  rw [hf.eval_derivative_eq_eval_mul_sum hx, mul_div_cancel_left₀ _ hx]
/-
**Polynomial.Splits.mem_subfield_of_isRoot** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
.Splits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] (F : Subfield R) {f : Polynomial ↥F},   
f.Splits → f ≠ 0 → ∀ {x : R}, (Polynomial.map F.subtype f).IsRoot x → x ∈ F
参数：F : Subfield R；Polynomial.map F.subtype f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Polynomial.Splits.mem_range_of_isRoot`：∀ {R : Type u_1} {S : Type u_2} [
inst : Field R] [inst_1 : CommRing S] [IsDomain S] {f : Polynomial R},   f.Split
s → f ≠ 0 → ∀ {i : R →+* S}…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem Splits.mem_subfield_of_isRoot (F : Subfield R) {f : F[X]} (hf : Splits f) (hf0 : f ≠ 0)
    {x : R} (hx : (f.map F.subtype).IsRoot x) : x ∈ F := by
  simpa using hf.mem_range_of_isRoot hf0 hx

/-- A polynomial of degree `2` with a root splits. -/
/-
**Polynomial.Splits.of_natDegree_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Sp
lits`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f : Polynomial R} {x : R}, f.natDegree 
= 2 → Polynomial.eval x f = 0 → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_divByMonic`：natDegree_divByMonic (f : R[X]) {g : R[
X]} (hg : g.Monic) : natDegree (f /ₘ g) = natDegree f - natDegree g
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mul_divByMonic_eq_iff_isRoot`：mul_divByMonic_eq_iff_isRoot : 
(X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a
· 使用定理 `Polynomial.splits_mul`：splits_mul (hf₀ : f != 0) (hg₀ : g != 0) : Splits
 (f * g) ↔ Splits f ∧ Splits g
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.Splits.X_sub_C`：∀ {R : Type u_1} [inst : Ring R] (a : R), (Po
lynomial.X - Polynomial.C a).Splits
· 使用定理 `Polynomial.Splits.of_natDegree_eq_one`：∀ {R : Type u_1} [inst : Division
Semiring R] {f : Polynomial R}, f.natDegree = 1 → f.Splits

--- 原说明 ---
A polynomial of degree `2` with a root splits.
-/
theorem Splits.of_natDegree_eq_two {x : R} (h₁ : f.natDegree = 2) (h₂ : f.eval x = 0) :
    Splits f := by
  have h : (f /ₘ (X - C x)).natDegree = 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C x), h₁, natDegree_X_sub_C]
  rw [← mul_divByMonic_eq_iff_isRoot.mpr h₂, splits_mul (X_sub_C_ne_zero x) (by aesop)]
  exact ⟨Splits.X_sub_C x, Splits.of_natDegree_eq_one h⟩
/-
**Polynomial.Splits.of_degree_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Split
s`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] {f : Polynomial R} {x : R}, f.degree = 2
 → Polynomial.eval x f = 0 → f.Splits
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.Splits.of_natDegree_eq_two`：∀ {R : Type u_1} [inst : Field R]
 {f : Polynomial R} {x : R}, f.natDegree = 2 → Polynomial.eval x f = 0 → f.Split
s
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
-/
theorem Splits.of_degree_eq_two {x : R} (h₁ : f.degree = 2) (h₂ : f.eval x = 0) : Splits f :=
  Splits.of_natDegree_eq_two (natDegree_eq_of_degree_eq_some h₁) h₂

open UniqueFactorizationMonoid in
@[deprecated "Use `Splits.degree_eq_one_of_irreducible` instead." (since := "2026-01-13")]
/-
**Polynomial.splits_iff_splits** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：splits_iff_splits {f : R[X]} : Splits f ↔ f = 0 ∨ forall {g : R[X]}, Irred
ucible g -> g ∣ f -> degree g = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Polynomial.Splits.degree_eq_one_of_irreducible`：∀ {R : Type u_1} [inst :
 Field R] {f : Polynomial R}, f.Splits → Irreducible f → f.degree = 1
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `Polynomial.Splits.mul`：∀ {R : Type u_1} [inst : Semiring R] {f g : Polyn
omial R}, f.Splits → g.Splits → (f * g).Splits
· 使用定理 `Polynomial.Splits.multisetProd`：∀ {R : Type u_1} [inst : CommSemiring R]
 {m : Multiset (Polynomial R)}, (∀ f ∈ m, f.Splits) → m.prod.Splits
· 使用定理 `Polynomial.Splits.of_degree_eq_one`：∀ {R : Type u_1} [inst : DivisionSem
iring R] {f : Polynomial R}, f.degree = 1 → f.Splits
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_factor`：irreducible_of_factor {
a : α} : forall x : α, x in factors a -> Irreducible x
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_factors`：dvd_of_mem_factors {p a : 
α} (h : p in factors a) : p ∣ a
· 使用定理 `IsUnit.splits`：∀ {R : Type u_1} [inst : Semiring R] [NoZeroDivisors R] {
f : Polynomial R}, IsUnit f → f.Splits
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
theorem splits_iff_splits {f : R[X]} :
    Splits f ↔ f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g = 1 := by
  refine ⟨fun hf ↦ or_iff_not_imp_left.mpr fun h0 g hg hgf ↦
    (hf.of_dvd h0 hgf).degree_eq_one_of_irreducible hg, ?_⟩
  rintro (rfl | hf)
  · aesop
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Splits.multisetProd fun g hg ↦ ?_).mul u.isUnit.splits
  exact Splits.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

end Field

noncomputable section

open Polynomial

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

section Splits

section CommRing

variable [CommRing K] [Field L] [Field F]
variable (i : K →+* L)

variable {i}

variable (i)

end CommRing

variable [CommRing R] [Field K] [Field L] [Field F]
variable (i : K →+* L)

section UFD

attribute [local instance] PrincipalIdealRing.to_uniqueFactorizationMonoid

local infixl:50 " ~ᵤ " => Associated

open UniqueFactorizationMonoid Associates

end UFD

variable [Algebra R K] [Algebra R L]

end Splits

end

end Polynomial

