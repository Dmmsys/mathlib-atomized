/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Separable

/-!

# Separable degree

This file contains basics about the separable degree of a polynomial.

## Main results

- `IsSeparableContraction`: is the condition that, for `g` a separable polynomial, we have that
  `g(x^(q^m)) = f(x)` for some `m : ℕ`.
- `HasSeparableContraction`: the condition of having a separable contraction
- `HasSeparableContraction.degree`: the separable degree, defined as the degree of some
  separable contraction
- `Irreducible.hasSeparableContraction`: any irreducible polynomial can be contracted
  to a separable polynomial
- `HasSeparableContraction.dvd_degree'`: the degree of a separable contraction divides the degree,
  in function of the exponential characteristic of the field
- `HasSeparableContraction.dvd_degree` and `HasSeparableContraction.eq_degree` specialize the
  statement of `separable_degree_dvd_degree`
- `IsSeparableContraction.degree_eq`: the separable degree is well-defined, implemented as the
  statement that the degree of any separable contraction equals `HasSeparableContraction.degree`

## Tags

separable degree, degree, polynomial
-/

@[expose] public section

noncomputable section

namespace Polynomial

open Polynomial

section CommSemiring

variable {F : Type*} [CommSemiring F] (q : ℕ)

/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`. -/
/-
**Polynomial.IsSeparableContraction** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：IsSeparableContraction (f : F[X]) (g : F[X]) : Prop
参数：f : F[X]；g : F[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A separable contraction of a polynomial `f` is a separable polynomial `g` such t
hat
`g(x^(q^m)) = f(x)` for some `m : ℕ`.
-/
def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ ∃ m : ℕ, expand F (q ^ m) g = f

/-- The condition of having a separable contraction. -/
/-
**Polynomial.HasSeparableContraction** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：HasSeparableContraction (f : F[X]) : Prop
参数：f : F[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition of having a separable contraction.
-/
def HasSeparableContraction (f : F[X]) : Prop :=
  ∃ g : F[X], IsSeparableContraction q f g

variable {q} {f : F[X]} (hf : HasSeparableContraction q f)

/-- A choice of a separable contraction. -/
/-
**Polynomial.HasSeparableContraction.contraction** 是 Mathlib 中的一个定义，位于命名空间 `Poly
nomial.HasSeparableContraction`。
形式化陈述：{F : Type u_1} →   [inst : CommSemiring F] → {q : ℕ} → {f : Polynomial F} 
→ Polynomial.HasSeparableContraction q f → Polynomial F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of a separable contraction.
-/
def HasSeparableContraction.contraction : F[X] :=
  Classical.choose hf

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
/-
**Polynomial.HasSeparableContraction.degree** 是 Mathlib 中的一个定义，位于命名空间 `Polynomia
l.HasSeparableContraction`。
形式化陈述：{F : Type u_1} → [inst : CommSemiring F] → {q : ℕ} → {f : Polynomial F} → 
Polynomial.HasSeparableContraction q f → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The separable degree of a polynomial is the degree of a given separable contract
ion.
-/
def HasSeparableContraction.degree : ℕ :=
  hf.contraction.natDegree

/-- The `HasSeparableContraction.contraction` is indeed a separable contraction. -/
/-
**Polynomial.HasSeparableContraction.isSeparableContraction** 是 Mathlib 中的一个定理，位
于命名空间 `Polynomial.HasSeparableContraction`。
形式化陈述：∀ {F : Type u_1} [inst : CommSemiring F] {q : ℕ} {f : Polynomial F} (hf : 
Polynomial.HasSeparableContraction q f),   Polynomial.IsSeparableContraction q f
 hf.contraction
参数：hf : Polynomial.HasSeparableContraction q f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The `HasSeparableContraction.contraction` is indeed a separable contraction.
-/
theorem HasSeparableContraction.isSeparableContraction :
    IsSeparableContraction q f hf.contraction := Classical.choose_spec hf

/-- The separable degree divides the degree, in function of the exponential characteristic of F. -/
/-
**Polynomial.IsSeparableContraction.dvd_degree'** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial.IsSeparableContraction`。
形式化陈述：∀ {F : Type u_1} [inst : CommSemiring F] {q : ℕ} {f g : Polynomial F},   P
olynomial.IsSeparableContraction q f g → ∃ m, g.natDegree * q ^ m = f.natDegree
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_expand`：natDegree_expand (p : Nat) (f : R[X]) : (ex
pand R p f).natDegree = f.natDegree * p

--- 原说明 ---
The separable degree divides the degree, in function of the exponential characte
ristic of F.
-/
theorem IsSeparableContraction.dvd_degree' {g} (hf : IsSeparableContraction q f g) :
    ∃ m : ℕ, g.natDegree * q ^ m = f.natDegree := by
  obtain ⟨m, rfl⟩ := hf.2
  use m
  rw [natDegree_expand]
/-
**Polynomial.HasSeparableContraction.dvd_degree'** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.HasSeparableContraction`。
形式化陈述：∀ {F : Type u_1} [inst : CommSemiring F] {q : ℕ} {f : Polynomial F} (hf : 
Polynomial.HasSeparableContraction q f),   ∃ m, hf.degree * q ^ m = f.natDegree
参数：hf : Polynomial.HasSeparableContraction q f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsSeparableContraction.dvd_degree'`：∀ {F : Type u_1} [inst : 
CommSemiring F] {q : ℕ} {f g : Polynomial F},   Polynomial.IsSeparableContractio
n q f g → ∃ m, g.natDegree * q ^ m …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem HasSeparableContraction.dvd_degree' : ∃ m : ℕ, hf.degree * q ^ m = f.natDegree :=
  (Classical.choose_spec hf).dvd_degree'

/-- The separable degree divides the degree. -/
/-
**Polynomial.HasSeparableContraction.dvd_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial.HasSeparableContraction`。
形式化陈述：∀ {F : Type u_1} [inst : CommSemiring F] {q : ℕ} {f : Polynomial F} (hf : 
Polynomial.HasSeparableContraction q f),   hf.degree ∣ f.natDegree
参数：hf : Polynomial.HasSeparableContraction q f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.HasSeparableContraction.dvd_degree'`：∀ {F : Type u_1} [inst :
 CommSemiring F] {q : ℕ} {f : Polynomial F} (hf : Polynomial.HasSeparableContrac
tion q f),   ∃ m, hf.degree * q ^ m …
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b

--- 原说明 ---
The separable degree divides the degree.
-/
theorem HasSeparableContraction.dvd_degree : hf.degree ∣ f.natDegree :=
  let ⟨a, ha⟩ := hf.dvd_degree'
  Dvd.intro (q ^ a) ha

/-- In exponential characteristic one, the separable degree equals the degree. -/
/-
**Polynomial.HasSeparableContraction.eq_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial.HasSeparableContraction`。
形式化陈述：∀ {F : Type u_1} [inst : CommSemiring F] {f : Polynomial F} (hf : Polynomi
al.HasSeparableContraction 1 f),   hf.degree = f.natDegree
参数：hf : Polynomial.HasSeparableContraction 1 f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.HasSeparableContraction.dvd_degree'`：∀ {F : Type u_1} [inst :
 CommSemiring F] {q : ℕ} {f : Polynomial F} (hf : Polynomial.HasSeparableContrac
tion q f),   ∃ m, hf.degree * q ^ m …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
In exponential characteristic one, the separable degree equals the degree.
-/
theorem HasSeparableContraction.eq_degree {f : F[X]} (hf : HasSeparableContraction 1 f) :
    hf.degree = f.natDegree := by
  let ⟨a, ha⟩ := hf.dvd_degree'
  rw [← ha, one_pow a, mul_one]

end CommSemiring

section Field

variable {F : Type*} [Field F]
variable (q : ℕ) {f : F[X]} (hf : HasSeparableContraction q f)

/-- Every irreducible polynomial can be contracted to a separable polynomial. -/
@[stacks 09H0]
/-
**Polynomial._root_.Irreducible.hasSeparableContraction** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every irreducible polynomial can be contracted to a separable polynomial.
-/
theorem _root_.Irreducible.hasSeparableContraction (q : ℕ) [hF : ExpChar F q] {f : F[X]}
    (irred : Irreducible f) : HasSeparableContraction q f := by
  cases hF
  · exact ⟨f, irred.separable, ⟨0, by rw [pow_zero, expand_one]⟩⟩
  · rcases exists_separable_of_irreducible q irred ‹q.Prime›.ne_zero with ⟨n, g, hgs, hge⟩
    exact ⟨g, hgs, n, hge⟩

/-- If two expansions (along the positive characteristic) of two separable polynomials `g` and `g'`
agree, then they have the same degree. -/
/-
**Polynomial.contraction_degree_eq_or_insep** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：contraction_degree_eq_or_insep [hq : NeZero q] [CharP F q] (g g' : F[X]) (
m m' : Nat) (h_expand : expand F (q ^ m) g = expand F (q ^ m') g') (hg : g.Separ
able) (hg' : g'.Separable) : g.natDegree = g'.natDegree
参数：g g' : F[X]；m m' : Nat；h_expand : expand F (q ^ m) g = expand F (q ^ m') g'；h
g : g.Separable；hg' : g'.Separable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Polynomial.isUnit_or_eq_zero_of_separable_expand`：isUnit_or_eq_zero_of_s
eparable_expand {f : F[X]} (n : Nat) (hp : 0 < p) (hf : (expand F (p ^ n) f).Sep
arable) : IsUnit f ∨ n = 0
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_expand`：natDegree_expand (p : Nat) (f : R[X]) : (ex
pand R p f).natDegree = f.natDegree * p
· 使用引理 `Polynomial.natDegree_eq_zero_of_isUnit`：natDegree_eq_zero_of_isUnit (h :
 IsUnit p) : natDegree p = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.expand_inj`：expand_inj {p : Nat} (hp : 0 < p) {f g : R[X]} : 
expand R p f = expand R p g ↔ f = g
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Polynomial.expand_mul`：expand_mul (f : R[X]) : expand R (p * q) f = expa
nd R p (expand R q f)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a

--- 原说明 ---
If two expansions (along the positive characteristic) of two separable polynomia
ls `g` and `g'`
agree, then they have the same degree.
-/
theorem contraction_degree_eq_or_insep [hq : NeZero q] [CharP F q] (g g' : F[X]) (m m' : ℕ)
    (h_expand : expand F (q ^ m) g = expand F (q ^ m') g') (hg : g.Separable) (hg' : g'.Separable) :
    g.natDegree = g'.natDegree := by
  wlog hm : m ≤ m'
  · exact (this q g' g m' m h_expand.symm hg' hg (le_of_not_ge hm)).symm
  obtain ⟨s, rfl⟩ := exists_add_of_le hm
  rw [pow_add, expand_mul, expand_inj (pow_pos (NeZero.pos q) m)] at h_expand
  subst h_expand
  rcases isUnit_or_eq_zero_of_separable_expand q s (NeZero.pos q) hg with (h | rfl)
  · rw [natDegree_expand, natDegree_eq_zero_of_isUnit h, zero_mul]
  · rw [natDegree_expand, pow_zero, mul_one]

/-- The separable degree equals the degree of any separable contraction, i.e., it is unique. -/
/-
**Polynomial.IsSeparableContraction.degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.IsSeparableContraction`。
形式化陈述：∀ {F : Type u_1} [inst : Field F] (q : ℕ) {f : Polynomial F} (hf : Polynom
ial.HasSeparableContraction q f)   [hF : ExpChar F q] (g : Polynomial F), Polyno
mial.IsSeparableContraction q f g → g.natDegree = hf.degree
参数：q : ℕ；hf : Polynomial.HasSeparableContraction q f；g : Polynomial F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.HasSeparableContraction.eq_degree`：∀ {F : Type u_1} [inst : C
ommSemiring F] {f : Polynomial F} (hf : Polynomial.HasSeparableContraction 1 f),
   hf.degree = f.natDegree
· 使用定理 `Polynomial.expand_one`：expand_one (f : R[X]) : expand R 1 f = f
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Polynomial.contraction_degree_eq_or_insep`：contraction_degree_eq_or_inse
p [hq : NeZero q] [CharP F q] (g g' : F[X]) (m m' : Nat) (h_expand : expand F (q
 ^ m) g = expand F (q ^ m') g')…
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)

--- 原说明 ---
The separable degree equals the degree of any separable contraction, i.e., it is
 unique.
-/
theorem IsSeparableContraction.degree_eq [hF : ExpChar F q] (g : F[X])
    (hg : IsSeparableContraction q f g) : g.natDegree = hf.degree := by
  cases hF
  · rcases hg with ⟨_, m, hm⟩
    rw [one_pow, expand_one] at hm
    rw [hf.eq_degree, hm]
  · rcases hg with ⟨hg, m, hm⟩
    let g' := Classical.choose hf
    obtain ⟨hg', m', hm'⟩ := Classical.choose_spec hf
    have : Fact q.Prime := ⟨by assumption⟩
    refine contraction_degree_eq_or_insep q g g' m m' ?_ hg hg'
    rw [hm, hm']

end Field

end Polynomial

