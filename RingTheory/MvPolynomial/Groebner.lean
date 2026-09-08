/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-! # Division algorithm with respect to monomial orders

We provide a division algorithm with respect to monomial orders in polynomial rings.
Let `R` be a commutative ring, `σ` a type of indeterminates and `m : MonomialOrder σ`
a monomial ordering on `σ →₀ ℕ`.

Consider a family of polynomials `b : ι → MvPolynomial σ R` with invertible leading coefficients
(with respect to `m`): we assume `hb : ∀ i, IsUnit (m.leadingCoeff (b i))`.

* `MonomialOrder.div hb f` furnishes
  - a finitely supported family `g : ι →₀ MvPolynomial σ R`
  - and a “remainder” `r : MvPolynomial σ R`
    such that the three properties hold:
    1. One has `f = ∑ (g i) * (b i) + r`
    2. For every `i`, `m.degree ((g i) * (b i)` is less than or equal to that of `f`
    3. For every `i`, every monomial in the support of `r` is strictly smaller
       than the leading term of `b i`,

The proof is done by induction, using two standard constructions

* `MonomialOrder.subLTerm f` deletes the leading term of a polynomial `f`

* `MonomialOrder.reduce hb f` subtracts from `f` the appropriate multiple of `b : MvPolynomial σ R`,
  provided `IsUnit (m.leadingCoeff b)`.

* `MonomialOrder.div_set` is the variant of `MonomialOrder.div` for a set of polynomials.

* `MonomialOrder.div_single` is the variant of `MonomialOrder.div` for a single polynomial.


## Reference : [Becker-Weispfenning1993]

-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

variable (m) in
/-- Delete the leading term in a multivariate polynomial (for some monomial order) -/
/-
**MonomialOrder.subLTerm** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：subLTerm (f : MvPolynomial σ R) : MvPolynomial σ R
参数：f : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Delete the leading term in a multivariate polynomial (for some monomial order)
-/
noncomputable def subLTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  f - monomial (m.degree f) (m.leadingCoeff f)
/-
**MonomialOrder.degree_sub_LTerm_le** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_sub_LTerm_le (f : MvPolynomial σ R) : m.degree (m.subLTerm f) ≼[m] 
m.degree f
参数：f : MvPolynomial σ R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_sub_le`：degree_sub_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f - g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MonomialOrder.degree_monomial_le`：degree_monomial_le {d : σ ->₀ Nat} (c 
: R) : m.degree (monomial d c) ≼[m] d
-/
theorem degree_sub_LTerm_le (f : MvPolynomial σ R) :
    m.degree (m.subLTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le
/-
**MonomialOrder.degree_sub_LTerm_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_sub_LTerm_lt {f : MvPolynomial σ R} (hf : m.degree f != 0) : m.degr
ee (m.subLTerm f) ≺[m] m.degree f
参数：hf : m.degree f != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `MonomialOrder.degree_sub_LTerm_le`：degree_sub_LTerm_le (f : MvPolynomial
 σ R) : m.degree (m.subLTerm f) ≼[m] m.degree f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonomialOrder.coeff_degree_ne_zero_iff`：coeff_degree_ne_zero_iff {f : Mv
Polynomial σ R} : f.coeff (m.degree f) != 0 ↔ f != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem degree_sub_LTerm_lt {f : MvPolynomial σ R} (hf : m.degree f ≠ 0) :
    m.degree (m.subLTerm f) ≺[m] m.degree f := by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f ≠ 0 := by
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m), hf'] at this
  apply this
  simp [subLTerm, coeff_monomial, leadingCoeff]

variable (m) in
/-- Reduce a polynomial modulo a polynomial with unit leading term (for some monomial order) -/
noncomputable
/-
**MonomialOrder.reduce** 是 Mathlib 中的一个定义，位于命名空间 `MonomialOrder`。
形式化陈述：reduce {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : MvPoly
nomial σ R) : MvPolynomial σ R
参数：hb : IsUnit (m.leadingCoeff b)；f : MvPolynomial σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def reduce {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
  f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.leadingCoeff f) * b
/-
**MonomialOrder.degree_reduce_lt** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：degree_reduce_lt {f b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
 (hbf : m.degree b <= m.degree f) (hf : m.degree f != 0) : m.degree (m.reduce hb
 f) ≺[m] m.degree f
参数：hb : IsUnit (m.leadingCoeff b)；hbf : m.degree b <= m.degree f；hf : m.degree f
 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.degree_monomial`：degree_monomial {d : σ ->₀ Nat} (c : R) [
Decidable (c = 0)] : m.degree (monomial d c) = if c = 0 then 0 else d
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MonomialOrder.coeff_mul_of_degree_add`：coeff_mul_of_degree_add {f g : Mv
Polynomial σ R} : (f * g).coeff (m.degree f + m.degree g) = m.leadingCoeff f * m
.leadingCoeff g
· 使用定理 `MonomialOrder.leadingCoeff_monomial`：leadingCoeff_monomial {d : σ ->₀ Na
t} (c : R) : m.leadingCoeff (monomial d c) = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MonomialOrder.leadingCoeff.eq_1`：∀ {σ : Type u_1} (m : MonomialOrder σ) 
{R : Type u_2} [inst : CommSemiring R] (f : MvPolynomial σ R),   m.leadingCoeff 
f = MvPolynomial.coef…
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_sub_le`：degree_sub_le {f g : MvPolynomial σ R} : m.
toSyn (m.degree (f - g)) <= m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
（共 32 条，此处仅展示前 30 条）
-/
theorem degree_reduce_lt {f b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
    (hbf : m.degree b ≤ m.degree f) (hf : m.degree f ≠ 0) :
    m.degree (m.reduce hb f) ≺[m] m.degree f := by
  have H : m.degree f =
      m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.leadingCoeff f)) +
        m.degree b := by
    classical
    rw [degree_monomial, if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, leadingCoeff_eq_zero_iff]
      intro hf0
      apply hf
      simp [hf0]
  have H' : coeff (m.degree f) (m.reduce hb f) = 0 := by
    simp only [reduce, coeff_sub, sub_eq_zero]
    nth_rewrite 2 [H]
    rw [coeff_mul_of_degree_add (m := m), leadingCoeff_monomial, mul_comm, ← mul_assoc,
      IsUnit.mul_val_inv, one_mul, ← leadingCoeff]
  rw [lt_iff_le_and_ne]
  constructor
  · classical
    apply le_trans degree_sub_le
    simp only [sup_le_iff, le_refl, true_and]
    apply le_of_le_of_eq degree_mul_le
    rw [m.toSyn.injective.eq_iff]
    exact H.symm
  · intro K
    simp only [EmbeddingLike.apply_eq_iff_eq] at K
    nth_rewrite 1 [← K] at H'
    rw [← leadingCoeff, leadingCoeff_eq_zero_iff] at H'
    rw [H', degree_zero] at K
    exact hf K.symm

/-- Division by a family of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order -/
/-
**MonomialOrder.div** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：div {ι : Type*} {b : ι -> MvPolynomial σ R} (hb : forall i, IsUnit (m.lead
ingCoeff (b i))) (f : MvPolynomial σ R) : exists (g : ι ->₀ (MvPolynomial σ R)) 
(r : MvPolynomial σ R), f = Finsupp.linearCombination _ b g + r ∧ (forall i, m.d
egree (b i * (g i)) ≼[m] m.degree f) ∧ (forall c in r.support, forall i, ¬ (m.de
gree (b i) <= c))
参数：hb : forall i, IsUnit (m.leadingCoeff (b i))；f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isWellFounded_iff`：∀ (α : Type u) (r : α → α → Prop), IsWellFounded α r 
↔ WellFounded r
· 使用定理 `MonomialOrder.wellFoundedLT_syn`：∀ {σ : Type u_1} (self : MonomialOrder 
σ), WellFoundedLT self.syn
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonomialOrder.eq_C_of_degree_eq_zero`：eq_C_of_degree_eq_zero {f : MvPoly
nomial σ R} (hf : m.degree f = 0) : f = C (m.leadingCoeff f)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MvPolynomial.smul_eq_C_mul`：smul_eq_C_mul (p : MvPolynomial σ R) (a : R)
 : a • p = C a * p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MonomialOrder.degree_mul_le`：degree_mul_le {f g : MvPolynomial σ R} : m.
degree (f * g) ≼[m] m.degree f + m.degree g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonomialOrder.degree_smul_of_isRegular`：degree_smul_of_isRegular {r : R}
 (hr : IsRegular r) {f : MvPolynomial σ R} : m.degree (r • f) = m.degree f
· 使用定理 `Units.isRegular`：Units.isRegular (a : Rˣ) : IsRegular (a : R)
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MonomialOrder.degree_zero`：degree_zero : m.degree (0 : MvPolynomial σ R)
 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
Division by a family of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order
-/
theorem div {ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : ∀ i, IsUnit (m.leadingCoeff (b i))) (f : MvPolynomial σ R) :
    ∃ (g : ι →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ b g + r ∧
        (∀ i, m.degree (b i * (g i)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ i, ¬ (m.degree (b i) ≤ c)) := by
  by_cases! hb' : ∃ i, m.degree (b i) = 0
  · obtain ⟨i, hb0⟩ := hb'
    use Finsupp.single i ((hb i).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      nth_rewrite 2 [eq_C_of_degree_eq_zero hb0]
      rw [mul_comm, smul_eq_C_mul]
    constructor
    · intro j
      by_cases hj : j = i
      · apply le_trans degree_mul_le
        simp only [hj, hb0, Finsupp.single_eq_same, zero_add]
        apply le_of_eq
        simp only [EmbeddingLike.apply_eq_iff_eq]
        apply degree_smul_of_isRegular (Units.isRegular _)
      · simp only [Finsupp.single_eq_of_ne hj, mul_zero, degree_zero, map_zero]
        apply bot_le
    · simp
  by_cases hf0 : f = 0
  · refine ⟨0, 0, by simp [hf0], ?_, by simp⟩
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
    exact bot_le
  by_cases! hf : ∃ i, m.degree (b i) ≤ m.degree f
  · obtain ⟨i, hf⟩ := hf
    have deg_reduce : m.degree (m.reduce (hb i) f) ≺[m] m.degree f := by
      apply degree_reduce_lt (hb i) hf
      intro hf0'
      apply hb' i
      simpa [hf0'] using hf
    obtain ⟨g', r', H'⟩ := div hb (m.reduce (hb i) f)
    use g' +
      Finsupp.single i (monomial (m.degree f - m.degree (b i)) ((hb i).unit⁻¹ * m.leadingCoeff f))
    use r'
    constructor
    · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
      simp [reduce]
    constructor
    · rintro j
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [mul_add]
      apply le_trans degree_add_le
      simp only [sup_le_iff]
      constructor
      · exact le_trans (H'.2.1 _) (le_of_lt deg_reduce)
      · classical
        rw [Finsupp.single_apply]
        split_ifs with hc
        · subst j
          grw [degree_mul_le, map_add, degree_monomial_le, ← map_add, add_tsub_cancel_of_le hf]
        · simp only [mul_zero, degree_zero, map_zero]
          exact bot_le
    · exact H'.2.2
  · suffices ∃ (g' : ι →₀ MvPolynomial σ R), ∃ r',
        (m.subLTerm f = Finsupp.linearCombination (MvPolynomial σ R) b g' + r') ∧
        (∀ i, m.degree ((b i) * (g' i)) ≼[m] m.degree (m.subLTerm f)) ∧
        (∀ c ∈ r'.support, ∀ i, ¬ m.degree (b i) ≤ c) by
      obtain ⟨g', r', H'⟩ := this
      use g', r' + monomial (m.degree f) (m.leadingCoeff f)
      constructor
      · simp [← add_assoc, ← H'.1, subLTerm]
      constructor
      · exact fun b ↦ le_trans (H'.2.1 b) (degree_sub_LTerm_le f)
      · intro c hc i
        by_cases hc' : c ∈ r'.support
        · exact H'.2.2 c hc' i
        · convert! hf i
          classical
          have := MvPolynomial.support_add hc
          rw [Finset.mem_union, Classical.or_iff_not_imp_left] at this
          simpa only [Finset.mem_singleton] using support_monomial_subset (this hc')
    by_cases hf'0 : m.subLTerm f = 0
    · refine ⟨0, 0, by simp [hf'0], ?_, by simp⟩
      intro b
      simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
      exact bot_le
    · exact (div hb) (m.subLTerm f)
termination_by WellFounded.wrap
  ((isWellFounded_iff m.syn fun x x_1 ↦ x < x_1).mp m.wellFoundedLT_syn) (m.toSyn (m.degree f))
decreasing_by
  · exact deg_reduce
  · apply degree_sub_LTerm_lt
    intro hf0
    apply hf'0
    simp only [subLTerm, sub_eq_zero]
    nth_rewrite 1 [eq_C_of_degree_eq_zero hf0, hf0]
    simp

/-!
Module doc as workaround for a parser error that prevents using `set_option`
after a `decreasing_by` block with focus dots.

See https://github.com/leanprover/lean4/issues/12573
-/

/-- Division by a *set* of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order -/
/-
**MonomialOrder.div_set** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：div_set {B : Set (MvPolynomial σ R)} (hB : forall b in B, IsUnit (m.leadin
gCoeff b)) (f : MvPolynomial σ R) : exists (g : B ->₀ (MvPolynomial σ R)) (r : M
vPolynomial σ R), f = Finsupp.linearCombination _ (fun (b : B) => (b : MvPolynom
ial σ R)) g + r ∧ (forall (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m
] m.degree f) ∧ (forall c in r.support, forall b in B, ¬ (m.degree b <= c))
参数：MvPolynomial σ R；hB : forall b in B, IsUnit (m.leadingCoeff b)；f : MvPolynomi
al σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.div`：div {ι : Type*} {b : ι -> MvPolynomial σ R} (hb : for
all i, IsUnit (m.leadingCoeff (b i))) (f : MvPolynomial σ R) : exists (g : ι ->₀
 (MvPol…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Division by a *set* of multivariate polynomials
whose leading coefficients are invertible with respect to a monomial order
-/
theorem div_set {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    ∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R),
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧
        (∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) := by
  obtain ⟨g, r, H⟩ := m.div (b := fun (p : B) ↦ p) (fun b ↦ hB b b.prop) f
  exact ⟨g, r, H.1, H.2.1, fun c hc b hb ↦ H.2.2 c hc ⟨b, hb⟩⟩

/-- Division by a multivariate polynomial
whose leading coefficient is invertible with respect to a monomial order -/
/-
**MonomialOrder.div_single** 是 Mathlib 中的一个定理，位于命名空间 `MonomialOrder`。
形式化陈述：div_single {b : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b)) (f : Mv
Polynomial σ R) : exists (g : MvPolynomial σ R) (r : MvPolynomial σ R), f = g * 
b + r ∧ (m.degree (b * g) ≼[m] m.degree f) ∧ (forall c in r.support, ¬ (m.degree
 b <= c))
参数：hb : IsUnit (m.leadingCoeff b)；f : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonomialOrder.div_set`：div_set {B : Set (MvPolynomial σ R)} (hB : forall
 b in B, IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) : exists (g : B ->₀ (
MvPolynomia…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Finsupp.sum_eq_single`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M} (a : α)   {g : α → M → N}
, (∀ (b : α…
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
Division by a multivariate polynomial
whose leading coefficient is invertible with respect to a monomial order
-/
theorem div_single {b : MvPolynomial σ R}
    (hb : IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    ∃ (g : MvPolynomial σ R) (r : MvPolynomial σ R),
      f = g * b + r ∧
        (m.degree (b * g) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ¬ (m.degree b ≤ c)) := by
  obtain ⟨g, r, hgr, h1, h2⟩ := div_set (B := {b}) (m := m) (by simp [hb]) f
  specialize h1 ⟨b, by simp⟩
  set q := g ⟨b, by simp⟩
  simp only [Set.mem_singleton_iff, forall_eq] at h2
  simp only at h1
  refine ⟨q, r, ?_, h1, h2⟩
  rw [hgr]
  simp only [Finsupp.linearCombination, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe,
    id_eq, smul_eq_mul, add_left_inj]
  rw [Finsupp.sum_eq_single ⟨b, by simp⟩ _ (by simp)]
  simp +contextual

end MonomialOrder

