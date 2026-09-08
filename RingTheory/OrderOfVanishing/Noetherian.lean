/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/

module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Order of vanishing in Noetherian rings.

In this file we define various properties of the order of vanishing in Noetherian rings, including
some API for computing the order of vanishing in discrete valuation rings.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace Ring

section NoetherianDimLEOne

variable {R : Type*} [CommRing R]
variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors
/--
Order of vanishing function as a monoid homomorphism
-/
noncomputable
/-
**Ring.ordMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Ring`。
形式化陈述：ordMonoidHom : R⁰ ->* Multiplicative Nat where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ordMonoidHom : R⁰ →* Multiplicative ℕ where
  toFun x := .ofAdd <| (Ring.ord R x).toNat
  map_one' := by simp [OneMemClass.coe_one, isUnit_one, ord_of_isUnit]
  map_mul' x y := by simp [ord_mul, ENat.toNat_add (ord_ne_top x.2) (ord_ne_top y.2)]

@[simp]
/-
**Ring.ordMonoidHom_eq_ord** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordMonoidHom_eq_ord (x : R⁰) : (ordMonoidHom x).toAdd = Ring.ord R x
参数：x : R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
· 使用引理 `Ring.ord_ne_top`：ord_ne_top {a : R} (ha : a in nonZeroDivisors R) : ord 
R a != ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma ordMonoidHom_eq_ord (x : R⁰) : (ordMonoidHom x).toAdd = Ring.ord R x :=
  (ENat.natCast_toNat (ord_ne_top x.2))

@[simp]
/-
**Ring.ordMonoidWithZeroHom_eq_ordMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordMonoidWithZeroHom_eq_ordMonoidHom [Nontrivial R] (x : R⁰) : .coe (.ofAd
d ((ordMonoidHom x).toAdd : Int)) = ordMonoidWithZeroHom R x
参数：x : R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.ordMonoidWithZeroHom_eq_ord`：ordMonoidWithZeroHom_eq_ord [Nontrivia
l R] {x : R} (h : x in nonZeroDivisors R) : ordMonoidWithZeroHom R x = (ENat.rec
TopCoe 0 (WithZero.coe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Ring.ord_lt_top`：ord_lt_top {a : R} (ha : a in nonZeroDivisors R) : ord 
R a < ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_lift`：∀ (x : ℕ∞) (h : x < ⊤), ↑(x.lift h) = x
· 使用定理 `ENat.recTopCoe_natCast`：recTopCoe_natCast {C : Nat∞ -> Sort*} (d : C ⊤) 
(f : forall a : Nat, C a) (x : Nat) : @recTopCoe C d f ↑x = f x
· 使用定理 `ENat.lift_eq_toNat_of_lt_top`：lift_eq_toNat_of_lt_top {x : Nat∞} (hx : x
 < ⊤) : x.lift hx = x.toNat
-/
lemma ordMonoidWithZeroHom_eq_ordMonoidHom [Nontrivial R] (x : R⁰) :
    .coe (.ofAdd ((ordMonoidHom x).toAdd : ℤ)) = ordMonoidWithZeroHom R x := by
  simp only [SetLike.coe_mem, ordMonoidWithZeroHom_eq_ord, ordMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd]
  rw [← ENat.natCast_lift (ord R x.1) (ord_lt_top x.2), ENat.recTopCoe_natCast,
    ENat.natCast_lift, ENat.lift_eq_toNat_of_lt_top]

/--
Analogue of `ord_ne_top` for `ordMonoidWithZeroHom`.
-/
/-
**Ring.ordMonoidWithZeroHom_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordMonoidWithZeroHom_ne_zero [Nontrivial R] {a : R} (ha : a in nonZeroDivi
sors R) : ordMonoidWithZeroHom R a != 0
参数：ha : a in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Analogue of `ord_ne_top` for `ordMonoidWithZeroHom`.
-/
lemma ordMonoidWithZeroHom_ne_zero [Nontrivial R] {a : R} (ha : a ∈ nonZeroDivisors R) :
    ordMonoidWithZeroHom R a ≠ 0 := by
  lift a to R⁰ using ha
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom]

variable [Nontrivial R]

/--
Helper lemma to pass between the orders on `ℕ∞` and `ℤᵐ⁰` (which notably have different behaviour at
`∞`). Note that here we're using the fact that the order of any non zero divisor is finite, hence
the assumptions on the ring.
-/
/-
**Ring.ord_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ord_le_iff {a b : R} (ha : a in nonZeroDivisors R) (hb : b in nonZeroDivis
ors R) : ord R a <= ord R b ↔ ordMonoidWithZeroHom R a <= ordMonoidWithZeroHom R
 b
参数：ha : a in nonZeroDivisors R；hb : b in nonZeroDivisors R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Helper lemma to pass between the orders on `ℕ∞` and `ℤᵐ⁰` (which notably have di
fferent behaviour at
`∞`). Note that here we're using the fact that the order of any non zero divisor
 is finite, hence
the assumptions on the ring.
-/
lemma ord_le_iff {a b : R} (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    ord R a ≤ ord R b ↔ ordMonoidWithZeroHom R a ≤ ordMonoidWithZeroHom R b := by
  lift a to R⁰ using ha
  lift b to R⁰ using hb
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom, ← ordMonoidHom_eq_ord]

end NoetherianDimLEOne

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/--
In a discrete valuation ring, `ord R x` is the same as `addVal R x`. We prefer the second spelling
here for most purposes.
-/
@[simp]
/-
**Ring.ord_eq_addVal** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ord_eq_addVal (x : R) : ord R x = IsDiscreteValuationRing.addVal R x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddValuation.map_zero`：AddValuation.map_zero : addValuationDef (0 : Rat_
[p]) = ⊤
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isFiniteLength_iff_isNoetherian_isArtinian`：isFiniteLength_iff_isNoether
ian_isArtinian : IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M
· 使用引理 `Module.length_ne_top_iff`：Module.length_ne_top_iff : Module.length R M !
= ⊤ ↔ IsFiniteLength R M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearEquiv.isArtinian_iff`：LinearEquiv.isArtinian_iff (f : M ≃ₗ[R] P) :
 IsArtinian R M ↔ IsArtinian R P
· 使用定理 `Ideal.span_singleton_zero`：span_singleton_zero : span ({0} : Set α) = ⊥
· 使用引理 `IsDiscreteValuationRing.not_krullDimLE_zero`：IsDiscreteValuationRing.not
_krullDimLE_zero [IsDomain R] [IsDiscreteValuationRing R] : ¬ KrullDimLE 0 R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ
· 使用定理 `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`：eq_unit_mul_pow_irr
educible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists (n : Nat)
 (u : Rˣ), x = u * ϖ ^ n
· 使用定理 `Ring.ord_mul`：ord_mul {a b : R} (hb : b in nonZeroDivisors R) : ord R (a
 * b) = ord R a + ord R b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ring.ord_pow`：ord_pow {x : R} (hx : x in nonZeroDivisors R) (n : Nat) : 
ord R (x ^ n) = n • ord R x
· 使用定理 `Ring.ord_of_irreducible`：ord_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ)
 : ord R ϖ = 1
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
In a discrete valuation ring, `ord R x` is the same as `addVal R x`. We prefer t
he second spelling
here for most purposes.
-/
lemma ord_eq_addVal (x : R) : ord R x = IsDiscreteValuationRing.addVal R x := by
  by_cases hx : x = 0
  · simp only [ord, hx, AddValuation.map_zero]
    subst hx
    by_contra!
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at this
    have art := this.2
    rw [Ideal.span_singleton_zero] at art
    have : IsArtinianRing R :=
      (LinearEquiv.isArtinian_iff (Submodule.quotEquivOfEqBot ⊥ rfl).symm).mpr art
    exact IsDiscreteValuationRing.not_krullDimLE_zero R inferInstance
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_mul, ord_pow, ord_of_irreducible hϖ]
  · simp [IsDiscreteValuationRing.addVal_uniformizer hϖ]
  all_goals simp_all [Irreducible.ne_zero hϖ]

open IsDiscreteValuationRing
/-
**Ring.ord_eq_iff_associated** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ord_eq_iff_associated (x y : R) : ord R x = ord R y ↔ Associated x y
参数：x y : R。
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
· 使用引理 `Ring.ord_eq_addVal`：ord_eq_addVal (x : R) : ord R x = IsDiscreteValuatio
nRing.addVal R x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ord_eq_iff_associated (x y : R) :
    ord R x = ord R y ↔ Associated x y := by simp [addVal_eq_iff_associated]

/--
For `x y : R` where `R` is a discrete valuation ring, we have that
`min (ord R x) (ord R y) ≤ ord R (x + y)`. It should be noted that the order
we're using here is the order on `ℕ∞`, where `⊤` is greater than everything else.
This is relevant since when we're working with `ordFrac` we work with `ℤᵐ⁰`, where the
order instance has the `0` element less than everything else.
-/
/-
**Ring.ord_add** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：ord_add (x y : R) : min (Ring.ord R x) (Ring.ord R y) <= Ring.ord R (x + y
)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ring.ord_eq_addVal`：ord_eq_addVal (x : R) : ord R x = IsDiscreteValuatio
nRing.addVal R x
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `IsDiscreteValuationRing.addVal_add`：addVal_add {a b : R} : min (addVal R
 a) (addVal R b) <= addVal R (a + b)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For `x y : R` where `R` is a discrete valuation ring, we have that
`min (ord R x) (ord R y) ≤ ord R (x + y)`. It should be noted that the order
we're using here is the order on `ℕ∞`, where `⊤` is greater than everything else
.
This is relevant since when we're working with `ordFrac` we work with `ℤᵐ⁰`, whe
re the
order instance has the `0` element less than everything else.
-/
theorem ord_add (x y : R) : min (Ring.ord R x) (Ring.ord R y) ≤ Ring.ord R (x + y) := by
  grw [ord_eq_addVal x, ord_eq_addVal y, ord_eq_addVal (x + y), IsDiscreteValuationRing.addVal_add]

end IsDiscreteValuationRing

section ordFrac

variable [IsDomain R] [IsNoetherianRing R] [KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
For any nonzero `x : R`, `ordFrac R (algebraMap R K x) ≥ 1`. Note here that this last
expression is in `ℤᵐ⁰`, so the syntax may be slightly different than expected. Namely,
the `1` here is `WithZero.exp 0`, and so would usually be written as `0` in the additive
context. Further, the order here is different to similar lemmas involving `Ring.ord`, since
here the order is on `ℤᵐ⁰` has the `∞` element less than everything else, whereas in `Ring.ord`
we work with the order on `ℕ∞` where the `∞` element is interpreted as a `⊤` element.
-/
/-
**Ring.ordFrac_ge_one_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordFrac_ge_one_of_ne_zero {x : R} (hx : x != 0) : 1 <= ordFrac R (algebraM
ap R K x)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENat.ne_top_iff_exists`：ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m 
= n
· 使用引理 `Ring.ord_ne_top`：ord_ne_top {a : R} (ha : a in nonZeroDivisors R) : ord 
R a != ⊤
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ring.ordFrac_eq_ord`：ordFrac_eq_ord {x : R} (hx : x != 0) : ordFrac R (a
lgebraMap R K x) = ordMonoidWithZeroHom R x
· 使用引理 `Ring.ordMonoidWithZeroHom_eq_coe`：ordMonoidWithZeroHom_eq_coe [Nontrivia
l R] {x : R} (hx : x in nonZeroDivisors R) {n : Nat} (hn : Ring.ord R x = n) : o
rdMonoidWithZeroHom R …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
For any nonzero `x : R`, `ordFrac R (algebraMap R K x) ≥ 1`. Note here that this
 last
expression is in `ℤᵐ⁰`, so the syntax may be slightly different than expected. N
amely,
the `1` here is `WithZero.exp 0`, and so would usually be written as `0` in the 
additive
context. Further, the order here is different to similar lemmas involving `Ring.
ord`, since
here the order is on `ℤᵐ⁰` has the `∞` element less than everything else, wherea
s in `Ring.ord`
we work with the order on `ℕ∞` where the `∞` element is interpreted as a `⊤` ele
ment.
-/
lemma ordFrac_ge_one_of_ne_zero {x : R} (hx : x ≠ 0) :
    1 ≤ ordFrac R (algebraMap R K x) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ord_ne_top (a := x) (by simpa))
  simp_rw [ordFrac_eq_ord R hx, ordMonoidWithZeroHom_eq_coe _ (by simpa) hm.symm,
    WithZero.one_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le, Nat.cast_nonneg _]
/-
**Ring.ordFrac_le_smul** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordFrac_le_smul {S : Type*} [CommRing S] [Algebra S R] [Algebra S K] [IsSc
alarTower S R K] (a : S) (ha : algebraMap S R a != 0) (f : K) : Ring.ordFrac R f
 <= Ring.ordFrac R (a • f)
参数：a : S；ha : algebraMap S R a != 0；f : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Ring.ordFrac_ge_one_of_ne_zero`：ordFrac_ge_one_of_ne_zero {x : R} (hx : 
x != 0) : 1 <= ordFrac R (algebraMap R K x)
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma ordFrac_le_smul {S : Type*} [CommRing S] [Algebra S R] [Algebra S K]
    [IsScalarTower S R K] (a : S) (ha : algebraMap S R a ≠ 0) (f : K) :
    Ring.ordFrac R f ≤ Ring.ordFrac R (a • f) := by
  by_cases j : f = 0
  · simp [j]
  suffices ordFrac R f ≤ ordFrac R (algebraMap S K a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  simp only [smul_eq_mul, map_mul]
  apply le_mul_of_one_le_left'
  simp [IsScalarTower.algebraMap_eq S R K, ordFrac_ge_one_of_ne_zero ha]

@[simp]
/-
**Ring.ordFrac_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordFrac_of_isUnit {x : R} (hx : IsUnit x) : ordFrac R (algebraMap R K x) =
 1
参数：hx : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ring.ordFrac_eq_ord`：ordFrac_eq_ord {x : R} (hx : x != 0) : ordFrac R (a
lgebraMap R K x) = ordMonoidWithZeroHom R x
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `Ring.ordMonoidWithZeroHom_eq_ord`：ordMonoidWithZeroHom_eq_ord [Nontrivia
l R] {x : R} (h : x in nonZeroDivisors R) : ordMonoidWithZeroHom R x = (ENat.rec
TopCoe 0 (WithZero.coe…
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰
· 使用引理 `Ring.ord_of_isUnit`：ord_of_isUnit {x : R} (hx : IsUnit x) : ord R x = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ordFrac_of_isUnit {x : R} (hx : IsUnit x) : ordFrac R (algebraMap R K x) = 1 := by
  simp [ordFrac_eq_ord R (IsUnit.ne_zero hx), IsUnit.mem_nonZeroDivisors hx,
      ordMonoidWithZeroHom_eq_ord, ord_of_isUnit hx]

end ordFrac
section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-
**Ring.ordMonoidWithZeroHom_eq_intValuation** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordMonoidWithZeroHom_eq_intValuation {x : R} (h : x in nonZeroDivisors R) 
: (ordMonoidWithZeroHom R) x = ((IsDiscreteValuationRing.maximalIdeal R).intValu
ation x)⁻¹
参数：h : x in nonZeroDivisors R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.ordMonoidWithZeroHom_eq_ord`：ordMonoidWithZeroHom_eq_ord [Nontrivia
l R] {x : R} (h : x in nonZeroDivisors R) : ordMonoidWithZeroHom R x = (ENat.rec
TopCoe 0 (WithZero.coe…
· 使用引理 `Ring.ord_eq_addVal`：ord_eq_addVal (x : R) : ord R x = IsDiscreteValuatio
nRing.addVal R x
· 使用引理 `IsDiscreteValuationRing.intValuation_maximalIdeal`：intValuation_maximalI
deal (x : A) : (maximalIdeal A).intValuation x = (ENat.recTopCoe 0 (WithZero.coe
 <| Multiplicative.ofAdd <| Nat.cast · …
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ordMonoidWithZeroHom_eq_intValuation {x : R} (h : x ∈ nonZeroDivisors R) :
    (ordMonoidWithZeroHom R) x = ((IsDiscreteValuationRing.maximalIdeal R).intValuation x)⁻¹ := by
  simp [ordMonoidWithZeroHom_eq_ord h, IsDiscreteValuationRing.intValuation_maximalIdeal]
/-
**Ring.ordFrac_eq_intValuation** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordFrac_eq_intValuation {x : R} (h : x != 0) : (ordFrac R) ((algebraMap R 
K) x) = ((IsDiscreteValuationRing.maximalIdeal R).intValuation x)⁻¹
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ring.ordFrac_eq_ord`：ordFrac_eq_ord {x : R} (hx : x != 0) : ordFrac R (a
lgebraMap R K x) = ordMonoidWithZeroHom R x
· 使用引理 `Ring.ordMonoidWithZeroHom_eq_intValuation`：ordMonoidWithZeroHom_eq_intVa
luation {x : R} (h : x in nonZeroDivisors R) : (ordMonoidWithZeroHom R) x = ((Is
DiscreteValuationRing.maximalId…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
lemma ordFrac_eq_intValuation {x : R} (h : x ≠ 0) : (ordFrac R) ((algebraMap R K) x) =
    ((IsDiscreteValuationRing.maximalIdeal R).intValuation x)⁻¹ := by
  rw [ordFrac_eq_ord R h,
      ordMonoidWithZeroHom_eq_intValuation (mem_nonZeroDivisors_of_ne_zero h)]
/-
**Ring.ordFrac_eq_inverse_comp_valuation** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：ordFrac_eq_inverse_comp_valuation : ordFrac R = MonoidWithZeroHom.comp Mon
oidWithZero.inverse ((IsDiscreteValuationRing.maximalIdeal R).valuation K).toMon
oidWithZeroHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用引理 `Ring.ordFrac_eq_intValuation`：ordFrac_eq_intValuation {x : R} (h : x != 
0) : (ordFrac R) ((algebraMap R K) x) = ((IsDiscreteValuationRing.maximalIdeal R
).intValuation x)⁻…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `IsDiscreteValuationRing.intValuation_maximalIdeal`：intValuation_maximalI
deal (x : A) : (maximalIdeal A).intValuation x = (ENat.recTopCoe 0 (WithZero.coe
 <| Multiplicative.ofAdd <| Nat.cast · …
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
（共 31 条，此处仅展示前 30 条）
-/
theorem ordFrac_eq_inverse_comp_valuation :
    ordFrac R = MonoidWithZeroHom.comp MonoidWithZero.inverse
    ((IsDiscreteValuationRing.maximalIdeal R).valuation K).toMonoidWithZeroHom := by
  ext a
  by_cases ha : a = 0
  · simp_all
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  simp_all [ordFrac_eq_intValuation _, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal]
/-
**Ring.ordFrac_eq_valuation_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：ordFrac_eq_valuation_inv (x : K) : ordFrac R x = ((IsDiscreteValuationRing
.maximalIdeal R).valuation K x)⁻¹
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.ordFrac_eq_inverse_comp_valuation`：ordFrac_eq_inverse_comp_valuatio
n : ordFrac R = MonoidWithZeroHom.comp MonoidWithZero.inverse ((IsDiscreteValuat
ionRing.maximalIdeal R).valu…
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordFrac_eq_valuation_inv (x : K) :
    ordFrac R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹ := by
  simp [ordFrac_eq_inverse_comp_valuation]
/-
**Ring.ordFrac_irreducible** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：ordFrac_irreducible {ϖ : R} (hϖ : Irreducible ϖ) : ordFrac R (algebraMap R
 K ϖ) = WithZero.exp 1
参数：hϖ : Irreducible ϖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Ring.ordFrac_eq_valuation_inv`：ordFrac_eq_valuation_inv (x : K) : ordFra
c R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap`：valuation_of
_algebraMap (r : R) : v.valuation K r = v.intValuation r
· 使用引理 `IsDiscreteValuationRing.intValuation_maximalIdeal`：intValuation_maximalI
deal (x : A) : (maximalIdeal A).intValuation x = (ENat.recTopCoe 0 (WithZero.coe
 <| Multiplicative.ofAdd <| Nat.cast · …
· 使用定理 `IsDiscreteValuationRing.addVal_uniformizer`：addVal_uniformizer {ϖ : R} (
hϖ : Irreducible ϖ) : addVal R ϖ = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ordFrac_irreducible
    {ϖ : R} (hϖ : Irreducible ϖ) : ordFrac R (algebraMap R K ϖ) = WithZero.exp 1 := by
  simp [ordFrac_eq_valuation_inv, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, ← WithZero.exp_eq_coe_ofAdd]

open IsDedekindDomain HeightOneSpectrum
/-
**Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing** 是 Mathlib 中的一个引理，位于命名
空间 `Ring`。
形式化陈述：isUnit_iff_ordFrac_one_of_isDiscreteValuationRing {x : R} : IsUnit x ↔ ord
Frac R (algebraMap R K x) = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.ordFrac_eq_valuation_inv`：ordFrac_eq_valuation_inv (x : K) : ordFra
c R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isUnit_iff_ordFrac_one_of_isDiscreteValuationRing {x : R} :
    IsUnit x ↔ ordFrac R (algebraMap R K x) = 1 := by
  simp [ordFrac_eq_valuation_inv, IsDiscreteValuationRing.maximalIdeal]
/-
**Ring.mker_ordFrac_eq_isUnitSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：mker_ordFrac_eq_isUnitSubmonoid : MonoidHom.mker (ordFrac R) = (IsUnit.sub
monoid R).map (algebraMap R K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.ordFrac_eq_inverse_comp_valuation`：ordFrac_eq_inverse_comp_valuatio
n : ordFrac R = MonoidWithZeroHom.comp MonoidWithZero.inverse ((IsDiscreteValuat
ionRing.maximalIdeal R).valu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.comap_mker`：MonoidWithZeroHom.comap_mker {M N P : Type
*} [MulZeroOneClass M] [MulZeroOneClass N] [MulZeroOneClass P] (g : N ->*₀ P) (f
 : M ->*₀ N) : Sub…
· 使用引理 `MonoidWithZeroHom.mker_inverse`：mker_inverse [CommGroupWithZero H] : Mon
oidHom.mker (MonoidWithZero.inverse (M
· 使用引理 `IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid`：mker_valuatio
n_eq_isUnitSubmonoid : MonoidHom.mker ((IsDiscreteValuationRing.maximalIdeal A).
valuation K) = (IsUnit.submonoid A).map (algebr…
-/
lemma mker_ordFrac_eq_isUnitSubmonoid :
    MonoidHom.mker (ordFrac R) = (IsUnit.submonoid R).map (algebraMap R K) := by
  rw [ordFrac_eq_inverse_comp_valuation, ← MonoidWithZeroHom.comap_mker,
      MonoidWithZeroHom.mker_inverse]
  exact IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid

/--
For `x y : R`, if `x + y ≠ 0` then `min (ordFrac R x) (ordFrac R y) ≤ ordFrac R (x + y)`. The
condition that `x + y ≠ 0` is used to guarantee that all the elements we're taking `ordFrac` of
are nonzero, meaning none of them will be `0` in `ℤᵐ⁰`. This allows us to use `ord_add` (which
uses the ordering on `ℕ∞`), since these orders correspond on non `⊤` elements.
-/
/-
**Ring.ordFrac_add** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：ordFrac_add (x y : K) (h1 : x + y != 0) : min (Ring.ordFrac R x) (Ring.ord
Frac R y) <= Ring.ordFrac R (x + y)
参数：x y : K；h1 : x + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.ordFrac_eq_valuation_inv`：ordFrac_eq_valuation_inv (x : K) : ordFra
c R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `instPosMulStrictMonoWithZeroOfMulLeftStrictMono`：∀ {α : Type u_1} [inst 
: Mul α] [inst_1 : Preorder α] [MulLeftStrictMono α], PosMulStrictMono (WithZero
 α)
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `instMulPosStrictMonoWithZeroOfMulRightStrictMono`：∀ {α : Type u_1} [inst
 : Mul α] [inst_1 : Preorder α] [MulRightStrictMono α], MulPosStrictMono (WithZe
ro α)
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
For `x y : R`, if `x + y ≠ 0` then `min (ordFrac R x) (ordFrac R y) ≤ ordFrac R 
(x + y)`. The
condition that `x + y ≠ 0` is used to guarantee that all the elements we're taki
ng `ordFrac` of
are nonzero, meaning none of them will be `0` in `ℤᵐ⁰`. This allows us to use `o
rd_add` (which
uses the ordering on `ℕ∞`), since these orders correspond on non `⊤` elements.
-/
theorem ordFrac_add (x y : K) (h1 : x + y ≠ 0) :
    min (Ring.ordFrac R x) (Ring.ordFrac R y) ≤ Ring.ordFrac R (x + y) := by
  simp only [ordFrac_eq_valuation_inv]
  grw [Valuation.map_add, min_inv_inv_le]
  simpa [WithZero.pos_iff_ne_zero]
/-
**Ring.associated_of_ordFrac_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：associated_of_ordFrac_eq (x y : K) (h : ordFrac R x = ordFrac R y) : exist
s u : Rˣ, u • x = y
参数：x y : K；h : ordFrac R x = ordFrac R y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `instKrullDimLEOfNatNatOfIsDiscreteValuationRing`：∀ (R : Type u_1) [inst 
: CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R], Ring.KrullDimLE
 1 R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsDiscreteValuationRing.associated_of_valuation_eq`：associated_of_valuat
ion_eq (x y : K) (h : ((maximalIdeal A).valuation K) x = ((maximalIdeal A).valua
tion K) y) : exists u : Aˣ, u • x = y
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inj`：inv_inj : a⁻¹ = b⁻¹ ↔ a = b
· 使用定理 `Ring.ordFrac_eq_valuation_inv`：ordFrac_eq_valuation_inv (x : K) : ordFra
c R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹
-/
theorem associated_of_ordFrac_eq (x y : K)
    (h : ordFrac R x = ordFrac R y) : ∃ u : Rˣ, u • x = y := by
  rw [ordFrac_eq_valuation_inv, ordFrac_eq_valuation_inv, inv_inj] at h
  exact IsDiscreteValuationRing.associated_of_valuation_eq _ _ h

end IsDiscreteValuationRing

end Ring

