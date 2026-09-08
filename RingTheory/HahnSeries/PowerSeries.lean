/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.Data.Finsupp.PWO

/-!
# Comparison between Hahn series and power series

If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `R⟦Γ⟧`.  When `R` is a semiring and `Γ = ℕ`, then
we get the more familiar semiring of formal power series with coefficients in `R`.

## Main Definitions
* `toPowerSeries` the isomorphism from `R⟦ℕ⟧` to `PowerSeries R`.
* `ofPowerSeries` the inverse, casting a `PowerSeries R` to a `R⟦ℕ⟧`.

## Instances
* For `Finite σ`, the instance `NoZeroDivisors R⟦σ →₀ ℕ⟧`,
  deduced from the case of `MvPowerSeries`
  The case of `R⟦ℕ⟧` is taken care of by `instNoZeroDivisors`.

## TODO
* Build an API for the variable `X` (defined to be `single 1 1 : R⟦Γ⟧`) in analogy to
  `X : R[X]` and `X : PowerSeries R`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function Pointwise Polynomial

noncomputable section

variable {Γ R : Type*}

namespace HahnSeries

section Semiring

variable [Semiring R]

/-- The ring `R⟦ℕ⟧` is isomorphic to `PowerSeries R`. -/
@[simps]
/-
**HahnSeries.toPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：toPowerSeries : R⟦Nat⟧ ≃+* PowerSeries R where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring `R⟦ℕ⟧` is isomorphic to `PowerSeries R`.
-/
def toPowerSeries : R⟦ℕ⟧ ≃+* PowerSeries R where
  toFun f := PowerSeries.mk f.coeff
  invFun f := ⟨fun n => PowerSeries.coeff n f, .of_linearOrder _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_mk, coeff_mul]
    classical
    refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
      sum_filter_ne_zero _
    ext m
    simp only [HasAntidiagonal.mem_antidiagonal, Finset.mem_antidiagonal, and_congr_left_iff,
      mem_filter, mem_support]
    rintro h
    rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]
/-
**HahnSeries.coeff_toPowerSeries** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_toPowerSeries {f : R⟦Nat⟧} {n : Nat} : PowerSeries.coeff n (toPowerS
eries f) = f.coeff n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
theorem coeff_toPowerSeries {f : R⟦ℕ⟧} {n : ℕ} :
    PowerSeries.coeff n (toPowerSeries f) = f.coeff n :=
  PowerSeries.coeff_mk _ _
/-
**HahnSeries.coeff_toPowerSeries_symm** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_toPowerSeries_symm {f : PowerSeries R} {n : Nat} : (HahnSeries.toPow
erSeries.symm f).coeff n = PowerSeries.coeff n f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_toPowerSeries_symm {f : PowerSeries R} {n : ℕ} :
    (HahnSeries.toPowerSeries.symm f).coeff n = PowerSeries.coeff n f :=
  rfl

variable (Γ R) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/-- Casts a power series as a Hahn series with coefficients from a strictly ordered semiring. -/
/-
**HahnSeries.ofPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeries : PowerSeries R ->+* R⟦Γ⟧
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R

--- 原说明 ---
Casts a power series as a Hahn series with coefficients from a strictly ordered 
semiring.
-/
def ofPowerSeries : PowerSeries R →+* R⟦Γ⟧ :=
  (HahnSeries.embDomainRingHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (RingEquiv.toRingHom toPowerSeries.symm)

variable {Γ R}
/-
**HahnSeries.ofPowerSeries_injective** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `HahnSeries.embDomain_injective`：embDomain_injective {f : Γ ↪o Γ'} : Func
tion.Injective (embDomain f : R⟦Γ⟧ -> R⟦Γ'⟧)
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
-/
theorem ofPowerSeries_injective : Function.Injective (ofPowerSeries Γ R) :=
  embDomain_injective.comp toPowerSeries.symm.injective

-- Not `@[simp]` since the RHS is more complicated and it makes linter failures elsewhere
/-
**HahnSeries.ofPowerSeries_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeries_apply (x : PowerSeries R) : ofPowerSeries Γ R x = embDomain 
Nat.castOrderEmbedding (toPowerSeries.symm x)
参数：x : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem ofPowerSeries_apply (x : PowerSeries R) :
    ofPowerSeries Γ R x = embDomain Nat.castOrderEmbedding (toPowerSeries.symm x) :=
  rfl
/-
**HahnSeries.ofPowerSeries_apply_coeff** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeries_apply_coeff (x : PowerSeries R) (n : Nat) : (ofPowerSeries Γ
 R x).coeff n = PowerSeries.coeff n x
参数：x : PowerSeries R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.toPowerSeries_symm_apply_coeff`：∀ {R : Type u_2} [inst : Semi
ring R] (f : PowerSeries R) (n : ℕ),   (HahnSeries.toPowerSeries.symm f).coeff n
 = (PowerSeries.coeff n) f
-/
theorem ofPowerSeries_apply_coeff (x : PowerSeries R) (n : ℕ) :
    (ofPowerSeries Γ R x).coeff n = PowerSeries.coeff n x := by
  trans (embDomain (Nat.castOrderEmbedding (α := Γ)) (toPowerSeries.symm x)).coeff
    (Nat.castOrderEmbedding n)
  · simp [ofPowerSeries_apply]
  rw [embDomain_coeff]
  simp

@[simp]
/-
**HahnSeries.ofPowerSeries_C** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C r) = HahnSeries
.C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_single`：coeff_single : (single a r).coeff b = if b = a 
then r else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.toPowerSeries_symm_apply_coeff`：∀ {R : Type u_2} [inst : Semi
ring R] (f : PowerSeries R) (n : ℕ),   (HahnSeries.toPowerSeries.symm f).coeff n
 = (PowerSeries.coeff n) f
· 使用定理 `PowerSeries.coeff_zero_C`：coeff_zero_C (a : R) : coeff 0 (C a) = a
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `HahnSeries.embDomain_notin_image_support`：embDomain_notin_image_support 
{f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ f '' x.support) : (embDomain f x).co
eff b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.coeff_C`：coeff_C (n : Nat) (a : R) : coeff n (C a : R⟦X⟧) = 
if n = 0 then a else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 33 条，此处仅展示前 30 条）
-/
theorem ofPowerSeries_C (r : R) : ofPowerSeries Γ R (PowerSeries.C r) = HahnSeries.C r := by
  ext n
  simp only [ofPowerSeries_apply, C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_single]
  split_ifs with hn
  · subst hn
    convert! embDomain_coeff (a := 0) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_C]
    intro
    simp +contextual [Ne.symm hn]

@[simp]
/-
**HahnSeries.ofPowerSeries_X** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.coeff_single`：coeff_single : (single a r).coeff b = if b = a 
then r else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.castOrderEmbedding_apply`：∀ {α : Type u_1} [inst : AddMonoidWithOne 
α] [inst_1 : PartialOrder α] [inst_2 : AddLeftMono α]   [inst_3 : ZeroLEOneClass
 α] [inst_4 : Char…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.toPowerSeries_symm_apply_coeff`：∀ {R : Type u_2} [inst : Semi
ring R] (f : PowerSeries R) (n : ℕ),   (HahnSeries.toPowerSeries.symm f).coeff n
 = (PowerSeries.coeff n) f
· 使用定理 `PowerSeries.coeff_one_X`：coeff_one_X : coeff 1 (X : R⟦X⟧) = 1
· 使用定理 `HahnSeries.embDomain_coeff`：embDomain_coeff {f : Γ ↪o Γ'} {x : R⟦Γ⟧} {a 
: Γ} : (embDomain f x).coeff (f a) = x.coeff a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `HahnSeries.embDomain_notin_image_support`：embDomain_notin_image_support 
{f : Γ ↪o Γ'} {x : R⟦Γ⟧} {b : Γ'} (hb : b ∉ f '' x.support) : (embDomain f x).co
eff b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 33 条，此处仅展示前 30 条）
-/
theorem ofPowerSeries_X : ofPowerSeries Γ R PowerSeries.X = single 1 1 := by
  ext n
  simp only [coeff_single, ofPowerSeries_apply]
  split_ifs with hn
  · rw [hn]
    convert! embDomain_coeff (a := 1) <;> simp
  · rw [embDomain_notin_image_support]
    simp only [not_exists, Set.mem_image, toPowerSeries_symm_apply_coeff, mem_support,
      PowerSeries.coeff_X]
    intro
    simp +contextual [Ne.symm hn]
/-
**HahnSeries.ofPowerSeries_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeries_X_pow {R} [Semiring R] (n : Nat) : ofPowerSeries Γ R (PowerS
eries.X ^ n) = single (n : Γ) 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `HahnSeries.ofPowerSeries_X`：ofPowerSeries_X : ofPowerSeries Γ R PowerSer
ies.X = single 1 1
· 使用定理 `HahnSeries.single_pow`：single_pow (a : Γ) (n : Nat) (r : R) : single a r
 ^ n = single (n • a) (r ^ n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofPowerSeries_X_pow {R} [Semiring R] (n : ℕ) :
    ofPowerSeries Γ R (PowerSeries.X ^ n) = single (n : Γ) 1 := by
  simp

set_option backward.isDefEq.respectTransparency false in
-- Lemmas converting Hahn series over a finite index type to and from `MvPowerSeries`
/-- The ring `R⟦σ →₀ ℕ⟧` is isomorphic to `MvPowerSeries σ R` for a `Finite` `σ`.
We take the index set of the hahn series to be `Finsupp` rather than `pi`,
even though we assume `Finite σ` as this is more natural for alignment with `MvPowerSeries`.
After importing `Mathlib/Algebra/Order/Pi.lean` the ring `R⟦σ → ℕ⟧` could be constructed
instead.
-/
@[simps]
/-
**HahnSeries.toMvPowerSeries** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：toMvPowerSeries {σ : Type*} [Finite σ] : R⟦σ ->₀ Nat⟧ ≃+* MvPowerSeries σ 
R where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring `R⟦σ →₀ ℕ⟧` is isomorphic to `MvPowerSeries σ R` for a `Finite` `σ`.
We take the index set of the hahn series to be `Finsupp` rather than `pi`,
even though we assume `Finite σ` as this is more natural for alignment with `MvP
owerSeries`.
After importing `Mathlib/Algebra/Order/Pi.lean` the ring `R⟦σ → ℕ⟧` could be con
structed
instead.
-/
def toMvPowerSeries {σ : Type*} [Finite σ] : R⟦σ →₀ ℕ⟧ ≃+* MvPowerSeries σ R where
  toFun f := f.coeff
  invFun f := ⟨(f : (σ →₀ ℕ) → R), Set.isPWO_of_wellQuasiOrderedLE _⟩
  left_inv f := by
    ext
    simp
  right_inv f := by
    ext
    simp
  map_add' f g := by
    ext
    simp
  map_mul' f g := by
    ext n
    classical
      change (f * g).coeff n = _
      simp_rw [coeff_mul]
      refine (sum_filter_ne_zero _).symm.trans <| (sum_congr ?_ fun _ _ ↦ rfl).trans <|
        sum_filter_ne_zero _
      ext m
      simp only [and_congr_left_iff, Finset.mem_antidiagonal, mem_filter, mem_support,
        HasAntidiagonal.mem_antidiagonal]
      rintro h
      rw [and_iff_right (left_ne_zero_of_mul h), and_iff_right (right_ne_zero_of_mul h)]

variable {σ : Type*} [Finite σ]

-- TODO : generalize to all (?) rings of Hahn Series
/-- If R has no zero divisors and `σ` is finite,
then `R⟦σ →₀ ℕ⟧` has no zero divisors -/
/-
**HahnSeries.** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If R has no zero divisors and `σ` is finite,
then `R⟦σ →₀ ℕ⟧` has no zero divisors
-/
instance [NoZeroDivisors R] : NoZeroDivisors (R⟦σ →₀ ℕ⟧) :=
  toMvPowerSeries.toMulEquiv.noZeroDivisors (A := R⟦σ →₀ ℕ⟧) (MvPowerSeries σ R)
/-
**HahnSeries.coeff_toMvPowerSeries** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_toMvPowerSeries {f : R⟦σ ->₀ Nat⟧} {n : σ ->₀ Nat} : MvPowerSeries.c
oeff n (toMvPowerSeries f) = f.coeff n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_toMvPowerSeries {f : R⟦σ →₀ ℕ⟧} {n : σ →₀ ℕ} :
    MvPowerSeries.coeff n (toMvPowerSeries f) = f.coeff n :=
  rfl
/-
**HahnSeries.coeff_toMvPowerSeries_symm** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ ->₀ Nat} : (Hahn
Series.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff n f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_toMvPowerSeries_symm {f : MvPowerSeries σ R} {n : σ →₀ ℕ} :
    (HahnSeries.toMvPowerSeries.symm f).coeff n = MvPowerSeries.coeff n f :=
  rfl

end Semiring

section Algebra

variable (R) [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

/-- The `R`-algebra `A⟦ℕ⟧` is isomorphic to `PowerSeries A`. -/
@[simps!]
/-
**HahnSeries.toPowerSeriesAlg** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：toPowerSeriesAlg : A⟦Nat⟧ ≃ₐ[R] PowerSeries A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-algebra `A⟦ℕ⟧` is isomorphic to `PowerSeries A`.
-/
def toPowerSeriesAlg : A⟦ℕ⟧ ≃ₐ[R] PowerSeries A :=
  { toPowerSeries with
    commutes' := fun r => by
      ext n
      cases n <;> simp [algebraMap_apply, PowerSeries.algebraMap_apply] }

variable (Γ) [Semiring Γ] [PartialOrder Γ] [IsStrictOrderedRing Γ]

/-- Casting a power series as a Hahn series with coefficients from a strictly ordered semiring. -/
@[simps!]
/-
**HahnSeries.ofPowerSeriesAlg** 是 Mathlib 中的一个定义，位于命名空间 `HahnSeries`。
形式化陈述：ofPowerSeriesAlg : PowerSeries A ->ₐ[R] A⟦Γ⟧
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R

--- 原说明 ---
Casting a power series as a Hahn series with coefficients from a strictly ordere
d semiring.
-/
def ofPowerSeriesAlg : PowerSeries A →ₐ[R] A⟦Γ⟧ :=
  (HahnSeries.embDomainAlgHom (Nat.castAddMonoidHom Γ) Nat.strictMono_cast.injective fun _ _ =>
        Nat.cast_le).comp
    (AlgEquiv.toAlgHom (toPowerSeriesAlg R).symm)
/-
**HahnSeries.powerSeriesAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `HahnSeries`。
形式化陈述：powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)
] : Algebra S R⟦Γ⟧
参数：PowerSeries R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
instance powerSeriesAlgebra {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)] :
    Algebra S R⟦Γ⟧ :=
  RingHom.toAlgebra <| (ofPowerSeries Γ R).comp (algebraMap S (PowerSeries R))

variable {R}
variable {S : Type*} [CommSemiring S] [Algebra S (PowerSeries R)]
/-
**HahnSeries.algebraMap_apply'** 是 Mathlib 中的一个定理，位于命名空间 `HahnSeries`。
形式化陈述：algebraMap_apply' (x : S) : algebraMap S R⟦Γ⟧ x = ofPowerSeries Γ R (algeb
raMap S (PowerSeries R) x)
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
theorem algebraMap_apply' (x : S) :
    algebraMap S R⟦Γ⟧ x = ofPowerSeries Γ R (algebraMap S (PowerSeries R) x) :=
  rfl

@[simp]
/-
**HahnSeries._root_.Polynomial.algebraMap_hahnSeries_apply** 是 Mathlib 中的一个定理，位于
命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.algebraMap_hahnSeries_apply (f : R[X]) :
    algebraMap R[X] R⟦Γ⟧ f = ofPowerSeries Γ R f :=
  rfl
/-
**HahnSeries._root_.Polynomial.algebraMap_hahnSeries_injective** 是 Mathlib 中的一个定
理，位于命名空间 `HahnSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.algebraMap_hahnSeries_injective :
    Function.Injective (algebraMap R[X] R⟦Γ⟧) :=
  ofPowerSeries_injective.comp (Polynomial.coe_injective R)

end Algebra

end HahnSeries

