/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluation of power series in Hahn Series

We describe a class of ring homomorphisms from formal power series to Hahn series,
given by substitution of the generating variable to an element of strictly positive order.

## Main Definitions
* `HahnSeries.SummableFamily.powerSeriesFamily`: A summable family of Hahn series whose elements
  are non-negative powers of a fixed positive-order Hahn series multiplied by the coefficients of a
  formal power series.
* `PowerSeries.heval`: The `R`-algebra homomorphism from `PowerSeries σ R` to `R⟦Γ⟧` that
  takes `X` to a fixed positive-order Hahn Series and extends to formal infinite sums.

## TODO
* `MvPowerSeries.heval`: An `R`-algebra homomorphism from `MvPowerSeries σ R` to `R⟦Γ⟧`
  (for finite σ) taking each `X i` to a positive order Hahn Series.

-/

@[expose] public section

open Finset Function

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

namespace HahnSeries

namespace SummableFamily

section PowerSeriesFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

variable [CommRing V] [Algebra R V]

/-- A summable family given by scalar multiples of powers of a positive order Hahn series.

The scalar multiples are given by the coefficients of a power series. -/
/-
**HahnSeries.SummableFamily.powerSeriesFamily** 是 Mathlib 中的一个缩写定义，位于命名空间 `HahnS
eries.SummableFamily`。
形式化陈述：powerSeriesFamily (x : V⟦Γ⟧) (f : PowerSeries R) : SummableFamily Γ V Nat
参数：x : V⟦Γ⟧；f : PowerSeries R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A summable family given by scalar multiples of powers of a positive order Hahn s
eries.

The scalar multiples are given by the coefficients of a power series.
-/
abbrev powerSeriesFamily (x : V⟦Γ⟧) (f : PowerSeries R) : SummableFamily Γ V ℕ :=
  smulFamily (fun n => f.coeff n) (powers x)
/-
**HahnSeries.SummableFamily.powerSeriesFamily_of_not_orderTop_pos** 是 Mathlib 中的
一个定理，位于命名空间 `HahnSeries.SummableFamily`。
形式化陈述：powerSeriesFamily_of_not_orderTop_pos {x : V⟦Γ⟧} (hx : ¬ 0 < x.orderTop) (
f : PowerSeries R) : powerSeriesFamily x f = powerSeriesFamily 0 f
参数：hx : ¬ 0 < x.orderTop；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.ext`：ext {s t : SummableFamily Γ R α} (h : for
all a : α, s a = t a) : s = t
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `HahnSeries.SummableFamily.powers_zero`：powers_zero : powers (0 : R⟦Γ⟧) =
 .single 0 1
· 使用定理 `HahnSeries.SummableFamily.single_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {ι : Type u_7}   [inst_2 : De
cidableEq ι] (i : ι) (x : Ha…
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem powerSeriesFamily_of_not_orderTop_pos {x : V⟦Γ⟧} (hx : ¬ 0 < x.orderTop)
    (f : PowerSeries R) :
    powerSeriesFamily x f = powerSeriesFamily 0 f := by
  ext n g
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
/-
**HahnSeries.SummableFamily.powerSeriesFamily_of_orderTop_pos** 是 Mathlib 中的一个定理
，位于命名空间 `HahnSeries.SummableFamily`。
形式化陈述：powerSeriesFamily_of_orderTop_pos {x : V⟦Γ⟧} (hx : 0 < x.orderTop) (f : Po
werSeries R) (n : Nat) : powerSeriesFamily x f n = f.coeff n • x ^ n
参数：hx : 0 < x.orderTop；f : PowerSeries R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powerSeriesFamily_of_orderTop_pos {x : V⟦Γ⟧} (hx : 0 < x.orderTop)
    (f : PowerSeries R) (n : ℕ) :
    powerSeriesFamily x f n = f.coeff n • x ^ n := by
  simp [hx]
/-
**HahnSeries.SummableFamily.powerSeriesFamily_hsum_zero** 是 Mathlib 中的一个定理，位于命名空
间 `HahnSeries.SummableFamily`。
形式化陈述：powerSeriesFamily_hsum_zero (f : PowerSeries R) : (powerSeriesFamily 0 f).
hsum = f.constantCoeff • (1 : V⟦Γ⟧)
参数：f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `HahnSeries.SummableFamily.powers_zero`：powers_zero : powers (0 : R⟦Γ⟧) =
 .single 0 1
· 使用定理 `HahnSeries.SummableFamily.single_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {ι : Type u_7}   [inst_2 : De
cidableEq ι] (i : ι) (x : Ha…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum`：coeff_hsum {s : SummableFamily Γ R
 α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
· 使用定理 `finsum_eq_zero_of_forall_eq_zero`：∀ {α : Type u_1} {M : Type u_5} [inst 
: AddCommMonoid M] {f : α → M}, (∀ (x : α), f x = 0) → ∑ᶠ (i : α), f i = 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem powerSeriesFamily_hsum_zero (f : PowerSeries R) :
    (powerSeriesFamily 0 f).hsum = f.constantCoeff • (1 : V⟦Γ⟧) := by
  ext g
  by_cases hg : g = 0
  · simp only [hg, coeff_hsum]
    rw [finsum_eq_single _ 0 (fun n hn ↦ by simp [hn])]
    simp
  · rw [coeff_hsum, finsum_eq_zero_of_forall_eq_zero
      fun n ↦ (by by_cases hn : n = 0 <;> simp [hg, hn])]
    simp [hg]
/-
**HahnSeries.SummableFamily.powerSeriesFamily_add** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nSeries.SummableFamily`。
形式化陈述：powerSeriesFamily_add {x : V⟦Γ⟧} (f g : PowerSeries R) : powerSeriesFamily
 x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g
参数：f g : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.ext`：ext {s t : SummableFamily Γ R α} (h : for
all a : α, s a = t a) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem powerSeriesFamily_add {x : V⟦Γ⟧} (f g : PowerSeries R) :
    powerSeriesFamily x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g := by
  ext1 n
  by_cases hx : 0 < x.orderTop <;> · simp [hx, add_smul]
/-
**HahnSeries.SummableFamily.powerSeriesFamily_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ha
hnSeries.SummableFamily`。
形式化陈述：powerSeriesFamily_smul {x : V⟦Γ⟧} (f : PowerSeries R) (r : R) : powerSerie
sFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f
参数：f : PowerSeries R；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.ext`：ext {s t : SummableFamily Γ R α} (h : for
all a : α, s a = t a) : s = t
· 使用定理 `instIsOrderedCancelVAddOfIsOrderedAddCancelMonoid`：∀ {G : Type u_1} [ins
t : AddCommMonoid G] [inst_1 : Preorder G] [IsOrderedCancelAddMonoid G], IsOrder
edCancelVAdd G G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用引理 `ite_pow`：ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) : (if p then
 a else b) ^ c = if p then a ^ c else b ^ c
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `HahnModule.single_zero_smul_eq_smul`：single_zero_smul_eq_smul (Γ) [AddCo
mmMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [MulZer
oClass R] [SMulWithZero R…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powerSeriesFamily_smul {x : V⟦Γ⟧} (f : PowerSeries R) (r : R) :
    powerSeriesFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f := by
  ext1 n
  simp [mul_smul]

set_option backward.isDefEq.respectTransparency false in
/-
**HahnSeries.SummableFamily.support_powerSeriesFamily_subset** 是 Mathlib 中的一个定理，
位于命名空间 `HahnSeries.SummableFamily`。
形式化陈述：support_powerSeriesFamily_subset {x : V⟦Γ⟧} (a b : PowerSeries R) (g : Γ) 
: ((powerSeriesFamily x (a * b)).coeff g).support subseteq (((powerSeriesFamily 
x a).mul (powerSeriesFamily x b)).coeff g).support.image fun i => i.1 + i.2
参数：a b : PowerSeries R；g : Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.SummableFamily.coeff_support`：∀ {Γ : Type u_1} {R : Type u_3}
 {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R]   (s : HahnSe
ries.SummableFamily Γ R α) (g…
· 使用定理 `Finset.exists_ne_zero_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} {s
 : Finset ι} [inst : AddCommMonoid M] {f : ι → M}, ∑ x ∈ s, f x ≠ 0 → ∃ a ∈ s, f
 a ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `HahnSeries.coeff_sum`：coeff_sum {s : Finset α} {x : α -> R⟦Γ⟧} (g : Γ) :
 (∑ i in s, x i).coeff g = ∑ i in s, (x i).coeff g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnSeries.SummableFamily.powers_of_orderTop_pos`：powers_of_orderTop_pos
 {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : Nat) : powers x n = x ^ n
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `HahnSeries.SummableFamily.mul_toFun`：∀ {Γ : Type u_1} {R : Type u_3} {α 
: Type u_5} {β : Type u_6} [inst : AddCommMonoid Γ] [inst_1 : PartialOrder Γ]   
[inst_2 : IsOrderedCancel…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 51 条，此处仅展示前 30 条）
-/
theorem support_powerSeriesFamily_subset {x : V⟦Γ⟧} (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily x (a * b)).coeff g).support ⊆
    (((powerSeriesFamily x a).mul (powerSeriesFamily x b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  by_cases h : 0 < x.orderTop
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    have he : ∃ c ∈ antidiagonal n, (PowerSeries.coeff c.1) a • (PowerSeries.coeff c.2) b •
        ((powers x) n).coeff g ≠ 0 := by
      refine exists_ne_zero_of_sum_ne_zero ?_
      simpa [PowerSeries.coeff_mul, sum_smul, mul_smul, h] using hn
    simp only [powers_of_orderTop_pos h, HasAntidiagonal.mem_antidiagonal] at he
    obtain ⟨c, hcn, hc⟩ := he
    simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    use c
    simp only [mul_toFun, smulFamily_toFun, Function.mem_support, hcn,
      and_true]
    rw [powers_of_orderTop_pos h c.1, powers_of_orderTop_pos h c.2, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, ← pow_add, hcn]
    simp [hc]
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    by_cases hz : n = 0
    · have : g = 0 ∧ (a.constantCoeff * b.constantCoeff) • (1 : V) ≠ 0 := by
        simpa [hz, h] using hn
      simp only [coe_image, Set.mem_image]
      use (0, 0)
      simp [this.2, this.1, h, hz, smul_smul, mul_comm]
    · simp [h, hz] at hn
/-
**HahnSeries.SummableFamily.hsum_powerSeriesFamily_mul** 是 Mathlib 中的一个定理，位于命名空间
 `HahnSeries.SummableFamily`。
形式化陈述：hsum_powerSeriesFamily_mul {x : V⟦Γ⟧} (a b : PowerSeries R) : (powerSeries
Family x (a * b)).hsum = ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).h
sum
参数：a b : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum_eq_sum`：coeff_hsum_eq_sum {s : Summ
ableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ i in (s.coeff g).support, (s i).c
oeff g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `HahnSeries.SummableFamily.powers_of_orderTop_pos`：powers_of_orderTop_pos
 {x : R⟦Γ⟧} (hx : 0 < x.orderTop) (n : Nat) : powers x n = x ^ n
· 使用定理 `HahnSeries.SummableFamily.mul_toFun`：∀ {Γ : Type u_1} {R : Type u_3} {α 
: Type u_5} {β : Type u_6} [inst : AddCommMonoid Γ] [inst_1 : PartialOrder Γ]   
[inst_2 : IsOrderedCancel…
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `HahnSeries.SummableFamily.support_powerSeriesFamily_subset`：support_powe
rSeriesFamily_subset {x : V⟦Γ⟧} (a b : PowerSeries R) (g : Γ) : ((powerSeriesFam
ily x (a * b)).coeff g).support subseteq (((powe…
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `HahnSeries.SummableFamily.finite_co_support`：finite_co_support (s : Summ
ableFamily Γ R α) (g : Γ) : (fun a => (s a).coeff g).HasFiniteSupport
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HahnSeries.coeff_sum`：coeff_sum {s : Finset α} {x : α -> R⟦Γ⟧} (g : Γ) :
 (∑ i in s, x i).coeff g = ∑ i in s, (x i).coeff g
· 使用定理 `HahnSeries.SummableFamily.coeff_support`：∀ {Γ : Type u_1} {R : Type u_3}
 {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R]   (s : HahnSe
ries.SummableFamily Γ R α) (g…
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_of_injOn`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [ins
t : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e 
: ι → κ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
（共 63 条，此处仅展示前 30 条）
-/
theorem hsum_powerSeriesFamily_mul {x : V⟦Γ⟧} (a b : PowerSeries R) :
    (powerSeriesFamily x (a * b)).hsum =
    ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).hsum := by
  by_cases h : 0 < x.orderTop;
  · ext g
    simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [sum_subset (support_powerSeriesFamily_subset a b g)
      (fun i hi his ↦ by simpa [h, PowerSeries.coeff_mul, sum_smul] using his)]
    simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
    rw [sum_sigma']
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
    · intro ij hij
      simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
        HasAntidiagonal.mem_antidiagonal, and_true]
      use ij.1, ij.2
      simp_all
    · intro i hi his
      have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff k) b •
          (PowerSeries.coeff j a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        simp only [powers_of_orderTop_pos h, Set.Finite.coe_toFinset, Set.mem_image,
          Function.mem_support, ne_eq, Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, HasAntidiagonal.mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff i.snd.1) a), ← hi.2, mul_smul, pow_add]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · simp only [h, not_false_eq_true, powerSeriesFamily_of_not_orderTop_pos,
      powerSeriesFamily_hsum_zero, map_mul, hsum_mul]
    rw [smul_mul_smul_comm, mul_one]

end PowerSeriesFamily

end SummableFamily

end HahnSeries

namespace PowerSeries

open HahnSeries SummableFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] (x : R⟦Γ⟧)

/-- The `R`-algebra homomorphism from `R⟦X⟧` to `R⟦Γ⟧` given by sending the power series
variable `X` to a positive order element `x` and extending to infinite sums. -/
@[simps]
/-
**PowerSeries.heval** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：heval : PowerSeries R ->ₐ[R] R⟦Γ⟧ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-algebra homomorphism from `R⟦X⟧` to `R⟦Γ⟧` given by sending the power se
ries
variable `X` to a positive order element `x` and extending to infinite sums.
-/
def heval : PowerSeries R →ₐ[R] R⟦Γ⟧ where
  toFun f := (powerSeriesFamily x f).hsum
  map_one' := by
    simp only [hsum, smulFamily_toFun, coeff_one, powers_toFun, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single _ (0 : ℕ) (fun n hn => by simp [hn])]
    simp
  map_mul' a b := by
    simp only [← hsum_mul, hsum_powerSeriesFamily_mul]
  map_zero' := by
    simp only [hsum, smulFamily_toFun, map_zero, zero_smul,
      coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    simp only [powerSeriesFamily_add, hsum_add]
  commutes' r := by
    simp only [algebraMap_eq]
    ext g
    simp only [coeff_hsum, smulFamily_toFun, coeff_C, powers_toFun, ite_smul, zero_smul]
    rw [finsum_eq_single _ 0 fun n hn => by simp [hn]]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one]
/-
**PowerSeries.heval_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：heval_mul {a b : PowerSeries R} : heval x (a * b) = heval x a * heval x b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem heval_mul {a b : PowerSeries R} : heval x (a * b) = heval x a * heval x b :=
  map_mul (heval x) a b
/-
**PowerSeries.heval_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：heval_C (r : R) : heval x (C r) = r • 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.heval_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddComm
Monoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst
_3 : CommRing…
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PowerSeries.coeff_C_of_ne_zero`：coeff_C_of_ne_zero {a : R} {n : Nat} (h 
: n != 0) : coeff n (C a) = 0
· 使用引理 `ite_pow`：ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) : (if p then
 a else b) ^ c = if p then a ^ c else b ^ c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.coeff_zero_C`：coeff_zero_C (a : R) : coeff 0 (C a) = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem heval_C (r : R) : heval x (C r) = r • 1 := by
  ext g
  simp only [heval_apply, coeff_hsum, smulFamily_toFun, powers_toFun, HahnSeries.coeff_smul,
    HahnSeries.coeff_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ 0 (fun n hn ↦ by simp [coeff_C_of_ne_zero hn])]
  by_cases hg : g = 0 <;> simp
/-
**PowerSeries.heval_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：heval_X (hx : 0 < x.orderTop) : heval x X = x
参数：hx : 0 < x.orderTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.X_eq`：X_eq : (X : R⟦X⟧) = monomial 1 1
· 使用定理 `PowerSeries.monomial_eq_mk`：monomial_eq_mk (n : Nat) (a : R) : monomial 
n a = mk fun m => if m = n then a else 0
· 使用定理 `PowerSeries.heval_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddComm
Monoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst
_3 : CommRing…
· 使用定理 `HahnSeries.SummableFamily.powerSeriesFamily.eq_1`：∀ {Γ : Type u_1} {R : 
Type u_3} {V : Type u_4} [inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ]   [in
st_2 : IsOrderedCancelAddMonoid Γ] [in…
· 使用定理 `HahnSeries.SummableFamily.smulFamily.eq_1`：∀ {Γ : Type u_1} {R : Type u_
3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid
 R]   [inst_2 : AddCommMonoid V…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `HahnSeries.SummableFamily.mk.congr_simp`：∀ {Γ : Type u_8} {R : Type u_9}
 [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R] {α : Type u_7}   (toFun toFu
n_1 : α → HahnSeries Γ R) (e_…
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum`：coeff_hsum {s : SummableFamily Γ R
 α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem heval_X (hx : 0 < x.orderTop) : heval x X = x := by
  rw [X_eq, monomial_eq_mk, heval_apply, powerSeriesFamily, smulFamily]
  simp only [coeff_mk, powers_toFun, hx, ↓reduceIte, ite_smul, one_smul, zero_smul]
  ext g
  rw [coeff_hsum, finsum_eq_single _ 1 (fun n hn ↦ by simp [hn])]
  simp
/-
**PowerSeries.heval_unit** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：heval_unit (u : (PowerSeries R)ˣ) : IsUnit (heval x u)
参数：u : (PowerSeries R)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.heval_mul`：heval_mul {a b : PowerSeries R} : heval x (a * b)
 = heval x a * heval x b
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem heval_unit (u : (PowerSeries R)ˣ) : IsUnit (heval x u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval x u.inv
  rw [← heval_mul, Units.val_inv, map_one]
/-
**PowerSeries.coeff_heval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_heval (f : PowerSeries R) (g : Γ) : (heval x f).coeff g = ∑ᶠ n, ((po
werSeriesFamily x f).coeff g) n
参数：f : PowerSeries R；g : Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.heval_apply`：∀ {Γ : Type u_1} {R : Type u_3} [inst : AddComm
Monoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMonoid Γ]   [inst
_3 : CommRing…
· 使用定理 `HahnSeries.SummableFamily.coeff_hsum`：coeff_hsum {s : SummableFamily Γ R
 α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g
-/
theorem coeff_heval (f : PowerSeries R) (g : Γ) :
    (heval x f).coeff g = ∑ᶠ n, ((powerSeriesFamily x f).coeff g) n := by
  rw [heval_apply, coeff_hsum]
  exact rfl
/-
**PowerSeries.coeff_heval_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_heval_zero (f : PowerSeries R) : (heval x f).coeff 0 = PowerSeries.c
onstantCoeff f
参数：f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_heval`：coeff_heval (f : PowerSeries R) (g : Γ) : (heva
l x f).coeff g = ∑ᶠ n, ((powerSeriesFamily x f).coeff g) n
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.SummableFamily.coeff_apply`：∀ {Γ : Type u_1} {R : Type u_3} {
α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoid R]   (s : HahnSeri
es.SummableFamily Γ R α) (g…
· 使用定理 `HahnSeries.SummableFamily.smulFamily_toFun`：∀ {Γ : Type u_1} {R : Type u
_3} {V : Type u_4} {α : Type u_5} [inst : PartialOrder Γ] [inst_1 : AddCommMonoi
d R]   [inst_2 : AddCommMonoid V…
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nsmul_pos_iff`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : LinearOrd
er M] [AddLeftMono M] {x : M} {n : ℕ},   n ≠ 0 → (0 < n • x ↔ 0 < x)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HahnSeries.SummableFamily.powers_toFun`：∀ {Γ : Type u_1} {R : Type u_3} 
[inst : AddCommMonoid Γ] [inst_1 : LinearOrder Γ] [inst_2 : IsOrderedCancelAddMo
noid Γ]   [inst_3 : CommRing…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantCoe
ff_apply (φ : R⟦X⟧) : coeff 0 φ = constantCoeff φ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `HahnSeries.coeff_one`：coeff_one [Zero R] [One R] {a : Γ} : (1 : R⟦Γ⟧).co
eff a = if a = 0 then 1 else 0
（共 32 条，此处仅展示前 30 条）
-/
theorem coeff_heval_zero (f : PowerSeries R) :
    (heval x f).coeff 0 = PowerSeries.constantCoeff f := by
  rw [coeff_heval, finsum_eq_single (fun n => ((powerSeriesFamily x f).coeff 0) n) 0,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp
  · intro n hn
    simp only [coeff_apply, smulFamily_toFun, HahnSeries.coeff_smul, smul_eq_mul]
    refine mul_eq_zero_of_right (coeff n f) (coeff_eq_zero_of_lt_orderTop ?_)
    by_cases h : 0 < x.orderTop
    · refine (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr h) ?_)
      simp [h, orderTop_nsmul_le_orderTop_pow]
    · simp [h, hn]

end PowerSeries

