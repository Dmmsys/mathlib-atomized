/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Bichang Lei, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Extension of Valuations

In this file, we define the typeclass for valuation extensions and prove basic facts about the
extension of valuations. Let `A` be an `R` algebra, equipped with valuations `vA` and `vR`
respectively. Here, the extension of a valuation means that the pullback of valuation `vA` to `R`
is equivalent to the valuation `vR` on `R`. We only require equivalence, not equality, of
valuations here.

Note that we do not require the ring map from `R` to `A` to be injective. This holds automatically
when `R` is a division ring and `A` is nontrivial.

A motivation for choosing the more flexible `Valuation.Equiv` rather than strict equality here is
to allow for possible normalization. As an example, consider a finite extension `K` of `ℚ_[p]`,
which is a discretely valued field. We may choose the valuation on `K` to be either:

1. the valuation where the uniformizer is mapped to one (more precisely, `-1` in `ℤᵐ⁰`) or

2. the valuation where `p` is mapped to one.

For the algebraic closure of `ℚ_[p]`, if we choose the valuation of `p` to be one, then the
restriction of this valuation to `K` equals the second valuation, but is only equivalent to the
first valuation. The flexibility of equivalence here allows us to develop theory for both cases
without first determining the normalizations once and for all.

## Main Definition

* `Valuation.HasExtension vR vA` : The valuation `vA` on `A` is an extension of the valuation
  `vR` on `R`.

## References

* [Bourbaki, Nicolas. *Commutative algebra*] Chapter VI §3, Valuations.
* <https://en.wikipedia.org/wiki/Valuation_(algebra)#Extension_of_valuations>

## Tags
Valuation, Extension of Valuations

-/

@[expose] public section

open Module

namespace Valuation

variable {R A ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓA] [Algebra R A]
    (vR : Valuation R ΓR) (vA : Valuation A ΓA)

/--
The class `Valuation.HasExtension vR vA` states that the valuation `vA` on `A` is an extension of
the valuation `vR` on `R`. More precisely, `vR` is equivalent to the comap of the valuation `vA`.
-/
/-
**Valuation.HasExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     {ΓR : Type u_3} →       {ΓA : Type
 u_4} →         [inst : CommRing R] →           [inst_1 : Ring A] →             
[inst_2 : LinearOrderedCommMonoidWithZero ΓR] →               [inst_3 : LinearOr
deredCommMonoidWithZero ΓA] → [Algebra R A] → Valuation R ΓR → Valuation A ΓA → 
Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class `Valuation.HasExtension vR vA` states that the valuation `vA` on `A` i
s an extension of
the valuation `vR` on `R`. More precisely, `vR` is equivalent to the comap of th
e valuation `vA`.
-/
class HasExtension : Prop where
  /-- The valuation `vR` on `R` is equivalent to the comap of the valuation `vA` on `A` -/
  val_isEquiv_comap : vR.IsEquiv <| vA.comap (algebraMap R A)

namespace HasExtension

section algebraMap

variable [vR.HasExtension vA]

-- @[simp] does not work because `vR` cannot be inferred from `R`.
/-
**Valuation.HasExtension.val_map_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Has
Extension`。
形式化陈述：val_map_le_iff (x y : R) : vA (algebraMap R A x) <= vA (algebraMap R A y) 
↔ vR x <= vR y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
· 使用定理 `Valuation.HasExtension.val_isEquiv_comap`：∀ {R : Type u_1} {A : Type u_2
} {ΓR : Type u_3} {ΓA : Type u_4} {inst : CommRing R} {inst_1 : Ring A}   {inst_
2 : LinearOrderedCommMonoidWit…
-/
theorem val_map_le_iff (x y : R) : vA (algebraMap R A x) ≤ vA (algebraMap R A y) ↔ vR x ≤ vR y :=
  val_isEquiv_comap.symm x y
/-
**Valuation.HasExtension.val_map_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Has
Extension`。
形式化陈述：val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔
 vR x < vR y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Valuation.HasExtension.val_map_le_iff`：val_map_le_iff (x y : R) : vA (al
gebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y
-/
theorem val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y := by
  simpa only [not_le] using ((val_map_le_iff vR vA _ _).not)
/-
**Valuation.HasExtension.val_map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Has
Extension`。
形式化陈述：val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔
 vR x = vR y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Valuation.IsEquiv.eq_iff`：eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = 
v₁ s ↔ v₂ r = v₂ s
· 使用定理 `Valuation.HasExtension.val_isEquiv_comap`：∀ {R : Type u_1} {A : Type u_2
} {ΓR : Type u_3} {ΓA : Type u_4} {inst : CommRing R} {inst_1 : Ring A}   {inst_
2 : LinearOrderedCommMonoidWit…
-/
theorem val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  (IsEquiv.eq_iff val_isEquiv_comap).symm
/-
**Valuation.HasExtension.val_map_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
.HasExtension`。
形式化陈述：val_map_le_one_iff (x : R) : vA (algebraMap R A x) <= 1 ↔ vR x <= 1
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.HasExtension.val_map_le_iff`：val_map_le_iff (x y : R) : vA (al
gebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y
-/
theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1 := by
  simpa only [map_one] using val_map_le_iff vR vA x 1
/-
**Valuation.HasExtension.val_map_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
.HasExtension`。
形式化陈述：val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Valuation.HasExtension.val_map_le_iff`：val_map_le_iff (x y : R) : vA (al
gebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y
-/
theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 := by
  simpa only [map_one, not_le] using (val_map_le_iff vR vA 1 x).not
/-
**Valuation.HasExtension.val_map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation
.HasExtension`。
形式化陈述：val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Valuation.HasExtension.val_map_le_iff`：val_map_le_iff (x y : R) : vA (al
gebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y
-/
theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 := by
  simpa only [le_antisymm_iff, map_one] using
    and_congr (val_map_le_iff vR vA x 1) (val_map_le_iff vR vA 1 x)

end algebraMap

/-
**Valuation.HasExtension.id** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.HasExtension`。
形式化陈述：id : vR.HasExtension vR where val_isEquiv_comap
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.comap_id`：comap_id : v.comap (RingHom.id R) = v
-/
instance id : vR.HasExtension vR where
  val_isEquiv_comap := by
    simp only [Algebra.algebraMap_self, comap_id, IsEquiv.refl]

section integer

variable {K : Type*} [Field K] [Algebra K A] {ΓR ΓA ΓK : Type*}
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓA] {vR : Valuation R ΓR} {vK : Valuation K ΓK}
    {vA : Valuation A ΓA} [vR.HasExtension vA]

/--
When `K` is a field, if the preimage of the valuation integers of `A` equals to the valuation
integers of `K`, then the valuation on `A` is an extension of the valuation on `K`.
-/
/-
**Valuation.HasExtension.ofComapInteger** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Has
Extension`。
形式化陈述：ofComapInteger (h : vA.integer.comap (algebraMap K A) = vK.integer) : vK.H
asExtension vA where val_isEquiv_comap
参数：h : vA.integer.comap (algebraMap K A) = vK.integer。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.isEquiv_iff_val_le_one`：isEquiv_iff_val_le_one : v.IsEquiv v' 
↔ forall {x}, v x <= 1 ↔ v' x <= 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When `K` is a field, if the preimage of the valuation integers of `A` equals to 
the valuation
integers of `K`, then the valuation on `A` is an extension of the valuation on `
K`.
-/
theorem ofComapInteger (h : vA.integer.comap (algebraMap K A) = vK.integer) :
    vK.HasExtension vA where
  val_isEquiv_comap := by
    rw [isEquiv_iff_val_le_one]
    intro x
    simp_rw [← Valuation.mem_integer_iff, ← h, Subring.mem_comap, mem_integer_iff, comap_apply]
/-
**Valuation.HasExtension.instAlgebraInteger** 是 Mathlib 中的一个实例，位于命名空间 `Valuation
.HasExtension`。
形式化陈述：instAlgebraInteger : Algebra vR.integer vA.integer where smul r a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebraInteger : Algebra vR.integer vA.integer where
  smul r a := ⟨r • a,
    Algebra.smul_def r (a : A) ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr r.2) a.2⟩
  algebraMap := (algebraMap R A).restrict vR.integer vA.integer
    (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)

@[simp, norm_cast]
/-
**Valuation.HasExtension.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.HasExtens
ion`。
形式化陈述：val_smul (r : vR.integer) (a : vA.integer) : ↑(r • a : vA.integer) = (r : 
R) • (a : A)
参数：r : vR.integer；a : vA.integer。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem val_smul (r : vR.integer) (a : vA.integer) : ↑(r • a : vA.integer) = (r : R) • (a : A) := by
  rfl

@[simp]
/-
**Valuation.HasExtension.mk_smul_mk** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.HasExte
nsion`。
形式化陈述：mk_smul_mk (r : R) (hr) (a : A) (ha) : (⟨r, hr⟩ : vR.integer) • (⟨a, ha⟩ :
 vA.integer) = ⟨r • a, Algebra.smul_def r a ▸ mul_mem ((val_map_le_one_iff vR vA
 _).mpr hr) ha⟩
参数：r : R；hr；a : A；ha。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
lemma mk_smul_mk (r : R) (hr) (a : A) (ha) :
    (⟨r, hr⟩ : vR.integer) • (⟨a, ha⟩ : vA.integer) =
      ⟨r • a, Algebra.smul_def r a ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr hr) ha⟩ := rfl

@[simp, norm_cast]
/-
**Valuation.HasExtension.val_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Has
Extension`。
形式化陈述：val_algebraMap (r : vR.integer) : ((algebraMap vR.integer vA.integer) r : 
A) = (algebraMap R A) (r : R)
参数：r : vR.integer。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
-/
theorem val_algebraMap (r : vR.integer) :
    ((algebraMap vR.integer vA.integer) r : A) = (algebraMap R A) (r : R) := by
  rfl
/-
**Valuation.HasExtension.instIsScalarTowerInteger** 是 Mathlib 中的一个实例，位于命名空间 `Val
uation.HasExtension`。
形式化陈述：instIsScalarTowerInteger : IsScalarTower vR.integer vA.integer A where smu
l_assoc x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
instance instIsScalarTowerInteger : IsScalarTower vR.integer vA.integer A where
  smul_assoc x y z := by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _
/-
**Valuation.HasExtension.instIsTorsionFreeInteger** 是 Mathlib 中的一个实例，位于命名空间 `Val
uation.HasExtension`。
形式化陈述：instIsTorsionFreeInteger [IsDomain R] [IsTorsionFree R A] : IsTorsionFree 
vR.integer vA.integer
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.IsTorsionFree.of_smul_eq_zero`：Module.IsTorsionFree.of_smul_eq_ze
ro [Nontrivial R] (h : forall (r : R) (m : M), r • m = 0 -> r = 0 ∨ m = 0) : IsT
orsionFree R M where isSMu…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.HasExtension.val_map_le_one_iff`：val_map_le_one_iff (x : R) : 
vA (algebraMap R A x) <= 1 ↔ vR x <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance instIsTorsionFreeInteger [IsDomain R] [IsTorsionFree R A] :
    IsTorsionFree vR.integer vA.integer := .of_smul_eq_zero <| by simp
/-
**Valuation.HasExtension.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Valuati
on.HasExtension`。
形式化陈述：algebraMap_injective [vK.HasExtension vA] [Nontrivial A] : Function.Inject
ive (algebraMap vK.integer vA.integer)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
-/
theorem algebraMap_injective [vK.HasExtension vA] [Nontrivial A] :
    Function.Injective (algebraMap vK.integer vA.integer) :=
  FaithfulSMul.algebraMap_injective _ _

@[instance]
/-
**Valuation.HasExtension.instIsLocalHomValuationInteger** 是 Mathlib 中的一个定理，位于命名空
间 `Valuation.HasExtension`。
形式化陈述：instIsLocalHomValuationInteger {S ΓS : Type*} [CommRing S] [LinearOrderedC
ommGroupWithZero ΓS] [Algebra R S] [IsLocalHom (algebraMap R S)] {vS : Valuation
 S ΓS} [vR.HasExtension vS] : IsLocalHom (algebraMap vR.integer vS.integer) wher
e map_nonunit r hr
参数：algebraMap R S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Valuation.Integers.isUnit_of_one`：isUnit_of_one (hv : Integers v O) {x :
 O} (hx : IsUnit (algebraMap O R x)) (hvx : v (algebraMap O R x) = 1) : IsUnit x
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `Valuation.HasExtension.val_map_eq_one_iff`：val_map_eq_one_iff (x : R) : 
vA (algebraMap R A x) = 1 ↔ vR x = 1
· 使用定理 `Valuation.Integers.one_of_isUnit`：one_of_isUnit (hv : Integers v O) {x :
 O} (hx : IsUnit x) : v (algebraMap O R x) = 1
-/
theorem instIsLocalHomValuationInteger {S ΓS : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero ΓS]
    [Algebra R S] [IsLocalHom (algebraMap R S)] {vS : Valuation S ΓS}
    [vR.HasExtension vS] : IsLocalHom (algebraMap vR.integer vS.integer) where
  map_nonunit r hr := by
    apply (Valuation.integer.integers (v := vR)).isUnit_of_one
    · exact (isUnit_map_iff (algebraMap R S) _).mp (hr.map (algebraMap _ S))
    · apply (Valuation.integer.integers (v := vS)).one_of_isUnit at hr
      exact (val_map_eq_one_iff vR vS _).mp hr

end integer

section AlgebraInstances

open IsLocalRing Valuation ValuationSubring

variable {K L Γ₀ Γ₁ : outParam Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁] (vK : Valuation K Γ₀)
  (vL : Valuation L Γ₁) [vK.HasExtension vL]

local notation "K₀" => Valuation.valuationSubring vK
local notation "L₀" => Valuation.valuationSubring vL

/-
**Valuation.HasExtension.algebraMap_mem_valuationSubring** 是 Mathlib 中的一个引理，位于命名
空间 `Valuation.HasExtension`。
形式化陈述：algebraMap_mem_valuationSubring (x : K₀) : algebraMap K L x in L₀
参数：x : K₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.mem_valuationSubring_iff`：mem_valuationSubring_iff (x : K) : x
 in v.valuationSubring ↔ v x <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.HasExtension.val_map_le_iff`：val_map_le_iff (x y : R) : vA (al
gebraMap R A x) <= vA (algebraMap R A y) ↔ vR x <= vR y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma algebraMap_mem_valuationSubring (x : K₀) : algebraMap K L x ∈ L₀ := by
  rw [mem_valuationSubring_iff, ← _root_.map_one vL, ← _root_.map_one (algebraMap K L),
    val_map_le_iff (vR := vK), _root_.map_one]
  exact x.2
/-
**Valuation.HasExtension.instAlgebra_valuationSubring** 是 Mathlib 中的一个实例，位于命名空间 
`Valuation.HasExtension`。
形式化陈述：instAlgebra_valuationSubring : Algebra K₀ L₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra_valuationSubring : Algebra K₀ L₀ :=
  inferInstanceAs (Algebra vK.integer vL.integer)

@[simp]
/-
**Valuation.HasExtension.coe_algebraMap_valuationSubring_eq** 是 Mathlib 中的一个引理，位
于命名空间 `Valuation.HasExtension`。
形式化陈述：coe_algebraMap_valuationSubring_eq (x : K₀) : (algebraMap K₀ L₀ x : L) = a
lgebraMap K L (x : K)
参数：x : K₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
-/
lemma coe_algebraMap_valuationSubring_eq (x : K₀) :
    (algebraMap K₀ L₀ x : L) = algebraMap K L (x : K) := rfl
/-
**Valuation.HasExtension.instIsScalarTower_valuationSubring** 是 Mathlib 中的一个实例，位
于命名空间 `Valuation.HasExtension`。
形式化陈述：instIsScalarTower_valuationSubring : IsScalarTower K₀ K L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower_valuationSubring : IsScalarTower K₀ K L :=
  inferInstanceAs (IsScalarTower vK.integer K L)
/-
**Valuation.HasExtension.instIsScalarTower_valuationSubring'** 是 Mathlib 中的一个实例，
位于命名空间 `Valuation.HasExtension`。
形式化陈述：instIsScalarTower_valuationSubring' : IsScalarTower K₀ L₀ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsScalarTower_valuationSubring' : IsScalarTower K₀ L₀ L :=
  instIsScalarTowerInteger
/-
**Valuation.HasExtension.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.HasExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalHom (algebraMap K₀ L₀) := instIsLocalHomValuationInteger
/-
**Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff** 是 Mathlib 中的一个引理，位于命名
空间 `Valuation.HasExtension`。
形式化陈述：algebraMap_mem_maximalIdeal_iff {x : K₀} : algebraMap K₀ L₀ x in (maximalI
deal L₀) ↔ x in maximalIdeal K₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.HasExtension.instIsLocalHomSubtypeMemValuationSubringValuation
SubringRingHomAlgebraMap`：∀ {K : outParam (Type u_5)} {L : outParam (Type u_6)} 
{Γ₀ : outParam (Type u_7)} {Γ₁ : outParam (Type u_8)}   [inst : Field K] [inst_1
 : Fie…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma algebraMap_mem_maximalIdeal_iff {x : K₀} :
    algebraMap K₀ L₀ x ∈ (maximalIdeal L₀) ↔ x ∈ maximalIdeal K₀ := by
  simp [mem_maximalIdeal, map_mem_nonunits_iff, _root_.mem_nonunits_iff]
/-
**Valuation.HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal** 是 Mathl
ib 中的一个引理，位于命名空间 `Valuation.HasExtension`。
形式化陈述：maximalIdeal_comap_algebraMap_eq_maximalIdeal : (maximalIdeal L₀).comap (a
lgebraMap K₀ L₀) = maximalIdeal K₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用引理 `Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff`：algebraMap_mem_m
aximalIdeal_iff {x : K₀} : algebraMap K₀ L₀ x in (maximalIdeal L₀) ↔ x in maxima
lIdeal K₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma maximalIdeal_comap_algebraMap_eq_maximalIdeal :
    (maximalIdeal L₀).comap (algebraMap K₀ L₀) = maximalIdeal K₀ :=
  Ideal.ext fun _ ↦ by rw [Ideal.mem_comap, algebraMap_mem_maximalIdeal_iff]
/-
**Valuation.HasExtension.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation.HasExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ideal.LiesOver (maximalIdeal L₀) (maximalIdeal K₀) :=
  ⟨(maximalIdeal_comap_algebraMap_eq_maximalIdeal _ _).symm⟩
/-
**Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap** 是 Mathlib 中的
一个引理，位于命名空间 `Valuation.HasExtension`。
形式化陈述：algebraMap_residue_eq_residue_algebraMap (x : K₀) : (algebraMap (ResidueFi
eld K₀) (ResidueField L₀)) (IsLocalRing.residue K₀ x) = IsLocalRing.residue L₀ (
algebraMap K₀ L₀ x)
参数：x : K₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.HasExtension.instIsLocalHomSubtypeMemValuationSubringValuation
SubringRingHomAlgebraMap`：∀ {K : outParam (Type u_5)} {L : outParam (Type u_6)} 
{Γ₀ : outParam (Type u_7)} {Γ₁ : outParam (Type u_8)}   [inst : Field K] [inst_1
 : Fie…
-/
lemma algebraMap_residue_eq_residue_algebraMap (x : K₀) :
    (algebraMap (ResidueField K₀) (ResidueField L₀)) (IsLocalRing.residue K₀ x) =
      IsLocalRing.residue L₀ (algebraMap K₀ L₀ x) :=
  rfl

end AlgebraInstances

end HasExtension

end Valuation

