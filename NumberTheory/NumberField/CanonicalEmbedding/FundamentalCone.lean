/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the mixed space `ℝ^r₁ × ℂ^r₂` via the `mixedEmbedding`. The fundamental cone is a cone in the
mixed space that is a fundamental domain for the action of `(𝓞 K)ˣ` modulo torsion.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on the mixed space defined, for
  `u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in the mixed space, i.e. a subset stable
  by multiplication by a nonzero real number, see `smul_mem_of_mem`, that is also a fundamental
  domain for the action of `(𝓞 K)ˣ` modulo torsion, see `exists_unit_smul_mem` and
  `torsion_unit_smul_mem_of_mem`.

* `NumberField.mixedEmbedding.fundamentalCone.idealSet`: for `J` an integral ideal, the intersection
  between the fundamental cone and the `idealLattice` defined by the image of `J`.

* `NumberField.mixedEmbedding.fundamentalCone.idealSetEquivNorm`: for `J` an integral ideal and `n`
  a natural integer, the equivalence between the elements of `idealSet K` of norm `n` and the
  product of the set of nonzero principal ideals of `K` divisible by `J` of norm `n` and the
  torsion of `K`.

## Tags

number field, canonical embedding, units, principal ideals
-/

@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on the mixed space `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by
multiplication component by component with `mixedEmbedding K u`. -/
@[simps]
/-
**NumberField.mixedEmbedding.unitSMul** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mix
edEmbedding`。
形式化陈述：unitSMul : SMul (𝓞 K)ˣ (mixedSpace K) where smul u x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of `(𝓞 K)ˣ` on the mixed space `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ
`, by
multiplication component by component with `mixedEmbedding K u`.
-/
instance unitSMul : SMul (𝓞 K)ˣ (mixedSpace K) where
  smul u x := mixedEmbedding K u * x
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (𝓞 K)ˣ (mixedSpace K) where
  one_smul := fun _ ↦ by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulZeroClass (𝓞 K)ˣ (mixedSpace K) where
  smul_zero := fun _ ↦ by simp_rw [unitSMul_smul, mul_zero]

variable {K}
/-
**NumberField.mixedEmbedding.unit_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：unit_smul_eq_zero (u : (𝓞 K)ˣ) (x : mixedSpace K) : u • x = 0 ↔ x = 0
参数：u : (𝓞 K)ˣ；x : mixedSpace K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.mixedEmbedding.exists_normAtPlace_ne_zero_iff`：exists_normAt
Place_ne_zero_iff {x : mixedSpace K} : (exists w, normAtPlace w x != 0) ↔ x != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.unitSMul_smul`：∀ (K : Type u_1) [inst : Field
 K] (u : (NumberField.RingOfIntegers K)ˣ) (x : NumberField.mixedEmbedding.mixedS
pace K),   u • x = (NumberFiel…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
· 使用定理 `NumberField.InfinitePlace.instMonoidWithZeroHomClassReal`：∀ {K : Type u_
1} [inst : Field K], MonoidWithZeroHomClass (NumberField.InfinitePlace K) K ℝ
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_2`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem unit_smul_eq_zero (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, smul_zero]⟩
  contrapose! h
  obtain ⟨w, h⟩ := exists_normAtPlace_ne_zero_iff.mpr h
  refine exists_normAtPlace_ne_zero_iff.mp ⟨w, ?_⟩
  rw [unitSMul_smul, map_mul]
  exact mul_ne_zero (by simp) h

variable [NumberField K]
/-
**NumberField.mixedEmbedding.unit_smul_eq_iff_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：unit_smul_eq_iff_mul_eq {x y : 𝓞 K} {u : (𝓞 K)ˣ} : u • mixedEmbedding K x 
= mixedEmbedding K y ↔ u * x = y
参数：𝓞 K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.unitSMul_smul`：∀ (K : Type u_1) [inst : Field
 K] (u : (NumberField.RingOfIntegers K)ˣ) (x : NumberField.mixedEmbedding.mixedS
pace K),   u • x = (NumberFiel…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NumberField.mixedEmbedding_injective`：∀ (K : Type u_1) [inst : Field K] 
[NumberField K], Function.Injective ⇑(NumberField.mixedEmbedding K)
· 使用引理 `NumberField.RingOfIntegers.coe_eq_algebraMap`：coe_eq_algebraMap (x : 𝓞 K
) : (x : K) = algebraMap _ _ x
· 使用定理 `NumberField.RingOfIntegers.ext_iff`：∀ {K : Type u_1} [inst : Field K] {x
 y : NumberField.RingOfIntegers K}, x = y ↔ ↑x = ↑y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem unit_smul_eq_iff_mul_eq {x y : 𝓞 K} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, ← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K
/-
**NumberField.mixedEmbedding.norm_unit_smul** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：norm_unit_smul (u : (𝓞 K)ˣ) (x : mixedSpace K) : mixedEmbedding.norm (u • 
x) = mixedEmbedding.norm x
参数：u : (𝓞 K)ˣ；x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.unitSMul_smul`：∀ (K : Type u_1) [inst : Field
 K] (u : (NumberField.RingOfIntegers K)ˣ) (x : NumberField.mixedEmbedding.mixedS
pace K),   u • x = (NumberFiel…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `NumberField.mixedEmbedding.norm_unit`：norm_unit (u : (𝓞 K)ˣ) : mixedEmbe
dding.norm (mixedEmbedding K u) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_unit_smul (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem Module

variable [NumberField K] {K}

/-- The map from the mixed space to `logSpace K` defined in such way that: 1) it factors the map
`logEmbedding`, see `logMap_eq_logEmbedding`; 2) it is constant on the sets
`{c • x | c ∈ ℝ, c ≠ 0}` if `norm x ≠ 0`, see `logMap_real_smul`. -/
/-
**NumberField.mixedEmbedding.logMap** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.mixed
Embedding`。
形式化陈述：logMap (x : mixedSpace K) : logSpace K
参数：x : mixedSpace K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K

--- 原说明 ---
The map from the mixed space to `logSpace K` defined in such way that: 1) it fac
tors the map
`logEmbedding`, see `logMap_eq_logEmbedding`; 2) it is constant on the sets
`{c • x | c ∈ ℝ, c ≠ 0}` if `norm x ≠ 0`, see `logMap_real_smul`.
-/
def logMap (x : mixedSpace K) : logSpace K := fun w ↦
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹)

@[simp]
/-
**NumberField.mixedEmbedding.logMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberField
.mixedEmbedding`。
形式化陈述：logMap_apply (x : mixedSpace K) (w : {w : InfinitePlace K // w != w₀}) : l
ogMap x w = mult w.val * (Real.log (normAtPlace w.val x) - Real.log (mixedEmbedd
ing.norm x) * (finrank Rat K : Real)⁻¹)
参数：x : mixedSpace K；w : {w : InfinitePlace K // w != w₀}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem logMap_apply (x : mixedSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    logMap x w = mult w.val * (Real.log (normAtPlace w.val x) -
      Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹) := rfl

@[simp]
/-
**NumberField.mixedEmbedding.logMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
mixedEmbedding`。
形式化陈述：logMap_zero : logMap (0 : mixedSpace K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMap_zero : logMap (0 : mixedSpace K) = 0 := by
  ext; simp

@[simp]
/-
**NumberField.mixedEmbedding.logMap_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：logMap_one : logMap (1 : mixedSpace K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMap_one : logMap (1 : mixedSpace K) = 0 := by
  ext; simp

variable {x y : mixedSpace K}
/-
**NumberField.mixedEmbedding.logMap_mul** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：logMap_mul (hx : mixedEmbedding.norm x != 0) (hy : mixedEmbedding.norm y !
= 0) : logMap (x * y) = logMap x + logMap y
参数：hx : mixedEmbedding.norm x != 0；hy : mixedEmbedding.norm y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.mixedEmbedding.norm_ne_zero_iff`：∀ {K : Type u_1} [inst : Fi
eld K] [inst_1 : NumberField K] {x : NumberField.mixedEmbedding.mixedSpace K},  
 NumberField.mixedEmbedding.norm …
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 46 条，此处仅展示前 30 条）
-/
theorem logMap_mul (hx : mixedEmbedding.norm x ≠ 0) (hy : mixedEmbedding.norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap_apply]
  rw [map_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w
/-
**NumberField.mixedEmbedding.logMap_apply_of_norm_eq_one** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：logMap_apply_of_norm_eq_one (hx : mixedEmbedding.norm x = 1) (w : {w : Inf
initePlace K // w != w₀}) : logMap x w = mult w.val * Real.log (normAtPlace w x)
参数：hx : mixedEmbedding.norm x = 1；w : {w : InfinitePlace K // w != w₀}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.logMap_apply`：logMap_apply (x : mixedSpace K)
 (w : {w : InfinitePlace K // w != w₀}) : logMap x w = mult w.val * (Real.log (n
ormAtPlace w.val x) - Real.lo…
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem logMap_apply_of_norm_eq_one (hx : mixedEmbedding.norm x = 1)
    (w : {w : InfinitePlace K // w ≠ w₀}) :
    logMap x w = mult w.val * Real.log (normAtPlace w x) := by
  rw [logMap_apply, hx, Real.log_one, zero_mul, sub_zero]

@[simp]
/-
**NumberField.mixedEmbedding.logMap_eq_logEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.mixedEmbedding`。
形式化陈述：logMap_eq_logEmbedding (u : (𝓞 K)ˣ) : logMap (mixedEmbedding K u) = logEmb
edding K (Additive.ofMul u)
参数：u : (𝓞 K)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
· 使用定理 `NumberField.mixedEmbedding.norm_eq_norm`：norm_eq_norm (x : K) : mixedEmb
edding.norm (mixedEmbedding K x) = |Algebra.norm Rat x|
· 使用定理 `NumberField.Units.norm`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Numb
erField K] (x : (NumberField.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraM
ap (NumberFi…
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K (Additive.ofMul u) := by
  ext; simp
/-
**NumberField.mixedEmbedding.logMap_unit_smul** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：logMap_unit_smul (u : (𝓞 K)ˣ) (hx : mixedEmbedding.norm x != 0) : logMap (
u • x) = logEmbedding K (Additive.ofMul u) + logMap x
参数：u : (𝓞 K)ˣ；hx : mixedEmbedding.norm x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.unitSMul_smul`：∀ (K : Type u_1) [inst : Field
 K] (u : (NumberField.RingOfIntegers K)ˣ) (x : NumberField.mixedEmbedding.mixedS
pace K),   u • x = (NumberFiel…
· 使用定理 `NumberField.mixedEmbedding.logMap_mul`：logMap_mul (hx : mixedEmbedding.n
orm x != 0) (hy : mixedEmbedding.norm y != 0) : logMap (x * y) = logMap x + logM
ap y
· 使用定理 `NumberField.mixedEmbedding.norm_unit`：norm_unit (u : (𝓞 K)ˣ) : mixedEmbe
dding.norm (mixedEmbedding K u) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NumberField.mixedEmbedding.logMap_eq_logEmbedding`：logMap_eq_logEmbeddin
g (u : (𝓞 K)ˣ) : logMap (mixedEmbedding K u) = logEmbedding K (Additive.ofMul u)
-/
theorem logMap_unit_smul (u : (𝓞 K)ˣ) (hx : mixedEmbedding.norm x ≠ 0) :
    logMap (u • x) = logEmbedding K (Additive.ofMul u) + logMap x := by
  rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

variable (x) in
/-
**NumberField.mixedEmbedding.logMap_torsion_smul** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.mixedEmbedding`。
形式化陈述：logMap_torsion_smul {ζ : (𝓞 K)ˣ} (hζ : ζ in torsion K) : logMap (ζ • x) = 
logMap x
参数：𝓞 K；hζ : ζ in torsion K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `NumberField.mixedEmbedding.norm_eq_norm`：norm_eq_norm (x : K) : mixedEmb
edding.norm (mixedEmbedding K x) = |Algebra.norm Rat x|
· 使用定理 `NumberField.Units.norm`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Numb
erField K] (x : (NumberField.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraM
ap (NumberFi…
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.Units.mem_torsion`：mem_torsion {x : (𝓞 K)ˣ} : x in torsion K
 ↔ forall w : InfinitePlace K, w x = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMap_torsion_smul {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap_apply, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
    normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]
/-
**NumberField.mixedEmbedding.logMap_real** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
mixedEmbedding`。
形式化陈述：logMap_real (c : Real) : logMap (c • (1 : mixedSpace K)) = 0
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.logMap_apply`：logMap_apply (x : mixedSpace K)
 (w : {w : InfinitePlace K // w != w₀}) : logMap x w = mult w.val * (Real.log (n
ormAtPlace w.val x) - Real.lo…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_smul`：normAtPlace_smul (w : Infin
itePlace K) (x : mixedSpace K) (c : Real) : normAtPlace w (c • x) = |c| * normAt
Place w x
· 使用定理 `NumberField.mixedEmbedding.norm_smul`：norm_smul (c : Real) (x : mixedSpa
ce K) : mixedEmbedding.norm (c • x) = |c| ^ finrank Rat K * (mixedEmbedding.norm
 x)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
-/
theorem logMap_real (c : ℝ) :
    logMap (c • (1 : mixedSpace K)) = 0 := by
  ext
  rw [logMap_apply, normAtPlace_smul, norm_smul, map_one, map_one, mul_one, mul_one, Real.log_pow,
    mul_comm (finrank ℚ K : ℝ) _, mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr finrank_pos.ne'),
    mul_one, sub_self, mul_zero, Pi.zero_apply]
/-
**NumberField.mixedEmbedding.logMap_real_smul** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：logMap_real_smul (hx : mixedEmbedding.norm x != 0) {c : Real} (hc : c != 0
) : logMap (c • x) = logMap x
参数：hx : mixedEmbedding.norm x != 0；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.norm_smul`：norm_smul (c : Real) (x : mixedSpa
ce K) : mixedEmbedding.norm (c • x) = |c| ^ finrank Rat K * (mixedEmbedding.norm
 x)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_ne_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≠ 0 ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NumberField.mixedEmbedding.logMap_mul`：logMap_mul (hx : mixedEmbedding.n
orm x != 0) (hy : mixedEmbedding.norm y != 0) : logMap (x * y) = logMap x + logM
ap y
· 使用定理 `NumberField.mixedEmbedding.logMap_real`：logMap_real (c : Real) : logMap 
(c • (1 : mixedSpace K)) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem logMap_real_smul (hx : mixedEmbedding.norm x ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  have : mixedEmbedding.norm (c • (1 : mixedSpace K)) ≠ 0 := by
    rw [norm_smul, map_one, mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)
  rw [← smul_one_mul, logMap_mul this hx, logMap_real, zero_add]
/-
**NumberField.mixedEmbedding.logMap_eq_of_normAtPlace_eq** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：logMap_eq_of_normAtPlace_eq (h : forall w, normAtPlace w x = normAtPlace w
 y) : logMap x = logMap y
参数：h : forall w, normAtPlace w x = normAtPlace w y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.mixedEmbedding.norm_eq_of_normAtPlace_eq`：norm_eq_of_normAtP
lace_eq {x y : mixedSpace K} (h : forall w, normAtPlace w x = normAtPlace w y) :
 mixedEmbedding.norm x = mixedEmbedding.no…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logMap_eq_of_normAtPlace_eq (h : ∀ w, normAtPlace w x = normAtPlace w y) :
    logMap x = logMap y := by
  ext
  simp_rw [logMap_apply, h, norm_eq_of_normAtPlace_eq h]

end logMap

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open scoped Classical in
/-- The fundamental cone is a cone in the mixed space, i.e. a subset fixed by multiplication by
a nonzero real number, see `smul_mem_of_mem`, that is also a fundamental domain for the action
of `(𝓞 K)ˣ` modulo torsion, see `exists_unit_smul_mem` and `torsion_smul_mem_of_mem`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone** 是 Mathlib 中的一个定义，位于命名空间 `NumberFi
eld.mixedEmbedding`。
形式化陈述：fundamentalCone : Set (mixedSpace K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)

--- 原说明 ---
The fundamental cone is a cone in the mixed space, i.e. a subset fixed by multip
lication by
a nonzero real number, see `smul_mem_of_mem`, that is also a fundamental domain 
for the action
of `(𝓞 K)ˣ` modulo torsion, see `exists_unit_smul_mem` and `torsion_smul_mem_of_
mem`.
-/
def fundamentalCone : Set (mixedSpace K) :=
  logMap ⁻¹' (ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _)) \
      {x | mixedEmbedding.norm x = 0}
/-
**NumberField.mixedEmbedding.measurableSet_fundamentalCone** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding`。
形式化陈述：measurableSet_fundamentalCone : MeasurableSet (fundamentalCone K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `MeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {m :
 MeasurableSpace α} {mβ : MeasurableSpace β} {t : Set β},   MeasurableSet t → Me
asurable f →…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `ZSpan.fundamentalDomain_measurableSet`：fundamentalDomain_measurableSet [
MeasurableSpace E] [OpensMeasurableSpace E] [Finite ι] : MeasurableSet (fundamen
talDomain b)
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_pi_iff`：measurable_pi_iff {g : α -> forall a, X a} : Measurab
le g ↔ forall a, Measurable fun x => g x a
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Measurable.sub`：∀ {G : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
G] [inst_1 : Sub G] {m : MeasurableSpace α} {f g : α → G}   [MeasurableSub₂ G], 
Meas…
· 使用定理 `ContinuousSub.measurableSub₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Sub γ] [Con…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Measurable.log`：∀ {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}, Me
asurable f → Measurable fun x => Real.log (f x)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
（共 42 条，此处仅展示前 30 条）
-/
theorem measurableSet_fundamentalCone :
    MeasurableSet (fundamentalCone K) := by
  classical
  refine MeasurableSet.diff ?_ ?_
  · unfold logMap
    refine MeasurableSet.preimage (ZSpan.fundamentalDomain_measurableSet _) <|
      measurable_pi_iff.mpr fun w ↦ measurable_const.mul ?_
    exact (continuous_normAtPlace _).measurable.log.sub <|
      (mixedEmbedding.continuous_norm _).measurable.log.mul measurable_const
  · exact measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

namespace fundamentalCone

variable {K} {x y : mixedSpace K} {c : ℝ}

/-
**NumberField.mixedEmbedding.fundamentalCone.norm_pos_of_mem** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：norm_pos_of_mem (hx : x in fundamentalCone K) : 0 < mixedEmbedding.norm x
参数：hx : x in fundamentalCone K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `NumberField.mixedEmbedding.norm_nonneg`：∀ {K : Type u_1} [inst : Field K
] [inst_1 : NumberField K] (x : NumberField.mixedEmbedding.mixedSpace K),   0 ≤ 
NumberField.mixedEmbedding.n…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
-/
theorem norm_pos_of_mem (hx : x ∈ fundamentalCone K) :
    0 < mixedEmbedding.norm x :=
  lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) (Ne.symm hx.2)
/-
**NumberField.mixedEmbedding.fundamentalCone.normAtPlace_pos_of_mem** 是 Mathlib 
中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：normAtPlace_pos_of_mem (hx : x in fundamentalCone K) (w : InfinitePlace K)
 : 0 < normAtPlace w x
参数：hx : x in fundamentalCone K；w : InfinitePlace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.mixedEmbedding.norm_ne_zero_iff`：∀ {K : Type u_1} [inst : Fi
eld K] [inst_1 : NumberField K] {x : NumberField.mixedEmbedding.mixedSpace K},  
 NumberField.mixedEmbedding.norm …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.norm_pos_of_mem`：norm_pos_of_
mem (hx : x in fundamentalCone K) : 0 < mixedEmbedding.norm x
-/
theorem normAtPlace_pos_of_mem (hx : x ∈ fundamentalCone K) (w : InfinitePlace K) :
    0 < normAtPlace w x :=
  lt_of_le_of_ne (normAtPlace_nonneg _ _)
    (mixedEmbedding.norm_ne_zero_iff.mp (norm_pos_of_mem hx).ne' w).symm
/-
**NumberField.mixedEmbedding.fundamentalCone.mem_of_normAtPlace_eq** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：mem_of_normAtPlace_eq (hx : x in fundamentalCone K) (hy : forall w, normAt
Place w y = normAtPlace w x) : y in fundamentalCone K
参数：hx : x in fundamentalCone K；hy : forall w, normAtPlace w y = normAtPlace w x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `NumberField.mixedEmbedding.logMap_eq_of_normAtPlace_eq`：logMap_eq_of_nor
mAtPlace_eq (h : forall w, normAtPlace w x = normAtPlace w y) : logMap x = logMa
p y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.norm_eq_of_normAtPlace_eq`：norm_eq_of_normAtP
lace_eq {x y : mixedSpace K} (h : forall w, normAtPlace w x = normAtPlace w y) :
 mixedEmbedding.norm x = mixedEmbedding.no…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_of_normAtPlace_eq (hx : x ∈ fundamentalCone K)
    (hy : ∀ w, normAtPlace w y = normAtPlace w x) :
    y ∈ fundamentalCone K := by
  refine ⟨?_, by simpa [norm_eq_of_normAtPlace_eq hy] using hx.2⟩
  rw [Set.mem_preimage, logMap_eq_of_normAtPlace_eq hy]
  exact hx.1
/-
**NumberField.mixedEmbedding.fundamentalCone.smul_mem_of_mem** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：smul_mem_of_mem (hx : x in fundamentalCone K) (hc : c != 0) : c • x in fun
damentalCone K
参数：hx : x in fundamentalCone K；hc : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `NumberField.mixedEmbedding.logMap_real_smul`：logMap_real_smul (hx : mixe
dEmbedding.norm x != 0) {c : Real} (hc : c != 0) : logMap (c • x) = logMap x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.norm_smul`：norm_smul (c : Real) (x : mixedSpa
ce K) : mixedEmbedding.norm (c • x) = |c| ^ finrank Rat K * (mixedEmbedding.norm
 x)
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_ne_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≠ 0 ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem smul_mem_of_mem (hx : x ∈ fundamentalCone K) (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_real_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_ofPred_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩
/-
**NumberField.mixedEmbedding.fundamentalCone.smul_mem_iff_mem** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：smul_mem_iff_mem (hc : c != 0) : c • x in fundamentalCone K ↔ x in fundame
ntalCone K
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_inv_smul_iff₀`：eq_inv_smul_iff₀ (ha : a != 0) {x y : β} : x = a⁻¹ • y
 ↔ a • x = y
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.smul_mem_of_mem`：smul_mem_of_
mem (hx : x in fundamentalCone K) (hc : c != 0) : c • x in fundamentalCone K
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
theorem smul_mem_iff_mem (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_of_mem h hc⟩
  convert! smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

set_option backward.isDefEq.respectTransparency.types false in
/-
**NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：exists_unit_smul_mem (hx : mixedEmbedding.norm x != 0) : exists u : (𝓞 K)ˣ
, u • x in fundamentalCone K
参数：hx : mixedEmbedding.norm x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `ZSpan.exist_unique_vadd_mem_fundamentalDomain`：exist_unique_vadd_mem_fun
damentalDomain [Finite ι] (x : E) : exists! v : span Int (Set.range b), v +ᵥ x i
n fundamentalDomain b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.ofZLatticeBasis_span`：ofZLatticeBasis_span : span Int (Set.
range (b.ofZLatticeBasis K)) = L
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `NumberField.mixedEmbedding.logMap_unit_smul`：logMap_unit_smul (u : (𝓞 K)
ˣ) (hx : mixedEmbedding.norm x != 0) : logMap (u • x) = logEmbedding K (Additive
.ofMul u) + logMap x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.norm_eq_norm`：norm_eq_norm (x : K) : mixedEmb
edding.norm (mixedEmbedding K x) = |Algebra.norm Rat x|
· 使用定理 `NumberField.Units.norm`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Numb
erField K] (x : (NumberField.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraM
ap (NumberFi…
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem exists_unit_smul_mem (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ ZSpan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unit_smul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩
/-
**NumberField.mixedEmbedding.fundamentalCone.torsion_smul_mem_of_mem** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：torsion_smul_mem_of_mem (hx : x in fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ
 in torsion K) : ζ • x in fundamentalCone K
参数：hx : x in fundamentalCone K；𝓞 K；hζ : ζ in torsion K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `NumberField.mixedEmbedding.logMap_torsion_smul`：logMap_torsion_smul {ζ :
 (𝓞 K)ˣ} (hζ : ζ in torsion K) : logMap (ζ • x) = logMap x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `NumberField.mixedEmbedding.unitSMul_smul`：∀ (K : Type u_1) [inst : Field
 K] (u : (NumberField.RingOfIntegers K)ˣ) (x : NumberField.mixedEmbedding.mixedS
pace K),   u • x = (NumberFiel…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `NumberField.mixedEmbedding.norm_unit`：norm_unit (u : (𝓞 K)ˣ) : mixedEmbe
dding.norm (mixedEmbedding K u) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem torsion_smul_mem_of_mem (hx : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  constructor
  · rw [Set.mem_preimage, logMap_torsion_smul _ hζ]
    exact hx.1
  · rw [Set.mem_ofPred_eq, unitSMul_smul, map_mul, norm_unit, one_mul]
    exact hx.2
/-
**NumberField.mixedEmbedding.fundamentalCone.unit_smul_mem_iff_mem_torsion** 是 M
athlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：unit_smul_mem_iff_mem_torsion (hx : x in fundamentalCone K) (u : (𝓞 K)ˣ) :
 u • x in fundamentalCone K ↔ u in torsion K
参数：hx : x in fundamentalCone K；u : (𝓞 K)ˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.dirichletUnitTheorem.logEmbedding_eq_zero_iff`：logEmbe
dding_eq_zero_iff {x : (𝓞 K)ˣ} : logEmbedding K (Additive.ofMul x) = 0 ↔ x in to
rsion K
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.ofZLatticeBasis_span`：ofZLatticeBasis_span : span Int (Set.
range (b.ofZLatticeBasis K)) = L
· 使用定理 `trivial`：True
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `ZSpan.exist_unique_vadd_mem_fundamentalDomain`：exist_unique_vadd_mem_fun
damentalDomain [Finite ι] (x : E) : exists! v : span Int (Set.range b), v +ᵥ x i
n fundamentalDomain b
· 使用定理 `AddSubmonoid.mk_vadd`：∀ {M' : Type u_1} {α : Type u_2} [inst : AddZeroCl
ass M'] [inst_1 : VAdd M' α] {S : AddSubmonoid M'} (g : M')   (hg : g ∈ S) (a : 
α), ⟨g, hg…
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `NumberField.mixedEmbedding.logMap_unit_smul`：logMap_unit_smul (u : (𝓞 K)
ˣ) (hx : mixedEmbedding.norm x != 0) : logMap (u • x) = logEmbedding K (Additive
.ofMul u) + logMap x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.torsion_smul_mem_of_mem`：tors
ion_smul_mem_of_mem (hx : x in fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ in torsio
n K) : ζ • x in fundamentalCone K
-/
theorem unit_smul_mem_iff_mem_torsion (hx : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ torsion_smul_mem_of_mem hx h⟩
  rw [← logEmbedding_eq_zero_iff]
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ
  refine (Subtype.mk_eq_mk (h := ?_) (h' := Submodule.zero_mem _)).mp <|
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)).unique ?_ ?_
  · rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)]
    exact ⟨u, trivial, rfl⟩
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unit_smul _ hx.2]
    exact h.1
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
    exact hx.1

variable (K) in
/-- The intersection between the fundamental cone and the `integerLattice`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSet** 是 Mathlib 中的一个定义，位于命名空
间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSet : Set (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intersection between the fundamental cone and the `integerLattice`.
-/
def integerSet : Set (mixedSpace K) :=
  fundamentalCone K ∩ mixedEmbedding.integerLattice K
/-
**NumberField.mixedEmbedding.fundamentalCone.mem_integerSet** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：mem_integerSet {a : mixedSpace K} : a in integerSet K ↔ a in fundamentalCo
ne K ∧ exists x : 𝓞 K, mixedEmbedding K x = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_integerSet {a : mixedSpace K} :
    a ∈ integerSet K ↔ a ∈ fundamentalCone K ∧ ∃ x : 𝓞 K, mixedEmbedding K x = a := by
  simp only [integerSet, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_range,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]

/-- If `a` is in `integerSet`, then there is a *unique* algebraic integer in `𝓞 K` such
that `mixedEmbedding K x = a`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.existsUnique_preimage_of_mem_intege
rSet** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：existsUnique_preimage_of_mem_integerSet {a : mixedSpace K} (ha : a in inte
gerSet K) : exists! x : 𝓞 K, mixedEmbedding K x = a
参数：ha : a in integerSet K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mem_integerSet`：mem_integerSe
t {a : mixedSpace K} : a in integerSet K ↔ a in fundamentalCone K ∧ exists x : 𝓞
 K, mixedEmbedding K x = a
· 使用定理 `Function.Injective.existsUnique_of_mem_range`：∀ {α : Type u_1} {β : Type
 u_2} {f : α → β}, Function.Injective f → ∀ {b : β}, b ∈ Set.range f → ∃! a, f a
 = b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `NumberField.mixedEmbedding_injective`：∀ (K : Type u_1) [inst : Field K] 
[NumberField K], Function.Injective ⇑(NumberField.mixedEmbedding K)
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
If `a` is in `integerSet`, then there is a *unique* algebraic integer in `𝓞 K` s
uch
that `mixedEmbedding K x = a`.
-/
theorem existsUnique_preimage_of_mem_integerSet {a : mixedSpace K} (ha : a ∈ integerSet K) :
    ∃! x : 𝓞 K, mixedEmbedding K x = a := by
  obtain ⟨_, ⟨x, rfl⟩⟩ := mem_integerSet.mp ha
  refine Function.Injective.existsUnique_of_mem_range ?_ (Set.mem_range_self x)
  exact (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective
/-
**NumberField.mixedEmbedding.fundamentalCone.ne_zero_of_mem_integerSet** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：ne_zero_of_mem_integerSet (a : integerSet K) : (a : mixedSpace K) != 0
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.Units.instDiscrete_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], DiscreteTopology ↥(NumberField.Units.unitLattice
 K)
· 使用定理 `NumberField.Units.instZLattice_unitLattice`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K], IsZLattice ℝ (NumberField.Units.unitLattice K)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_mem_integerSet (a : integerSet K) : (a : mixedSpace K) ≠ 0 := by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

open scoped nonZeroDivisors

/-- For `a : integerSet K`, the unique nonzero algebraic integer `x` such that its image by
`mixedEmbedding` is equal to `a`. Note that we state the fact that `x ≠ 0` by saying that `x` is
a nonzero divisors since we will use later on the isomorphism
`Ideal.associatesNonZeroDivisorsEquivIsPrincipal`, see `integerSetEquiv`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.preimageOfMemIntegerSet** 是 Mathlib
 中的一个定义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：preimageOfMemIntegerSet (a : integerSet K) : (𝓞 K)⁰
参数：a : integerSet K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `a : integerSet K`, the unique nonzero algebraic integer `x` such that its i
mage by
`mixedEmbedding` is equal to `a`. Note that we state the fact that `x ≠ 0` by sa
ying that `x` is
a nonzero divisors since we will use later on the isomorphism
`Ideal.associatesNonZeroDivisorsEquivIsPrincipal`, see `integerSetEquiv`.
-/
def preimageOfMemIntegerSet (a : integerSet K) : (𝓞 K)⁰ :=
  ⟨(mem_integerSet.mp a.prop).2.choose, mem_nonZeroDivisors_of_ne_zero (by
  simp_rw [ne_eq, ← RingOfIntegers.coe_injective.eq_iff, ← (mixedEmbedding_injective K).eq_iff,
    map_zero, (mem_integerSet.mp a.prop).2.choose_spec, ne_zero_of_mem_integerSet,
    not_false_eq_true])⟩

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.mixedEmbedding_preimageOfMemInteger
Set** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) : mixedEmbedding
 K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K)
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.preimageOfMemIntegerSet.eq_1`
：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]   (a : ↑(NumberField
.mixedEmbedding.fundamentalCone.integerSet K)),   NumberField…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mem_integerSet`：mem_integerSe
t {a : mixedSpace K} : a in integerSet K ↔ a in fundamentalCone K ∧ exists x : 𝓞
 K, mixedEmbedding K x = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) :
    mixedEmbedding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K) := by
  rw [preimageOfMemIntegerSet, (mem_integerSet.mp a.prop).2.choose_spec]
/-
**NumberField.mixedEmbedding.fundamentalCone.preimageOfMemIntegerSet_mixedEmbedd
ing** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：preimageOfMemIntegerSet_mixedEmbedding {x : (𝓞 K)} (hx : mixedEmbedding K 
(x : 𝓞 K) in integerSet K) : preimageOfMemIntegerSet (⟨mixedEmbedding K (x : 𝓞 K
), hx⟩) = x
参数：𝓞 K；hx : mixedEmbedding K (x : 𝓞 K) in integerSet K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NumberField.mixedEmbedding_injective`：∀ (K : Type u_1) [inst : Field K] 
[NumberField K], Function.Injective ⇑(NumberField.mixedEmbedding K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mixedEmbedding_preimageOfMemI
ntegerSet`：mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) : mixedEmbe
dding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimageOfMemIntegerSet_mixedEmbedding {x : (𝓞 K)}
    (hx : mixedEmbedding K (x : 𝓞 K) ∈ integerSet K) :
    preimageOfMemIntegerSet (⟨mixedEmbedding K (x : 𝓞 K), hx⟩) = x := by
  simp_rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfMemIntegerSet]

/-- If `x : mixedSpace K` is nonzero and the image of an algebraic integer, then there exists a
unit such that `u • x ∈ integerSet K`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.exists_unitSMul_mem_integerSet** 是 
Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：exists_unitSMul_mem_integerSet {x : mixedSpace K} (hx : x != 0) (hx' : x i
n mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) : exists u : (𝓞 K)ˣ, u •
 x in integerSet K
参数：hx : x != 0；hx' : x in mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `NumberField.mixedEmbedding.norm_eq_zero_iff'`：norm_eq_zero_iff' {x : mix
edSpace K} (hx : x in Set.range (mixedEmbedding K)) : mixedEmbedding.norm x = 0 
↔ x = 0
· 使用定理 `Set.mem_range_of_mem_image`：mem_range_of_mem_image (f : α -> β) (s) {x :
 β} (h : x in f '' s) : x in range f
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem`：exists_
unit_smul_mem (hx : mixedEmbedding.norm x != 0) : exists u : (𝓞 K)ˣ, u • x in fu
ndamentalCone K
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mem_integerSet`：mem_integerSe
t {a : mixedSpace K} : a in integerSet K ↔ a in fundamentalCone K ∧ exists x : 𝓞
 K, mixedEmbedding K x = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `x : mixedSpace K` is nonzero and the image of an algebraic integer, then the
re exists a
unit such that `u • x ∈ integerSet K`.
-/
theorem exists_unitSMul_mem_integerSet {x : mixedSpace K} (hx : x ≠ 0)
    (hx' : x ∈ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integerSet K := by
  replace hx : mixedEmbedding.norm x ≠ 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hx
  obtain ⟨_, ⟨x, rfl⟩, _, rfl⟩ := hx'
  exact ⟨u, mem_integerSet.mpr ⟨hu, u * x, by simp_rw [unitSMul_smul, ← map_mul]⟩⟩

/-- The set `integerSet K` is stable under the action of the torsion. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.torsion_unitSMul_mem_integerSet** 是
 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：torsion_unitSMul_mem_integerSet {x : mixedSpace K} {ζ : (𝓞 K)ˣ} (hζ : ζ in
 torsion K) (hx : x in integerSet K) : ζ • x in integerSet K
参数：𝓞 K；hζ : ζ in torsion K；hx : x in integerSet K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mem_integerSet`：mem_integerSe
t {a : mixedSpace K} : a in integerSet K ↔ a in fundamentalCone K ∧ exists x : 𝓞
 K, mixedEmbedding K x = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.torsion_smul_mem_of_mem`：tors
ion_smul_mem_of_mem (hx : x in fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ in torsio
n K) : ζ • x in fundamentalCone K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The set `integerSet K` is stable under the action of the torsion.
-/
theorem torsion_unitSMul_mem_integerSet {x : mixedSpace K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integerSet K) : ζ • x ∈ integerSet K := by
  obtain ⟨a, ⟨_, rfl⟩, rfl⟩ := (mem_integerSet.mp hx).2
  refine mem_integerSet.mpr ⟨torsion_smul_mem_of_mem hx.1 hζ, ⟨ζ * a, by simp⟩⟩

/-- The action of `torsion K` on `integerSet K`. -/
@[simps]
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetTorsionSMul** 是 Mathlib 中
的一个实例，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetTorsionSMul : SMul (torsion K) (integerSet K) where smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.torsion_unitSMul_mem_integerS
et`：torsion_unitSMul_mem_integerSet {x : mixedSpace K} {ζ : (𝓞 K)ˣ} (hζ : ζ in t
orsion K) (hx : x in integerSet K) : ζ • x in integerSet K

--- 原说明 ---
The action of `torsion K` on `integerSet K`.
-/
instance integerSetTorsionSMul : SMul (torsion K) (integerSet K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ ↦ ⟨ζ • x, torsion_unitSMul_mem_integerSet hζ hx⟩
/-
**NumberField.mixedEmbedding.fundamentalCone.** 是 Mathlib 中的一个实例，位于命名空间 `NumberF
ield.mixedEmbedding.fundamentalCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (torsion K) (integerSet K) where
  one_smul := fun _ ↦ by
    rw [Subtype.mk_eq_mk, integerSetTorsionSMul_smul_coe, OneMemClass.coe_one, one_smul]
  mul_smul := fun _ _ _ ↦ by
    rw [Subtype.mk_eq_mk]
    simp_rw [integerSetTorsionSMul_smul_coe, Subgroup.coe_mul, mul_smul]

/-- The `mixedEmbedding.norm` of `a : integerSet K` as a natural number, see also
`intNorm_coe`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.intNorm** 是 Mathlib 中的一个定义，位于命名空间 `
NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：intNorm (a : integerSet K) : Nat
参数：a : integerSet K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `mixedEmbedding.norm` of `a : integerSet K` as a natural number, see also
`intNorm_coe`.
-/
def intNorm (a : integerSet K) : ℕ := (Algebra.norm ℤ (preimageOfMemIntegerSet a : 𝓞 K)).natAbs

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.intNorm_coe** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：intNorm_coe (a : integerSet K) : (intNorm a : Real) = mixedEmbedding.norm 
(a : mixedSpace K)
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.intNorm.eq_1`：∀ {K : Type u_1
} [inst : Field K] [inst_1 : NumberField K]   (a : ↑(NumberField.mixedEmbedding.
fundamentalCone.integerSet K)),   NumberField…
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Algebra.coe_norm_int`：Algebra.coe_norm_int : (Algebra.norm Int x : Rat) 
= Algebra.norm Rat (x : K)
· 使用定理 `NumberField.mixedEmbedding.norm_eq_norm`：norm_eq_norm (x : K) : mixedEmb
edding.norm (mixedEmbedding K x) = |Algebra.norm Rat x|
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mixedEmbedding_preimageOfMemI
ntegerSet`：mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) : mixedEmbe
dding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K)
-/
theorem intNorm_coe (a : integerSet K) :
    (intNorm a : ℝ) = mixedEmbedding.norm (a : mixedSpace K) := by
  rw [intNorm, Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, Algebra.coe_norm_int,
    ← norm_eq_norm, mixedEmbedding_preimageOfMemIntegerSet]

/-- The norm `intNorm` lifts to a function on `integerSet K` modulo `torsion K`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.quotIntNorm** 是 Mathlib 中的一个定义，位于命名
空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：quotIntNorm : Quotient (MulAction.orbitRel (torsion K) (integerSet K)) -> 
Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm `intNorm` lifts to a function on `integerSet K` modulo `torsion K`.
-/
def quotIntNorm :
    Quotient (MulAction.orbitRel (torsion K) (integerSet K)) → ℕ :=
  Quotient.lift (fun x ↦ intNorm x) fun a b ⟨u, hu⟩ ↦ by
    rw [← Nat.cast_inj (R := ℝ), intNorm_coe, intNorm_coe, ← hu, integerSetTorsionSMul_smul_coe,
      norm_unit_smul]

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.quotIntNorm_apply** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：quotIntNorm_apply (a : integerSet K) : quotIntNorm ⟦a⟧ = intNorm a
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotIntNorm_apply (a : integerSet K) : quotIntNorm ⟦a⟧ = intNorm a := rfl

variable (K) in
/-- The map that sends an element of `a : integerSet K` to the associates class
of its preimage in `(𝓞 K)⁰`. By quotienting by the kernel of the map, which is equal to the
subgroup of torsion, we get the equivalence `integerSetQuotEquivAssociates`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetToAssociates** 是 Mathlib 
中的一个定义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetToAssociates (a : integerSet K) : Associates (𝓞 K)⁰
参数：a : integerSet K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that sends an element of `a : integerSet K` to the associates class
of its preimage in `(𝓞 K)⁰`. By quotienting by the kernel of the map, which is e
qual to the
subgroup of torsion, we get the equivalence `integerSetQuotEquivAssociates`.
-/
def integerSetToAssociates (a : integerSet K) : Associates (𝓞 K)⁰ :=
  ⟦preimageOfMemIntegerSet a⟧

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetToAssociates_apply** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetToAssociates_apply (a : integerSet K) : integerSetToAssociates K
 a = ⟦preimageOfMemIntegerSet a⟧
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integerSetToAssociates_apply (a : integerSet K) :
    integerSetToAssociates K a = ⟦preimageOfMemIntegerSet a⟧ := rfl

variable (K) in
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetToAssociates_surjective**
 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetToAssociates_surjective : Function.Surjective (integerSetToAssoc
iates K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.exists_unitSMul_mem_integerSe
t`：exists_unitSMul_mem_integerSet {x : mixedSpace K} (hx : x != 0) (hx' : x in m
ixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) : exists u…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `NumberField.mixedEmbedding.instNontrivialMixedSpace`：∀ (K : Type u_1) [i
nst : Field K] [NumberField K], Nontrivial (NumberField.mixedEmbedding.mixedSpac
e K)
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `NumberField.RingOfIntegers.coe_ne_zero_iff`：coe_ne_zero_iff {x : 𝓞 K} : 
algebraMap _ K x != 0 ↔ x != 0
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NumberField.mixedEmbedding_injective`：∀ (K : Type u_1) [inst : Field K] 
[NumberField K], Function.Injective ⇑(NumberField.mixedEmbedding K)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mixedEmbedding_preimageOfMemI
ntegerSet`：mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) : mixedEmbe
dding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe`：∀ {M₀ : Type u_1} [ins
t : MonoidWithZero M₀] (u : M₀ˣ), ↑↑(unitsNonZeroDivisorsEquiv.symm u)⁻¹ = ↑u⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integerSetToAssociates_surjective :
    Function.Surjective (integerSetToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) ∈ integerSet K := by
    refine exists_unitSMul_mem_integerSet ?_ ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
    exact (map_ne_zero _).mpr <| RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero _)
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨unitsNonZeroDivisorsEquiv.symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfMemIntegerSet,
    unitSMul_smul, ← map_mul, mul_comm, map_inv, val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe,
    Units.mul_inv_cancel_right]
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetToAssociates_eq_iff** 是 M
athlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetToAssociates_eq_iff (a b : integerSet K) : integerSetToAssociate
s K a = integerSetToAssociates K b ↔ exists ζ : torsion K, ζ • a = b
参数：a b : integerSet K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NumberField.mixedEmbedding_injective`：∀ (K : Type u_1) [inst : Field K] 
[NumberField K], Function.Injective ⇑(NumberField.mixedEmbedding K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mixedEmbedding_preimageOfMemI
ntegerSet`：mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) : mixedEmbe
dding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.unit_smul_mem_iff_mem_torsion
`：unit_smul_mem_iff_mem_torsion (hx : x in fundamentalCone K) (u : (𝓞 K)ˣ) : u •
 x in fundamentalCone K ↔ u in torsion K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `unitsNonZeroDivisorsEquiv_apply`：∀ {M₀ : Type u_1} [inst : MonoidWithZer
o M₀] (a : (↥(nonZeroDivisors M₀))ˣ),   unitsNonZeroDivisorsEquiv a = (↑(Units.m
ap (nonZeroDivisors M…
· 使用定理 `val_unitsNonZeroDivisorsEquiv_symm_apply_coe`：∀ {M₀ : Type u_1} [inst : 
MonoidWithZero M₀] (u : M₀ˣ), ↑↑(unitsNonZeroDivisorsEquiv.symm u) = ↑u
-/
theorem integerSetToAssociates_eq_iff (a b : integerSet K) :
    integerSetToAssociates K a = integerSetToAssociates K b ↔
      ∃ ζ : torsion K, ζ • a = b := by
  simp_rw [integerSetToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfMemIntegerSet, integerSetTorsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ ↦  ⟨⟨unitsNonZeroDivisorsEquiv u, ?_⟩, by simpa using h⟩,
    fun ⟨⟨u, _⟩, h⟩ ↦ ⟨unitsNonZeroDivisorsEquiv.symm u, by simpa using h⟩⟩
  exact (unit_smul_mem_iff_mem_torsion a.prop.1 _).mp (by simpa [h] using b.prop.1)

variable (K) in
/-- The equivalence between `integerSet K` modulo `torsion K` and `Associates (𝓞 K)⁰`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetQuotEquivAssociates** 是 M
athlib 中的一个定义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetQuotEquivAssociates : Quotient (MulAction.orbitRel (torsion K) (
integerSet K)) ≃ Associates (𝓞 K)⁰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `integerSet K` modulo `torsion K` and `Associates (𝓞 K)⁰
`.
-/
def integerSetQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integerSet K)) ≃ Associates (𝓞 K)⁰ :=
  Equiv.ofBijective
    (Quotient.lift (integerSetToAssociates K)
      fun _ _ h ↦ ((integerSetToAssociates_eq_iff _ _).mpr h).symm)
    ⟨Setoid.lift_injective_iff_ker_eq_of_le _ |>.mpr <| by
        ext a b
        rw [Setoid.ker_def, eq_comm, integerSetToAssociates_eq_iff b a,
          MulAction.orbitRel_apply, MulAction.mem_orbit_iff],
        (Quot.surjective_lift _).mpr (integerSetToAssociates_surjective K)⟩

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetQuotEquivAssociates_apply
** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetQuotEquivAssociates_apply (a : integerSet K) : integerSetQuotEqu
ivAssociates K ⟦a⟧ = ⟦preimageOfMemIntegerSet a⟧
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integerSetQuotEquivAssociates_apply (a : integerSet K) :
    integerSetQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfMemIntegerSet a⟧ := rfl
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetTorsionSMul_stabilizer** 
是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetTorsionSMul_stabilizer (a : integerSet K) : MulAction.stabilizer
 (torsion K) a = ⊥
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.eq_bot_iff_forall`：eq_bot_iff_forall : H = ⊥ ↔ forall x in H, x
 = (1 : G)
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OneMemClass.coe_eq_one`：coe_eq_one {x : S'} : (↑x : M₁) = 1 ↔ x = 1
· 使用定理 `Units.val_eq_one`：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
· 使用定理 `mul_eq_right₀`：mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b != 0) : a
 * b = b ↔ a = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.RingOfIntegers.ext_iff`：∀ {K : Type u_1} [inst : Field K] {x
 y : NumberField.RingOfIntegers K}, x = y ↔ ↑x = ↑y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NumberField.mixedEmbedding_injective`：∀ (K : Type u_1) [inst : Field K] 
[NumberField K], Function.Injective ⇑(NumberField.mixedEmbedding K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mixedEmbedding_preimageOfMemI
ntegerSet`：mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) : mixedEmbe
dding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K)
· 使用定理 `NumberField.mixedEmbedding.unitSMul_smul`：∀ (K : Type u_1) [inst : Field
 K] (u : (NumberField.RingOfIntegers K)ˣ) (x : NumberField.mixedEmbedding.mixedS
pace K),   u • x = (NumberFiel…
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.integerSetTorsionSMul_smul_co
e`：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (x : ↥(NumberField
.Units.torsion K))   (x_1 : ↑(NumberField.mixedEmbedding.fundam…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
-/
theorem integerSetTorsionSMul_stabilizer (a : integerSet K) :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integerSetTorsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfMemIntegerSet, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

open Submodule Ideal

variable (K) in
/-- The equivalence between `integerSet K` and the product of the set of nonzero principal
ideals of `K` and the torsion of `K`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetEquiv** 是 Mathlib 中的一个定义，
位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetEquiv : integerSet K ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val}
 × torsion K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
The equivalence between `integerSet K` and the product of the set of nonzero pri
ncipal
ideals of `K` and the torsion of `K`.
-/
def integerSetEquiv :
    integerSet K ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} × torsion K :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integerSet K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integerSetTorsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ ↦ (integerSetQuotEquivAssociates K).trans
        (Ideal.associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetEquiv_apply_fst** 是 Mathl
ib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetEquiv_apply_fst (a : integerSet K) : ((integerSetEquiv K a).1 : 
Ideal (𝓞 K)) = span {(preimageOfMemIntegerSet a : 𝓞 K)}
参数：a : integerSet K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integerSetEquiv_apply_fst (a : integerSet K) :
    ((integerSetEquiv K a).1 : Ideal (𝓞 K)) = span {(preimageOfMemIntegerSet a : 𝓞 K)} := rfl

variable (K) in
/-- For an integer `n`, The equivalence between the elements of `integerSet K` of norm `n`
and the product of the set of nonzero principal ideals of `K` of norm `n` and the torsion of `K`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetEquivNorm** 是 Mathlib 中的一
个定义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetEquivNorm (n : Nat) : {a : integerSet K // mixedEmbedding.norm (
a : mixedSpace K) = n} ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧ 
absNorm (I : Ideal (𝓞 K)) = n} × (torsion K)
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)

--- 原说明 ---
For an integer `n`, The equivalence between the elements of `integerSet K` of no
rm `n`
and the product of the set of nonzero principal ideals of `K` of norm `n` and th
e torsion of `K`.
-/
def integerSetEquivNorm (n : ℕ) :
    {a : integerSet K // mixedEmbedding.norm (a : mixedSpace K) = n} ≃
      {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      Equiv.subtypeEquiv (integerSetEquiv K) fun _ ↦ by simp_rw [← intNorm_coe, intNorm,
        Nat.cast_inj, integerSetEquiv_apply_fst, absNorm_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} ↦ absNorm (I : Ideal (𝓞 K)) = n)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) := Equiv.prodCongrLeft fun _ ↦
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1) (fun I ↦ absNorm I.1 = n))

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.integerSetEquivNorm_apply_fst** 是 M
athlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：integerSetEquivNorm_apply_fst {n : Nat} (a : {a : integerSet K // mixedEmb
edding.norm (a : mixedSpace K) = n}) : ((integerSetEquivNorm K n a).1 : Ideal (𝓞
 K)) = span {(preimageOfMemIntegerSet a.val : 𝓞 K)}
参数：a : {a : integerSet K // mixedEmbedding.norm (a : mixedSpace K) = n}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.subtypeEquiv_apply`：∀ {α : Sort u_1} {β : Sort u_4} {p : α → Prop}
 {q : β → Prop} (e : α ≃ β) (h : ∀ (a : α), p a ↔ q (e a))   (a : { a // p a }),
 (e.subtypeEqu…
· 使用定理 `Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe`：∀ {α : Type u} (p q : α
 → Prop) (a : { x // q ↑x }), ↑((Equiv.subtypeSubtypeEquivSubtypeInter p q) a) =
 ↑↑a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integerSetEquivNorm_apply_fst {n : ℕ}
    (a : {a : integerSet K // mixedEmbedding.norm (a : mixedSpace K) = n}) :
    ((integerSetEquivNorm K n a).1 : Ideal (𝓞 K)) =
      span {(preimageOfMemIntegerSet a.val : 𝓞 K)} := by
  simp_rw [integerSetEquivNorm, Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.trans_def,
    Equiv.prodCongrLeft, Equiv.trans_apply, Equiv.subtypeEquiv_apply, Equiv.coe_fn_mk,
    Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe, integerSetEquiv_apply_fst]

variable (K)

/-- For `n` positive, the number of principal ideals in `𝓞 K` of norm `n` multiplied by the order
of the torsion of `K` is equal to the number of elements in `integerSet K` of norm `n`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_norm_eq_mul_torsio
n** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：card_isPrincipal_norm_eq_mul_torsion (n : Nat) : Nat.card {I : (Ideal (𝓞 K
))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧ absNorm (I : Ideal (𝓞 K)) = n} * torsionOr
der K = Nat.card {a : integerSet K | mixedEmbedding.norm (a : mixedSpace K) = n}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Units.torsionOrder.eq_1`：∀ (K : Type u_1) [inst : Field K], 
NumberField.Units.torsionOrder K = Nat.card ↥(NumberField.Units.torsion K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
For `n` positive, the number of principal ideals in `𝓞 K` of norm `n` multiplied
 by the order
of the torsion of `K` is equal to the number of elements in `integerSet K` of no
rm `n`.
-/
theorem card_isPrincipal_norm_eq_mul_torsion (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n} * torsionOrder K =
        Nat.card {a : integerSet K | mixedEmbedding.norm (a : mixedSpace K) = n} := by
  rw [torsionOrder, ← Nat.card_prod]
  exact Nat.card_congr (integerSetEquivNorm K n).symm

variable (J : (Ideal (𝓞 K))⁰)

/-- The intersection between the fundamental cone and the `idealLattice` defined by the image of
the integral ideal `J`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.idealSet** 是 Mathlib 中的一个定义，位于命名空间 
`NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：idealSet : Set (mixedSpace K)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
The intersection between the fundamental cone and the `idealLattice` defined by 
the image of
the integral ideal `J`.
-/
def idealSet : Set (mixedSpace K) :=
  fundamentalCone K ∩ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))

set_option backward.isDefEq.respectTransparency.types false in
variable {K J} in
/-
**NumberField.mixedEmbedding.fundamentalCone.mem_idealSet** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：mem_idealSet : x in idealSet K J ↔ x in fundamentalCone K ∧ exists a : (𝓞 
K), (a : 𝓞 K) in (J : Set (𝓞 K)) ∧ mixedEmbedding K (a : 𝓞 K) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_idealSet :
    x ∈ idealSet K J ↔ x ∈ fundamentalCone K ∧ ∃ a : (𝓞 K), (a : 𝓞 K) ∈ (J : Set (𝓞 K)) ∧
      mixedEmbedding K (a : 𝓞 K) = x := by
  simp_rw [idealSet, Set.mem_inter_iff, idealLattice, SetLike.mem_coe, FractionalIdeal.coe_mk0,
    LinearMap.mem_range, LinearMap.coe_comp, LinearMap.coe_restrictScalars, coe_subtype,
    Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, Subtype.exists,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal, exists_prop', nonempty_prop,
    exists_exists_and_eq_and]

/-- The map that sends `a : idealSet` to an element of `integerSet`. This map exists because
`J` is an integral ideal. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.idealSetMap** 是 Mathlib 中的一个定义，位于命名
空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：idealSetMap : idealSet K J -> integerSet K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map that sends `a : idealSet` to an element of `integerSet`. This map exists
 because
`J` is an integral ideal.
-/
def idealSetMap : idealSet K J → integerSet K :=
  fun ⟨a, ha⟩ ↦ ⟨a, mem_integerSet.mpr ⟨(mem_idealSet.mp ha).1, (mem_idealSet.mp ha).2.choose,
    (mem_idealSet.mp ha).2.choose_spec.2⟩⟩

@[simp]
/-
**NumberField.mixedEmbedding.fundamentalCone.idealSetMap_apply** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：idealSetMap_apply (a : idealSet K J) : (idealSetMap K J a : mixedSpace K) 
= a
参数：a : idealSet K J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idealSetMap_apply (a : idealSet K J) : (idealSetMap K J a : mixedSpace K) = a := rfl
/-
**NumberField.mixedEmbedding.fundamentalCone.preimage_of_IdealSetMap** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：preimage_of_IdealSetMap (a : idealSet K J) : (preimageOfMemIntegerSet (ide
alSetMap K J a) : 𝓞 K) in (J : Set (𝓞 K))
参数：a : idealSet K J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.mem_idealSet`：mem_idealSet : 
x in idealSet K J ↔ x in fundamentalCone K ∧ exists a : (𝓞 K), (a : 𝓞 K) in (J :
 Set (𝓞 K)) ∧ mixedEmbedding K (a : 𝓞 K) = x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.preimageOfMemIntegerSet_mixed
Embedding`：preimageOfMemIntegerSet_mixedEmbedding {x : (𝓞 K)} (hx : mixedEmbeddi
ng K (x : 𝓞 K) in integerSet K) : preimageOfMemIntegerSet (⟨mixedEmbedd…
-/
theorem preimage_of_IdealSetMap (a : idealSet K J) :
    (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) ∈ (J : Set (𝓞 K)) := by
  obtain ⟨_, ⟨x, hx₁, hx₂⟩⟩ := mem_idealSet.mp a.prop
  simp_rw [idealSetMap, ← hx₂, preimageOfMemIntegerSet_mixedEmbedding]
  exact hx₁

/-- The map `idealSetMap` is actually an equiv between `idealSet K J` and the elements of
`integerSet K` whose preimage lies in `J`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：idealSetEquiv : idealSet K J ≃ {a : integerSet K | (preimageOfMemIntegerSe
t a : 𝓞 K) in (J : Set (𝓞 K))}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.preimage_of_IdealSetMap`：prei
mage_of_IdealSetMap (a : idealSet K J) : (preimageOfMemIntegerSet (idealSetMap K
 J a) : 𝓞 K) in (J : Set (𝓞 K))

--- 原说明 ---
The map `idealSetMap` is actually an equiv between `idealSet K J` and the elemen
ts of
`integerSet K` whose preimage lies in `J`.
-/
def idealSetEquiv : idealSet K J ≃
    {a : integerSet K | (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Set (𝓞 K))} :=
  Equiv.ofBijective (fun a ↦ ⟨idealSetMap K J a, preimage_of_IdealSetMap K J a⟩)
    ⟨fun _ _ h ↦ (by
        simp_rw [Subtype.ext_iff, idealSetMap_apply] at h
        rwa [Subtype.ext_iff]),
    fun ⟨a, ha₂⟩ ↦ ⟨⟨a.val, mem_idealSet.mpr ⟨a.prop.1,
        ⟨preimageOfMemIntegerSet a, ha₂, mixedEmbedding_preimageOfMemIntegerSet a⟩⟩⟩, rfl⟩⟩

variable {K J}
/-
**NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv_apply** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：idealSetEquiv_apply (a : idealSet K J) : (idealSetEquiv K J a : mixedSpace
 K) = a
参数：a : idealSet K J。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idealSetEquiv_apply (a : idealSet K J) :
    (idealSetEquiv K J a : mixedSpace K) = a := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv_symm_apply** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：idealSetEquiv_symm_apply (a : {a : integerSet K // (preimageOfMemIntegerSe
t a : 𝓞 K) in (J : Set (𝓞 K)) }) : ((idealSetEquiv K J).symm a : mixedSpace K) =
 a
参数：a : {a : integerSet K // (preimageOfMemIntegerSet a : 𝓞 K) in (J : Set (𝓞 K))
 }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv_apply`：idealSet
Equiv_apply (a : idealSet K J) : (idealSetEquiv K J a : mixedSpace K) = a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem idealSetEquiv_symm_apply
    (a : {a : integerSet K // (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Set (𝓞 K)) }) :
    ((idealSetEquiv K J).symm a : mixedSpace K) = a := by
  rw [← (idealSetEquiv_apply ((idealSetEquiv K J).symm a)), Equiv.apply_symm_apply]
/-
**NumberField.mixedEmbedding.fundamentalCone.intNorm_idealSetEquiv_apply** 是 Mat
hlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：intNorm_idealSetEquiv_apply (a : idealSet K J) : intNorm (idealSetEquiv K 
J a).val = mixedEmbedding.norm (a : mixedSpace K)
参数：a : idealSet K J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.intNorm_coe`：intNorm_coe (a :
 integerSet K) : (intNorm a : Real) = mixedEmbedding.norm (a : mixedSpace K)
· 使用定理 `NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv_apply`：idealSet
Equiv_apply (a : idealSet K J) : (idealSetEquiv K J a : mixedSpace K) = a
-/
theorem intNorm_idealSetEquiv_apply (a : idealSet K J) :
    intNorm (idealSetEquiv K J a).val = mixedEmbedding.norm (a : mixedSpace K) := by
  rw [intNorm_coe, idealSetEquiv_apply]

variable (K J)

set_option backward.isDefEq.respectTransparency false in
/-- For an integer `n`, The equivalence between the elements of `idealSet K` of norm `n` and
the product of the set of nonzero principal ideals of `K` divisible by `J` of norm `n` and the
torsion of `K`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.idealSetEquivNorm** 是 Mathlib 中的一个定
义，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：idealSetEquivNorm (n : Nat) : {a : idealSet K J // mixedEmbedding.norm (a 
: mixedSpace K) = n} ≃ {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipa
l (I : Ideal (𝓞 K)) ∧ absNorm (I : Ideal (𝓞 K)) = n} × (torsion K)
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
For an integer `n`, The equivalence between the elements of `idealSet K` of norm
 `n` and
the product of the set of nonzero principal ideals of `K` divisible by `J` of no
rm `n` and the
torsion of `K`.
-/
def idealSetEquivNorm (n : ℕ) :
    {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = n} ≃
      {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc
    _ ≃ {a : {a : integerSet K // (preimageOfMemIntegerSet a).1 ∈ J.1} //
            mixedEmbedding.norm a.1.1 = n} := by
        convert! (Equiv.subtypeEquivOfSubtype (idealSetEquiv K J).symm).symm using 3
        rw [idealSetEquiv_symm_apply]
    _ ≃ {a : integerSet K // (preimageOfMemIntegerSet a).1 ∈ J.1 ∧
          mixedEmbedding.norm a.1 = n} := Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K ↦ (preimageOfMemIntegerSet a).1 ∈ J.1)
        (fun a ↦ mixedEmbedding.norm a.1 = n)
    _ ≃ {a : {a :integerSet K // mixedEmbedding.norm a.1 = n} //
          (preimageOfMemIntegerSet a.1).1 ∈ J.1} := ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K ↦ mixedEmbedding.norm a.1 = n)
        (fun a ↦ (preimageOfMemIntegerSet a).1 ∈ J.1)).trans
        (Equiv.subtypeEquivRight (fun _ ↦ by simp [and_comm]))).symm
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} × (torsion K) //
          J.1 ∣ I.1.1} := by
      convert! Equiv.subtypeEquivOfSubtype (p := fun I ↦ J.1 ∣ I.1) (integerSetEquivNorm K n)
      rw [integerSetEquivNorm_apply_fst, dvd_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} // J.1 ∣ I.1} ×
        (torsion K) := Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} ↦ J.1 ∣ I.1)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 = n) ∧ J.1 ∣ I.1} × (torsion K) :=
      Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1 ∧ absNorm I.1 = n)
        (fun I ↦ J.1 ∣ I.1))
    _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = n} ×
          (Units.torsion K) :=
      Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeEquivRight fun _ ↦ by rw [and_comm]

/-- For `s : ℝ`, the number of principal nonzero ideals in `𝓞 K` divisible par `J` of norm `≤ s`
multiplied by the order of the torsion of `K` is equal to the number of elements in `idealSet K J`
of norm `≤ s`. -/
/-
**NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_dvd_norm_le** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding.fundamentalCone`。
形式化陈述：card_isPrincipal_dvd_norm_le (s : Real) : Nat.card {I : (Ideal (𝓞 K))⁰ // 
(J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧ absNorm (I : Ideal (𝓞 K)
) <= s} * torsionOrder K = Nat.card {a : idealSet K J // mixedEmbedding.norm (a 
: mixedSpace K) <= s}
参数：s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_floor_iff`：le_floor_iff (ha : 0 <= a) : n <= ⌊a⌋₊ ↔ (n : α) <= a
· 使用定理 `NumberField.Units.torsionOrder.eq_1`：∀ (K : Type u_1) [inst : Field K], 
NumberField.Units.torsionOrder K = Nat.card ↥(NumberField.Units.torsion K)
· 使用定理 `Nat.card_prod`：card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α *
 Nat.card β
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrderBot α] {a x : α}, x ∈ Finset.Iic a ↔ x ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `lt_iff_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a < b 
↔ ¬b ≤ a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `NumberField.mixedEmbedding.norm_nonneg`：∀ {K : Type u_1} [inst : Field K
] [inst_1 : NumberField K] (x : NumberField.mixedEmbedding.mixedSpace K),   0 ≤ 
NumberField.mixedEmbedding.n…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Nat.card_of_isEmpty`：∀ {α : Type u_1} [IsEmpty α], Nat.card α = 0
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
For `s : ℝ`, the number of principal nonzero ideals in `𝓞 K` divisible par `J` o
f norm `≤ s`
multiplied by the order of the torsion of `K` is equal to the number of elements
 in `idealSet K J`
of norm `≤ s`.
-/
theorem card_isPrincipal_dvd_norm_le (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) ≤ s} * torsionOrder K =
        Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  obtain hs | hs := le_or_gt 0 s
  · simp_rw [← intNorm_idealSetEquiv_apply, ← Nat.le_floor_iff hs]
    rw [torsionOrder, ← Nat.card_prod]
    refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
      (fun I ↦ ⟨absNorm I.1.val.1, Finset.mem_Iic.mpr I.1.prop.2.2⟩)
      (fun a ↦ ⟨intNorm (idealSetEquiv K J a.1).1, Finset.mem_Iic.mpr a.prop⟩) fun ⟨i, hi⟩ ↦ ?_
    simp_rw [Subtype.mk.injEq]
    calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // _ ∧ _ ∧ _} // absNorm I.1.1 = i} × torsion K :=
        Equiv.prodSubtypeFstEquivSubtypeProd
      _ ≃ {I : (Ideal (𝓞 K))⁰ // (_ ∧ _ ∧ absNorm I.1 ≤ ⌊s⌋₊) ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
        (p := fun I : (Ideal (𝓞 K))⁰ ↦ J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 ≤ ⌊s⌋₊)
        (q := fun I ↦ absNorm I.1 = i))
      _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeEquivRight fun _ ↦ by grind
      _ ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = i} :=
            (idealSetEquivNorm K J i).symm
      _ ≃ {a : idealSet K J // intNorm (idealSetEquiv K J a).1 = i} := by
        simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]
        rfl
      _ ≃ {b : {a : idealSet K J // intNorm (idealSetEquiv K J a).1 ≤ ⌊s⌋₊} //
            intNorm (idealSetEquiv K J b).1 = i} :=
        (Equiv.subtypeSubtypeEquivSubtype fun h ↦ Finset.mem_Iic.mp (h ▸ hi)).symm
  · simp_rw [lt_iff_not_ge.mp (lt_of_lt_of_le hs (Nat.cast_nonneg _)), lt_iff_not_ge.mp
      (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)), and_false, Nat.card_of_isEmpty,
      zero_mul]

end fundamentalCone

end

end NumberField.mixedEmbedding

