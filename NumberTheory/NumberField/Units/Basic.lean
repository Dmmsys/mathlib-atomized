/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Units of a number field

We prove some basic results on the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K` and its torsion subgroup.

## Main definition

* `NumberField.Units.torsion`: the torsion subgroup of a number field.

## Main results

* `NumberField.isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if
  `|norm ℚ x| = 1`.

* `NumberField.Units.mem_torsion`: a unit `x : (𝓞 K)ˣ` is torsion iff `w x = 1` for all infinite
  places `w` of `K`.

## Tags
number field, units
-/

@[expose] public section

open scoped NumberField

noncomputable section

open NumberField Units

section Rat

set_option backward.isDefEq.respectTransparency false in
/-
**Rat.RingOfIntegers.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.RingOfIntegers.isUnit_iff {x : 𝓞 Rat} : IsUnit x ↔ (x : Rat) = 1 ∨ (x 
: Rat) = -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `isLocalHom_toRingHom`：isLocalHom_toRingHom {F : Type*} [FunLike F R S] [
RingHomClass F R S] (f : F) [IsLocalHom f] : IsLocalHom (f : R ->+* S)
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl

end Rat

variable (K : Type*) [Field K]

section IsUnit

variable {K}

/-
**NumberField.isUnit_iff_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NumberField.isUnit_iff_norm [NumberField K] {x : 𝓞 K} : IsUnit x ↔ |(RingO
fIntegers.norm Rat x : Rat)| = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `abs_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] {a b : α}, |a| = |b| ↔ a = b ∨ a = -b
· 使用定理 `Rat.RingOfIntegers.isUnit_iff`：Rat.RingOfIntegers.isUnit_iff {x : 𝓞 Rat}
 : IsUnit x ↔ (x : Rat) = 1 ∨ (x : Rat) = -1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `RingOfIntegers.isUnit_norm`：isUnit_norm [CharZero K] {x : 𝓞 F} : IsUnit 
(norm K x) ↔ IsUnit x
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
-/
theorem NumberField.isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert! (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]

end IsUnit

namespace NumberField.Units

section coe

/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeHTC (𝓞 K)ˣ K :=
  ⟨fun x => algebraMap _ K (Units.val x)⟩
/-
**NumberField.Units.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ -> K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
-/
theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  RingOfIntegers.coe_injective.comp Units.val_injective

variable {K}
/-
**NumberField.Units.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_coe (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) = (u : K)
参数：u : (𝓞 K)ˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) = (u : K) := rfl
/-
**NumberField.Units._root_.IsPrimitiveRoot.coe_coe_iff** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsPrimitiveRoot.coe_coe_iff {ν : (𝓞 K)ˣ} {n : ℕ} :
    IsPrimitiveRoot (ν : K) n ↔ IsPrimitiveRoot ν n :=
  IsPrimitiveRoot.map_iff_of_injective
    (f := (algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))) (coe_injective K)
/-
**NumberField.Units.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_mul (x y : (𝓞 K)ˣ) : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K)
参数：x y : (𝓞 K)ˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : (𝓞 K)ˣ) : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K) := rfl
/-
**NumberField.Units.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_pow (x : (𝓞 K)ˣ) (n : Nat) : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n
参数：x : (𝓞 K)ˣ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
-/
theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n := by
  rw [← map_pow, ← val_pow_eq_pow_val]
/-
**NumberField.Units.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_zpow (x : (𝓞 K)ˣ) (n : Int) : (↑(x ^ n) : K) = (x : K) ^ n
参数：x : (𝓞 K)ˣ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : (↑(x ^ n) : K) = (x : K) ^ n := by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n
/-
**NumberField.Units.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl
/-
**NumberField.Units.coe_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_neg_one : ((-1 : (𝓞 K)ˣ) : K) = (-1 : K)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg_one : ((-1 : (𝓞 K)ˣ) : K) = (-1 : K) := rfl
/-
**NumberField.Units.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) != 0
参数：x : (𝓞 K)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
-/
theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

end coe

variable {K}

/--
The group homomorphism `(𝓞 K)ˣ →* ℂˣ` induced by a complex embedding of `K`.
-/
/-
**NumberField.Units.complexEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Unit
s`。
形式化陈述：{K : Type u_1} → [inst : Field K] → (K →+* ℂ) → (NumberField.RingOfInteger
s K)ˣ →* ℂˣ
参数：K →+* ℂ；NumberField.RingOfIntegers K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism `(𝓞 K)ˣ →* ℂˣ` induced by a complex embedding of `K`.
-/
protected def complexEmbedding (φ : K →+* ℂ) : (𝓞 K)ˣ →* ℂˣ :=
  (map φ).comp (map (algebraMap (𝓞 K) K).toMonoidHom)

@[simp]
/-
**NumberField.Units.complexEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `NumberFiel
d.Units`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (φ : K →+* ℂ) (u : (NumberField.RingOfIn
tegers K)ˣ),   ↑((NumberField.Units.complexEmbedding φ) u) = φ ((algebraMap (Num
berField.RingOfIntegers K) K) ↑u)
参数：φ : K →+* ℂ；u : (NumberField.RingOfIntegers K)ˣ；(NumberField.Units.complexEmb
edding φ) u；(algebraMap (NumberField.RingOfIntegers K) K) ↑u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem complexEmbedding_apply (φ : K →+* ℂ) (u : (𝓞 K)ˣ) :
    Units.complexEmbedding φ u = φ u := rfl
/-
**NumberField.Units.complexEmbedding_injective** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.Units`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (φ : K →+* ℂ), Function.Injective ⇑(Numb
erField.Units.complexEmbedding φ)
参数：φ : K →+* ℂ；NumberField.Units.complexEmbedding φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Units.map_injective`：map_injective {f : M ->* N} (hf : Function.Injectiv
e f) : Function.Injective (map f)
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)
-/
protected theorem complexEmbedding_injective (φ : K →+* ℂ) :
    Function.Injective (Units.complexEmbedding φ) :=
  (map_injective φ.injective).comp (map_injective RingOfIntegers.coe_injective)

@[simp]
/-
**NumberField.Units.complexEmbedding_inj** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
Units`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] (φ : K →+* ℂ) (u v : (NumberField.RingOf
Integers K)ˣ),   (NumberField.Units.complexEmbedding φ) u = (NumberField.Units.c
omplexEmbedding φ) v ↔ u = v
参数：φ : K →+* ℂ；u v : (NumberField.RingOfIntegers K)ˣ；NumberField.Units.complexEm
bedding φ；NumberField.Units.complexEmbedding φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `NumberField.Units.complexEmbedding_injective`：∀ {K : Type u_1} [inst : F
ield K] (φ : K →+* ℂ), Function.Injective ⇑(NumberField.Units.complexEmbedding φ
)
-/
protected theorem complexEmbedding_inj (φ : K →+* ℂ) (u v : (𝓞 K)ˣ) :
    Units.complexEmbedding φ u = Units.complexEmbedding φ v ↔ u = v :=
  (Units.complexEmbedding_injective φ).eq_iff

open NumberField.InfinitePlace

variable (K)

@[simp]
/-
**NumberField.Units.norm** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (x : (NumberFie
ld.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraMap (NumberField.RingOfInte
gers K) K) ↑x)| = 1
参数：K : Type u_1；x : (NumberField.RingOfIntegers K)ˣ；Algebra.norm ℚ；(algebraMap (
NumberField.RingOfIntegers K) K) ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingOfIntegers.coe_norm`：∀ {L : Type u_1} (K : Type u_2) [inst : Field K
] [inst_1 : Field L] [inst_2 : Algebra K L]   (x : NumberField.RingOfIntegers L)
, ↑((RingOfIn…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.isUnit_iff_norm`：NumberField.isUnit_iff_norm [NumberField K]
 {x : 𝓞 K} : IsUnit x ↔ |(RingOfIntegers.norm Rat x : Rat)| = 1
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
protected theorem norm [NumberField K] (x : (𝓞 K)ˣ) :
    |Algebra.norm ℚ (x : K)| = 1 := by
  rw [← RingOfIntegers.coe_norm, isUnit_iff_norm.mp x.isUnit]

variable {K} in
/-
**NumberField.Units.pos_at_place** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：pos_at_place (x : (𝓞 K)ˣ) (w : InfinitePlace K) : 0 < w x
参数：x : (𝓞 K)ˣ；w : InfinitePlace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.pos_iff`：pos_iff {w : InfinitePlace K} {x : K}
 : 0 < w x ↔ x != 0
· 使用定理 `NumberField.Units.coe_ne_zero`：coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) != 0
-/
theorem pos_at_place (x : (𝓞 K)ˣ) (w : InfinitePlace K) :
    0 < w x := pos_iff.mpr (coe_ne_zero x)

variable {K} in
/-
**NumberField.Units.sum_mult_mul_log** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Unit
s`。
形式化陈述：sum_mult_mul_log [NumberField K] (x : (𝓞 K)ˣ) : ∑ w : InfinitePlace K, w.m
ult * Real.log (w x) = 0
参数：x : (𝓞 K)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.log_prod`：log_prod {α : Type*} {s : Finset α} {f : α -> Real} (hf :
 forall x in s, f x != 0) : log (∏ i in s, f i) = ∑ i in s, log (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `NumberField.InfinitePlace.instMonoidWithZeroHomClassReal`：∀ {K : Type u_
1} [inst : Field K], MonoidWithZeroHomClass (NumberField.InfinitePlace K) K ℝ
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_2`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `NumberField.Units.norm`：∀ (K : Type u_1) [inst : Field K] [inst_1 : Numb
erField K] (x : (NumberField.RingOfIntegers K)ˣ),   |(Algebra.norm ℚ) ((algebraM
ap (NumberFi…
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.prod_eq_abs_norm`：prod_eq_abs_norm (x : K) : ∏
 w : InfinitePlace K, w x ^ mult w = abs (Algebra.norm Rat x)
-/
theorem sum_mult_mul_log [NumberField K] (x : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, w.mult * Real.log (w x) = 0 := by
  simpa [Units.norm, Real.log_prod, Real.log_pow] using
    congr_arg Real.log (prod_eq_abs_norm (x : K))

section torsion

/-- The torsion subgroup of the group of units. -/
/-
**NumberField.Units.torsion** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Units`。
形式化陈述：torsion : Subgroup (𝓞 K)ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The torsion subgroup of the group of units.
-/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (torsion K) := One.instNonempty

variable [NumberField K]
/-
**NumberField.Units.mem_torsion** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Units`。
形式化陈述：mem_torsion {x : (𝓞 K)ˣ} : x in torsion K ↔ forall w : InfinitePlace K, w 
x = 1
参数：𝓞 K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.eq_iff_eq`：eq_iff_eq (x : K) (r : Real) : (for
all w : InfinitePlace K, w x = r) ↔ forall φ : K ->+* Complex, ‖φ x‖ = r
· 使用定理 `NumberField.Units.torsion.eq_1`：∀ (K : Type u_1) [inst : Field K], Numbe
rField.Units.torsion K = CommGroup.torsion (NumberField.RingOfIntegers K)ˣ
· 使用定理 `CommGroup.mem_torsion`：mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrd
er g
· 使用定理 `IsOfFinOrder.norm_eq_one`：∀ {α : Type u_1} [inst : NormedRing α] [NormMu
lClass α] [NormOneClass α] {a : α}, IsOfFinOrder a → ‖a‖ = 1
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `MonoidHom.isOfFinOrder`：MonoidHom.isOfFinOrder [Monoid H] (f : G ->* H) 
{x : G} (h : IsOfFinOrder x) : IsOfFinOrder f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`：pow_eq_one_of_norm_eq_
one {x : K} (hxi : IsIntegral Int x) (hx : forall φ : K ->+* A, ‖φ x‖ = 1) : exi
sts (n : Nat) (_ : 0 < n), x ^ n = 1
· 使用定理 `NumberField.RingOfIntegers.isIntegral_coe`：isIntegral_coe (x : 𝓞 K) : Is
Integral Int (algebraMap _ K x)
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `NumberField.RingOfIntegers.ext`：∀ {K : Type u_1} [inst : Field K] {x y :
 NumberField.RingOfIntegers K}, ↑x = ↑y → x = y
· 使用引理 `NumberField.RingOfIntegers.coe_eq_algebraMap`：coe_eq_algebraMap (x : 𝓞 K
) : (x : K) = algebraMap _ _ x
· 使用定理 `NumberField.Units.coe_pow`：coe_pow (x : (𝓞 K)ˣ) (n : Nat) : ((x ^ n : (𝓞
 K)ˣ) : K) = (x : K) ^ n
· 使用定理 `NumberField.Units.coe_one`：coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K)
-/
theorem mem_torsion {x : (𝓞 K)ˣ} :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion]
  refine ⟨fun hx φ ↦ (((φ.comp <| algebraMap (𝓞 K) K).toMonoidHom.comp <|
    Units.coeHom _).isOfFinOrder hx).norm_eq_one, fun h ↦ isOfFinOrder_iff_pow_eq_one.2 ?_⟩
  obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.isIntegral_coe h
  exact ⟨n, hn, by ext; rw [NumberField.RingOfIntegers.coe_eq_algebraMap, coe_pow, hx,
    NumberField.RingOfIntegers.coe_eq_algebraMap, coe_one]⟩

/-- The torsion subgroup is finite. -/
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The torsion subgroup is finite.
-/
instance : Finite (torsion K) := by
  refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

/-- The torsion subgroup is cyclic. -/
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The torsion subgroup is cyclic.
-/
instance : IsCyclic (torsion K) := isCyclic_subgroup_units _

/-- The order of the torsion subgroup. -/
/-
**NumberField.Units.torsionOrder** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.Units`。
形式化陈述：torsionOrder : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order of the torsion subgroup.
-/
def torsionOrder : ℕ := Nat.card (torsion K)
/-
**NumberField.Units.torsionOrder_pos** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Unit
s`。
形式化陈述：torsionOrder_pos : 0 < torsionOrder K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `NumberField.Units.instNonemptySubtypeUnitsRingOfIntegersMemSubgroupTorsi
on`：∀ (K : Type u_1) [inst : Field K], Nonempty ↥(NumberField.Units.torsion K)
· 使用定理 `NumberField.Units.instFiniteSubtypeUnitsRingOfIntegersMemSubgroupTorsion
`：∀ (K : Type u_1) [inst : Field K] [NumberField K], Finite ↥(NumberField.Units.
torsion K)
-/
theorem torsionOrder_pos : 0 < torsionOrder K :=
  Nat.card_pos
/-
**NumberField.Units.torsionOrder_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.
Units`。
形式化陈述：torsionOrder_ne_zero : torsionOrder K != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NumberField.Units.torsionOrder_pos`：torsionOrder_pos : 0 < torsionOrder 
K
-/
theorem torsionOrder_ne_zero : torsionOrder K ≠ 0 :=
  (torsionOrder_pos K).ne'
/-
**NumberField.Units.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.Units`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NeZero (torsionOrder K) :=
  ⟨torsionOrder_ne_zero K⟩

omit [NumberField K] in
/-- If `k` does not divide `torsionOrder` then there are no nontrivial roots of unity of
  order dividing `k`. -/
/-
**NumberField.Units.rootsOfUnity_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.U
nits`。
形式化陈述：rootsOfUnity_eq_one {k : Nat+} (hc : Nat.Coprime k (torsionOrder K)) {ζ : 
(𝓞 K)ˣ} : ζ in rootsOfUnity k (𝓞 K) ↔ ζ = 1
参数：hc : Nat.Coprime k (torsionOrder K)；𝓞 K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_rootsOfUnity`：mem_rootsOfUnity (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnit
y k M ↔ ζ ^ k = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `Nat.eq_one_of_dvd_coprimes`：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_c
oprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `NumberField.Units.torsion.eq_1`：∀ (K : Type u_1) [inst : Field K], Numbe
rField.Units.torsion K = CommGroup.torsion (NumberField.RingOfIntegers K)ˣ
· 使用定理 `CommGroup.mem_torsion`：mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrd
er g
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `orderOf_submonoid`：orderOf_submonoid {H : Submonoid G} (y : H) : orderOf
 (y : G) = orderOf y
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a

--- 原说明 ---
If `k` does not divide `torsionOrder` then there are no nontrivial roots of unit
y of
  order dividing `k`.
-/
theorem rootsOfUnity_eq_one {k : ℕ+} (hc : Nat.Coprime k (torsionOrder K))
    {ζ : (𝓞 K)ˣ} : ζ ∈ rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ, hζ⟩ : torsion K)]
    apply orderOf_dvd_natCard

/-- The group of roots of unity of order dividing `torsionOrder` is equal to the torsion
group. -/
/-
**NumberField.Units.rootsOfUnity_eq_torsion** 是 Mathlib 中的一个定理，位于命名空间 `NumberFie
ld.Units`。
形式化陈述：rootsOfUnity_eq_torsion : rootsOfUnity (torsionOrder K) (𝓞 K) = torsion K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Units.torsion.eq_1`：∀ (K : Type u_1) [inst : Field K], Numbe
rField.Units.torsion K = CommGroup.torsion (NumberField.RingOfIntegers K)ˣ
· 使用定理 `mem_rootsOfUnity`：mem_rootsOfUnity (k : Nat) (ζ : Mˣ) : ζ in rootsOfUnit
y k M ↔ ζ ^ k = 1
· 使用定理 `CommGroup.mem_torsion`：mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrd
er g
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `NumberField.Units.torsionOrder_pos`：torsionOrder_pos : 0 < torsionOrder 
K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1

--- 原说明 ---
The group of roots of unity of order dividing `torsionOrder` is equal to the tor
sion
group.
-/
theorem rootsOfUnity_eq_torsion :
    rootsOfUnity (torsionOrder K) (𝓞 K) = torsion K := by
  ext ζ
  rw [torsion, mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨torsionOrder K, torsionOrder_pos K, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one' (torsion K) _ ⟨ζ, h⟩)

/--
The image of `torsion K` by a complex embedding is the group of complex roots of unity of
order `torsionOrder K`.
-/
/-
**NumberField.Units.map_complexEmbedding_torsion** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.Units`。
形式化陈述：map_complexEmbedding_torsion (φ : K ->+* Complex) : (torsion K).map (Units
.complexEmbedding φ) = rootsOfUnity (torsionOrder K) Complex
参数：φ : K ->+* Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.eq_of_le_of_card_ge`：eq_of_le_of_card_ge {H K : Subgroup G} [Fi
nite K] (hle : H <= K) (hcard : Nat.card K <= Nat.card H) : H = K
· 使用定理 `instFiniteSubtypeUnitsMemSubgroupRootsOfUnity`：∀ (R : Type u_4) (k : ℕ) 
[NeZero k] [inst : CommRing R] [IsDomain R], Finite ↥(rootsOfUnity k R)
· 使用定理 `NumberField.Units.instNeZeroNatTorsionOrder`：∀ (K : Type u_1) [inst : Fi
eld K] [NumberField K], NeZero (NumberField.Units.torsionOrder K)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.rootsOfUnity_eq_torsion`：rootsOfUnity_eq_torsion : roo
tsOfUnity (torsionOrder K) (𝓞 K) = torsion K
· 使用定理 `map_rootsOfUnity`：map_rootsOfUnity (f : Mˣ ->* Nˣ) (k : Nat) : (rootsOfU
nity k M).map f <= rootsOfUnity k N
· 使用定理 `NumberField.Units.complexEmbedding_injective`：∀ {K : Type u_1} [inst : F
ield K] (φ : K →+* ℂ), Function.Injective ⇑(NumberField.Units.complexEmbedding φ
)
· 使用定理 `Complex.card_rootsOfUnity`：card_rootsOfUnity (n : Nat) [NeZero n] : Nat.
card (rootsOfUnity n Complex) = n
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `NumberField.Units.torsionOrder.eq_1`：∀ (K : Type u_1) [inst : Field K], 
NumberField.Units.torsionOrder K = Nat.card ↥(NumberField.Units.torsion K)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The image of `torsion K` by a complex embedding is the group of complex roots of
 unity of
order `torsionOrder K`.
-/
theorem map_complexEmbedding_torsion (φ : K →+* ℂ) :
    (torsion K).map (Units.complexEmbedding φ) = rootsOfUnity (torsionOrder K) ℂ := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [← rootsOfUnity_eq_torsion]
    exact map_rootsOfUnity _ (torsionOrder K)
  · let e := ((torsion K).equivMapOfInjective (Units.complexEmbedding φ)
      (Units.complexEmbedding_injective φ)).symm.toEquiv
    rw [Complex.card_rootsOfUnity, Nat.card_congr e, torsionOrder]
/-
**NumberField.Units.even_torsionOrder** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.Uni
ts`。
形式化陈述：even_torsionOrder : Even (torsionOrder K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_one_mem_torsion`：neg_one_mem_torsion : -1 in CommMonoid.torsion M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.orderOf_coe`：orderOf_coe (a : H) : orderOf (a : G) = orderOf a
· 使用定理 `orderOf_units`：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
· 使用定理 `Units.val_neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg 
α] (u : αˣ), ↑(-u) = -↑u
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `orderOf_neg_one`：orderOf_neg_one {R} [Ring R] [Nontrivial R] : orderOf (
-1 : R) = if ringChar R = 2 then 1 else 2
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用引理 `ringChar.eq_zero`：eq_zero [CharZero R] : ringChar R = 0
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
theorem even_torsionOrder :
    Even (torsionOrder K) := by
  suffices orderOf (⟨-1, neg_one_mem_torsion⟩ : torsion K) = 2 by
    rw [even_iff_two_dvd, ← this]
    apply orderOf_dvd_natCard
  rw [← Subgroup.orderOf_coe, ← orderOf_units, Units.val_neg, val_one, orderOf_neg_one,
    ringChar.eq_zero, if_neg (by decide)]

section odd

variable {K}

set_option backward.isDefEq.respectTransparency false in
/-
**NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.Units`。
形式化陈述：torsion_eq_one_or_neg_one_of_odd_finrank (h : Odd (Module.finrank Rat K)) 
(x : torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1
参数：h : Odd (Module.finrank Rat K)；x : torsion K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
· 使用定理 `Mathlib.Tactic.Linarith.lt_of_lt_of_eq`：lt_of_lt_of_eq {a b : α} (ha : a
 < 0) (hb : b = 0) : a + b < 0
（共 69 条，此处仅展示前 30 条）
-/
theorem torsion_eq_one_or_neg_one_of_odd_finrank
    (h : Odd (Module.finrank ℚ K)) (x : torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : K)),
        NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank h]
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]
/-
**NumberField.Units.torsionOrder_eq_two_of_odd_finrank** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.Units`。
形式化陈述：torsionOrder_eq_two_of_odd_finrank (h : Odd (Module.finrank Rat K)) : tors
ionOrder K = 2
参数：h : Odd (Module.finrank Rat K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.Units.instFiniteSubtypeUnitsRingOfIntegersMemSubgroupTorsion
`：∀ (K : Type u_1) [inst : Field K] [NumberField K], Finite ↥(NumberField.Units.
torsion K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.Units.torsionOrder.eq_1`：∀ (K : Type u_1) [inst : Field K], 
NumberField.Units.torsionOrder K = Nat.card ↥(NumberField.Units.torsion K)
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_eq_two`：card_eq_two : #s = 2 ↔ exists x y, x != y ∧ s = {x, 
y}
· 使用定理 `neg_one_mem_torsion`：neg_one_mem_torsion : -1 in CommMonoid.torsion M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
· 使用定理 `NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank`：torsion_eq_o
ne_or_neg_one_of_odd_finrank (h : Odd (Module.finrank Rat K)) (x : torsion K) : 
(x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem torsionOrder_eq_two_of_odd_finrank (h : Odd (Module.finrank ℚ K)) :
    torsionOrder K = 2 := by
  classical
  let := Fintype.ofFinite (torsion K)
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact torsion_eq_one_or_neg_one_of_odd_finrank h x

end odd

end torsion

end Units

end NumberField

