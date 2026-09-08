/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/

@[expose] public section

open Set

universe u v w

namespace Valuation

section Ring

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)

/-- The ring of integers under a given valuation is the subring of elements with valuation ≤ 1. -/
/-
**Valuation.integer** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：integer : Subring R where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of integers under a given valuation is the subring of elements with val
uation ≤ 1.
-/
def integer : Subring R where
  carrier := { x | v x ≤ 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_ofPred_eq, map_mul, mul_le_one' hx hy]
  zero_mem' := by simp
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_ofPred_eq] at hx; simpa only [Set.mem_ofPred_eq, map_neg]
/-
**Valuation.mem_integer_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_integer_iff (r : R) : r in v.integer ↔ v r <= 1
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_integer_iff (r : R) : r ∈ v.integer ↔ v r ≤ 1 := by rfl

end Ring

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)
variable (O : Type w) [CommRing O] [Algebra O R]

/-- Given a valuation v : R → Γ₀ and a ring homomorphism O →+* R, we say that O is the integers of v
if f is injective, and its range is exactly `v.integer`. -/
/-
**Valuation.Integers** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{R : Type u} →   {Γ₀ : Type v} →     [inst : CommRing R] →       [inst_1 :
 LinearOrderedCommGroupWithZero Γ₀] →         Valuation R Γ₀ → (O : Type w) → [i
nst_2 : CommRing O] → [Algebra O R] → Prop
参数：O : Type w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a valuation v : R → Γ₀ and a ring homomorphism O →+* R, we say that O is t
he integers of v
if f is injective, and its range is exactly `v.integer`.
-/
structure Integers : Prop where
  hom_inj : Function.Injective (algebraMap O R)
  map_le_one : ∀ x, v (algebraMap O R x) ≤ 1
  exists_of_le_one : ∀ ⦃r⦄, v r ≤ 1 → ∃ x, algebraMap O R x = r

-- typeclass shortcut
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra v.integer R :=
  inferInstance
/-
**Valuation.integer.integers** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.integer`。
形式化陈述：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRing R] [inst_1 : LinearOrderedCo
mmGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Integers ↥v.integer
参数：v : Valuation R Γ₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem integer.integers : v.Integers v.integer :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun r => r.2
    exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }

namespace Integers

variable {v O}

/-
**Valuation.Integers.one_of_isUnit'** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integer
s`。
形式化陈述：one_of_isUnit' {x : O} (hx : IsUnit x) (H : forall x, v (algebraMap O R x)
 <= 1) : v (algebraMap O R x) = 1
参数：hx : IsUnit x；H : forall x, v (algebraMap O R x) <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem one_of_isUnit' {x : O} (hx : IsUnit x) (H : ∀ x, v (algebraMap O R x) ≤ 1) :
    v (algebraMap O R x) = 1 :=
  let ⟨u, hu⟩ := hx
  le_antisymm (H _) <| by
    grw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul, H (u⁻¹ : Units O)]
/-
**Valuation.Integers.one_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integers
`。
形式化陈述：one_of_isUnit (hv : Integers v O) {x : O} (hx : IsUnit x) : v (algebraMap 
O R x) = 1
参数：hv : Integers v O；hx : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.one_of_isUnit'`：one_of_isUnit' {x : O} (hx : IsUnit x
) (H : forall x, v (algebraMap O R x) <= 1) : v (algebraMap O R x) = 1
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
-/
theorem one_of_isUnit (hv : Integers v O) {x : O} (hx : IsUnit x) : v (algebraMap O R x) = 1 :=
  one_of_isUnit' hx hv.map_le_one

/--
Let `O` be the integers of the valuation `v` on some commutative ring `R`. For every element `x` in
`O`, `x` is a unit in `O` if and only if the image of `x` in `R` is a unit and has valuation 1.
-/
/-
**Valuation.Integers.isUnit_of_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integers
`。
形式化陈述：isUnit_of_one (hv : Integers v O) {x : O} (hx : IsUnit (algebraMap O R x))
 (hvx : v (algebraMap O R x) = 1) : IsUnit x
参数：hv : Integers v O；hx : IsUnit (algebraMap O R x)；hvx : v (algebraMap O R x) =
 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Valuation.Integers.exists_of_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst 
: CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} 
  {O : Type w} [inst_2 : …
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
Let `O` be the integers of the valuation `v` on some commutative ring `R`. For e
very element `x` in
`O`, `x` is a unit in `O` if and only if the image of `x` in `R` is a unit and h
as valuation 1.
-/
theorem isUnit_of_one (hv : Integers v O) {x : O} (hx : IsUnit (algebraMap O R x))
    (hvx : v (algebraMap O R x) = 1) : IsUnit x :=
  let ⟨u, hu⟩ := hx
  have h1 : v u ≤ 1 := hu.symm ▸ hv.2 x
  have h2 : v (u⁻¹ : Rˣ) ≤ 1 := by
    rw [← one_mul (v _), ← hvx, ← v.map_mul, ← hu, u.mul_inv, hu, hvx, v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1
  let ⟨r2, hr2⟩ := hv.3 h2
  ⟨⟨r1, r2, hv.1 <| by rw [map_mul, map_one, hr1, hr2, Units.mul_inv],
      hv.1 <| by rw [map_mul, map_one, hr1, hr2, Units.inv_mul]⟩,
    hv.1 <| hr1.trans hu⟩
/-
**Valuation.Integers.le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integers`。
形式化陈述：le_of_dvd (hv : Integers v O) {x y : O} (h : x ∣ y) : v (algebraMap O R y)
 <= v (algebraMap O R x)
参数：hv : Integers v O；h : x ∣ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
-/
theorem le_of_dvd (hv : Integers v O) {x y : O} (h : x ∣ y) :
    v (algebraMap O R y) ≤ v (algebraMap O R x) := by
  obtain ⟨z, rfl⟩ := h
  grw [← mul_one (v (algebraMap O R x)), map_mul, v.map_mul, hv.2 z]
/-
**Valuation.Integers.nontrivial_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.Integer
s`。
形式化陈述：nontrivial_iff (hv : v.Integers O) : Nontrivial O ↔ Nontrivial R
参数：hv : v.Integers O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `Valuation.Integers.exists_of_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst 
: CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} 
  {O : Type w} [inst_2 : …
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
lemma nontrivial_iff (hv : v.Integers O) : Nontrivial O ↔ Nontrivial R := by
  constructor <;> intro h
  · exact hv.hom_inj.nontrivial
  · obtain ⟨o0, ho0⟩ := hv.exists_of_le_one (r := 0) (by simp)
    obtain ⟨o1, ho1⟩ := hv.exists_of_le_one (r := 1) (by simp)
    refine ⟨o0, o1, ?_⟩
    rintro rfl
    simp [ho1] at ho0

end Integers

/-
**Valuation.IsTrivialOn.of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsTrivial
On`。
形式化陈述：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRing R] [inst_1 : LinearOrderedCo
mmGroupWithZero Γ₀] {k : Type u_1}   [inst_2 : Field k] [inst_3 : Algebra k R] (
v : Valuation R Γ₀),   (∀ (x : k), v ((algebraMap k R) x) ≤ 1) → Valuation.IsTri
vialOn k v
参数：v : Valuation R Γ₀；∀ (x : k), v ((algebraMap k R) x) ≤ 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.one_of_isUnit'`：one_of_isUnit' {x : O} (hx : IsUnit x
) (H : forall x, v (algebraMap O R x) <= 1) : v (algebraMap O R x) = 1
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
-/
theorem IsTrivialOn.of_le_one {k : Type*} [Field k] [Algebra k R] (v : Valuation R Γ₀)
    (hle : ∀ (x : k), v (algebraMap k R x) ≤ 1) : v.IsTrivialOn k where
  eq_one a ha := Valuation.Integers.one_of_isUnit' (IsUnit.mk0 a ha) hle
/-
**Valuation.integers_nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：integers_nontrivial (v : Valuation R Γ₀) : Nontrivial v.integer ↔ Nontrivi
al R
参数：v : Valuation R Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.Integers.nontrivial_iff`：nontrivial_iff (hv : v.Integers O) : 
Nontrivial O ↔ Nontrivial R
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
lemma integers_nontrivial (v : Valuation R Γ₀) :
    Nontrivial v.integer ↔ Nontrivial R :=
  (Valuation.integer.integers v).nontrivial_iff

end CommRing

section Field

variable {F : Type u} {Γ₀ : Type v} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {O : Type w} [CommRing O] [Algebra O F]

namespace Integers

/-
**Valuation.Integers.dvd_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integers`。
形式化陈述：dvd_of_le (hv : Integers v O) {x y : O} (h : v (algebraMap O F x) <= v (al
gebraMap O F y)) : y ∣ x
参数：hv : Integers v O；h : v (algebraMap O F x) <= v (algebraMap O F y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Valuation.Integers.exists_of_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst 
: CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} 
  {O : Type w} [inst_2 : …
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
-/
theorem dvd_of_le (hv : Integers v O) {x y : O}
    (h : v (algebraMap O F x) ≤ v (algebraMap O F y)) : y ∣ x :=
  by_cases
    (fun hy : algebraMap O F y = 0 =>
      have hx : x = 0 :=
        hv.1 <|
          (algebraMap O F).map_zero.symm ▸ (v.zero_iff.1 <| le_zero_iff.1 (v.map_zero ▸ hy ▸ h))
      hx.symm ▸ dvd_zero y)
    fun hy : algebraMap O F y ≠ 0 =>
    have : v ((algebraMap O F y)⁻¹ * algebraMap O F x) ≤ 1 := by
      grw [← v.map_one, ← inv_mul_cancel₀ hy, v.map_mul, v.map_mul, h]
    let ⟨z, hz⟩ := hv.3 this
    ⟨z, hv.1 <| ((algebraMap O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩
/-
**Valuation.Integers.dvd_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integers`。
形式化陈述：dvd_iff_le (hv : Integers v O) {x y : O} : x ∣ y ↔ v (algebraMap O F y) <=
 v (algebraMap O F x)
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.le_of_dvd`：le_of_dvd (hv : Integers v O) {x y : O} (h
 : x ∣ y) : v (algebraMap O R y) <= v (algebraMap O R x)
· 使用定理 `Valuation.Integers.dvd_of_le`：dvd_of_le (hv : Integers v O) {x y : O} (h
 : v (algebraMap O F x) <= v (algebraMap O F y)) : y ∣ x
-/
theorem dvd_iff_le (hv : Integers v O) {x y : O} :
    x ∣ y ↔ v (algebraMap O F y) ≤ v (algebraMap O F x) :=
  ⟨hv.le_of_dvd, hv.dvd_of_le⟩
/-
**Valuation.Integers.le_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integers`。
形式化陈述：le_iff_dvd (hv : Integers v O) {x y : O} : v (algebraMap O F x) <= v (alge
braMap O F y) ↔ y ∣ x
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.dvd_of_le`：dvd_of_le (hv : Integers v O) {x y : O} (h
 : v (algebraMap O F x) <= v (algebraMap O F y)) : y ∣ x
· 使用定理 `Valuation.Integers.le_of_dvd`：le_of_dvd (hv : Integers v O) {x y : O} (h
 : x ∣ y) : v (algebraMap O R y) <= v (algebraMap O R x)
-/
theorem le_iff_dvd (hv : Integers v O) {x y : O} :
    v (algebraMap O F x) ≤ v (algebraMap O F y) ↔ y ∣ x :=
  ⟨hv.dvd_of_le, hv.le_of_dvd⟩

/--
This is the special case of `Valuation.Integers.isUnit_of_one` when the valuation is defined
over a field. Let `v` be a valuation on some field `F` and `O` be its integers. For every element
`x` in `O`, `x` is a unit in `O` if and only if the image of `x` in `F` has valuation 1.
-/
/-
**Valuation.Integers.isUnit_of_one'** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Integer
s`。
形式化陈述：isUnit_of_one' (hv : Integers v O) {x : O} (hvx : v (algebraMap O F x) = 1
) : IsUnit x
参数：hv : Integers v O；hvx : v (algebraMap O F x) = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.isUnit_of_one`：isUnit_of_one (hv : Integers v O) {x :
 O} (hx : IsUnit (algebraMap O R x)) (hvx : v (algebraMap O R x) = 1) : IsUnit x
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
This is the special case of `Valuation.Integers.isUnit_of_one` when the valuatio
n is defined
over a field. Let `v` be a valuation on some field `F` and `O` be its integers. 
For every element
`x` in `O`, `x` is a unit in `O` if and only if the image of `x` in `F` has valu
ation 1.
-/
theorem isUnit_of_one' (hv : Integers v O) {x : O} (hvx : v (algebraMap O F x) = 1) : IsUnit x := by
  refine isUnit_of_one hv (IsUnit.mk0 _ ?_) hvx
  simp only [← v.ne_zero_iff, hvx, ne_eq, one_ne_zero, not_false_eq_true]
/-
**Valuation.Integers.isUnit_iff_valuation_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Valu
ation.Integers`。
形式化陈述：isUnit_iff_valuation_eq_one (hv : Integers v O) {x : O} : IsUnit x ↔ v (al
gebraMap O F x) = 1
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.Integers.one_of_isUnit`：one_of_isUnit (hv : Integers v O) {x :
 O} (hx : IsUnit x) : v (algebraMap O R x) = 1
· 使用定理 `Valuation.Integers.isUnit_of_one'`：isUnit_of_one' (hv : Integers v O) {x
 : O} (hvx : v (algebraMap O F x) = 1) : IsUnit x
-/
lemma isUnit_iff_valuation_eq_one (hv : Integers v O) {x : O} :
    IsUnit x ↔ v (algebraMap O F x) = 1 :=
  ⟨hv.one_of_isUnit, hv.isUnit_of_one'⟩
/-
**Valuation.Integers.valuation_irreducible_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Val
uation.Integers`。
形式化陈述：valuation_irreducible_lt_one (hv : Integers v O) {ϖ : O} (h : Irreducible 
ϖ) : v (algebraMap O F ϖ) < 1
参数：hv : Integers v O；h : Irreducible ϖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
-/
lemma valuation_irreducible_lt_one (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) :
    v (algebraMap O F ϖ) < 1 :=
  lt_of_le_of_ne (hv.map_le_one ϖ) (mt hv.isUnit_iff_valuation_eq_one.mpr h.not_isUnit)
/-
**Valuation.Integers.valuation_unit** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.Integer
s`。
形式化陈述：valuation_unit (hv : Integers v O) (x : Oˣ) : v (algebraMap O F x) = 1
参数：hv : Integers v O；x : Oˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
-/
lemma valuation_unit (hv : Integers v O) (x : Oˣ) :
    v (algebraMap O F x) = 1 := by
  simp [← hv.isUnit_iff_valuation_eq_one]
/-
**Valuation.Integers.valuation_pos_iff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuat
ion.Integers`。
形式化陈述：valuation_pos_iff_ne_zero (hv : Integers v O) {x : O} : 0 < v (algebraMap 
O F x) ↔ x != 0
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma valuation_pos_iff_ne_zero (hv : Integers v O) {x : O} :
    0 < v (algebraMap O F x) ↔ x ≠ 0 := by
  rw [← not_le]
  refine not_congr ?_
  simp [map_eq_zero_iff _ hv.hom_inj]
/-
**Valuation.Integers.valuation_irreducible_pos** 是 Mathlib 中的一个引理，位于命名空间 `Valuat
ion.Integers`。
形式化陈述：valuation_irreducible_pos (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) 
: 0 < v (algebraMap O F ϖ)
参数：hv : Integers v O；h : Irreducible ϖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.Integers.valuation_pos_iff_ne_zero`：valuation_pos_iff_ne_zero 
(hv : Integers v O) {x : O} : 0 < v (algebraMap O F x) ↔ x != 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
-/
lemma valuation_irreducible_pos (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) :
    0 < v (algebraMap O F ϖ) :=
  hv.valuation_pos_iff_ne_zero.mpr h.ne_zero
/-
**Valuation.Integers.dvdNotUnit_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Inte
gers`。
形式化陈述：dvdNotUnit_iff_lt (hv : Integers v O) {x y : O} : DvdNotUnit x y ↔ v (alge
braMap O F y) < v (algebraMap O F x)
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `Valuation.Integers.le_iff_dvd`：le_iff_dvd (hv : Integers v O) {x y : O} 
: v (algebraMap O F x) <= v (algebraMap O F y) ↔ y ∣ x
· 使用定理 `Valuation.Integers.dvd_iff_le`：dvd_iff_le (hv : Integers v O) {x y : O} 
: x ∣ y ↔ v (algebraMap O F y) <= v (algebraMap O F x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
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
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `one_le_of_le_mul_left₀`：one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha :
 0 < a) (h : a <= a * b) : 1 <= b
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Valuation.Integers.valuation_pos_iff_ne_zero`：valuation_pos_iff_ne_zero 
(hv : Integers v O) {x : O} : 0 < v (algebraMap O F x) ↔ x != 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ne_iff_lt_iff_le`：ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
· 使用定理 `dvdNotUnit_of_dvd_of_not_dvd`：dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd
 : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b
-/
theorem dvdNotUnit_iff_lt (hv : Integers v O) {x y : O} :
    DvdNotUnit x y ↔ v (algebraMap O F y) < v (algebraMap O F x) := by
  rw [lt_iff_le_not_ge, hv.le_iff_dvd, hv.le_iff_dvd]
  refine ⟨?_, And.elim dvdNotUnit_of_dvd_of_not_dvd⟩
  rintro ⟨hx0, d, hdu, rfl⟩
  refine ⟨⟨d, rfl⟩, ?_⟩
  rw [hv.isUnit_iff_valuation_eq_one, ← ne_eq, ne_iff_lt_iff_le.mpr (hv.map_le_one d)] at hdu
  rw [dvd_iff_le hv]
  simp only [map_mul, not_le]
  contrapose! hdu
  refine one_le_of_le_mul_left₀ ?_ hdu
  simp [hv.valuation_pos_iff_ne_zero, hx0]
/-
**Valuation.Integers.eq_algebraMap_or_inv_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空
间 `Valuation.Integers`。
形式化陈述：eq_algebraMap_or_inv_eq_algebraMap (hv : Integers v O) (x : F) : exists a 
: O, x = algebraMap O F a ∨ x⁻¹ = algebraMap O F a
参数：hv : Integers v O；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.val_le_one_or_val_inv_le_one`：val_le_one_or_val_inv_le_one (v 
: Valuation K Γ₀) (x : K) : v x <= 1 ∨ v x⁻¹ <= 1
· 使用定理 `Valuation.Integers.exists_of_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst 
: CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} 
  {O : Type w} [inst_2 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_algebraMap_or_inv_eq_algebraMap (hv : Integers v O) (x : F) :
    ∃ a : O, x = algebraMap O F a ∨ x⁻¹ = algebraMap O F a := by
  rcases val_le_one_or_val_inv_le_one v x with h | h <;>
  obtain ⟨a, ha⟩ := exists_of_le_one hv h
  exacts [⟨a, Or.inl ha.symm⟩, ⟨a, Or.inr ha.symm⟩]
/-
**Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap** 是 Mathlib
 中的一个引理，位于命名空间 `Valuation.Integers`。
形式化陈述：coe_span_singleton_eq_setOfPred_le_v_algebraMap (hv : Integers v O) (x : O
) : (Ideal.span {x} : Set O) = {y : O | v (algebraMap O F y) <= v (algebraMap O 
F x)}
参数：hv : Integers v O；x : O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_zero`：span_zero : span R (0 : Set M) = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Valuation.Integers.dvd_iff_le`：dvd_iff_le (hv : Integers v O) {x y : O} 
: x ∣ y ↔ v (algebraMap O F y) <= v (algebraMap O F x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_span_singleton_eq_setOfPred_le_v_algebraMap (hv : Integers v O) (x : O) :
    (Ideal.span {x} : Set O) = {y : O | v (algebraMap O F y) ≤ v (algebraMap O F x)} := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Set.singleton_zero, map_eq_zero_iff _ hv.hom_inj]
  ext
  simp [SetLike.mem_coe, Ideal.mem_span_singleton, hv.dvd_iff_le]

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_algebraMap := coe_span_singleton_eq_setOfPred_le_v_algebraMap
/-
**Valuation.Integers.bijective_algebraMap_of_subsingleton_units_mrange** 是 Mathl
ib 中的一个引理，位于命名空间 `Valuation.Integers`。
形式化陈述：bijective_algebraMap_of_subsingleton_units_mrange (hv : Integers v O) [Sub
singleton (MonoidHom.mrange v)ˣ] : Function.Bijective (algebraMap O F)
参数：hv : Integers v O；MonoidHom.mrange v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `Valuation.Integers.exists_of_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst 
: CommRing R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀} 
  {O : Type w} [inst_2 : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma bijective_algebraMap_of_subsingleton_units_mrange (hv : Integers v O)
    [Subsingleton (MonoidHom.mrange v)ˣ] :
    Function.Bijective (algebraMap O F) := by
  refine ⟨hv.hom_inj, fun x ↦ hv.exists_of_le_one ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (congr_arg Units.val (Subsingleton.elim (α := (MonoidHom.mrange v)ˣ)
      ((isUnit_iff_ne_zero.mpr hx).unit.map v.toMonoidHom.mrangeRestrict) 1)).le
/-
**Valuation.Integers.isPrincipal_iff_exists_isGreatest** 是 Mathlib 中的一个引理，位于命名空间
 `Valuation.Integers`。
形式化陈述：isPrincipal_iff_exists_isGreatest (hv : Integers v O) {I : Ideal O} : I.Is
Principal ↔ exists x, IsGreatest (v ∘ algebraMap O F '' I) x
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Valuation.Integers.le_of_dvd`：le_of_dvd (hv : Integers v O) {x y : O} (h
 : x ∣ y) : v (algebraMap O R y) <= v (algebraMap O R x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Valuation.Integers.dvd_of_le`：dvd_of_le (hv : Integers v O) {x y : O} (h
 : v (algebraMap O F x) <= v (algebraMap O F y)) : y ∣ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Ideal.mem_of_dvd`：mem_of_dvd (hab : a ∣ b) (ha : a in I) : b in I
-/
lemma isPrincipal_iff_exists_isGreatest (hv : Integers v O) {I : Ideal O} :
    I.IsPrincipal ↔ ∃ x, IsGreatest (v ∘ algebraMap O F '' I) x := by
  constructor <;> rintro ⟨x, hx⟩
  · refine ⟨(v ∘ algebraMap O F) x, ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      simp [hx]
    · intro y hy
      simp only [Function.comp_apply, hx, Ideal.submodule_span_eq, Set.mem_image,
        SetLike.mem_coe, Ideal.mem_span_singleton] at hy
      obtain ⟨y, hy, rfl⟩ := hy
      exact le_of_dvd hv hy
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact ⟨fun hb ↦ dvd_of_le hv (hx.2 <| mem_image_of_mem _ hb), fun hb ↦ I.mem_of_dvd hb ha⟩
/-
**Valuation.Integers.isPrincipal_iff_exists_eq_setOfPred_valuation_le** 是 Mathli
b 中的一个引理，位于命名空间 `Valuation.Integers`。
形式化陈述：isPrincipal_iff_exists_eq_setOfPred_valuation_le (hv : Integers v O) {I : 
Ideal O} : I.IsPrincipal ↔ exists x, (I : Set O) = {y | v (algebraMap O F y) <= 
v (algebraMap O F x)}
参数：hv : Integers v O。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.Integers.isPrincipal_iff_exists_isGreatest`：isPrincipal_iff_ex
ists_isGreatest (hv : Integers v O) {I : Ideal O} : I.IsPrincipal ↔ exists x, Is
Greatest (v ∘ algebraMap O F '' I) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Ideal.mem_of_dvd`：mem_of_dvd (hab : a ∣ b) (ha : a in I) : b in I
· 使用定理 `Valuation.Integers.le_iff_dvd`：le_iff_dvd (hv : Integers v O) {x y : O} 
: v (algebraMap O F x) <= v (algebraMap O F y) ↔ y ∣ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isPrincipal_iff_exists_eq_setOfPred_valuation_le (hv : Integers v O) {I : Ideal O} :
    I.IsPrincipal ↔ ∃ x, (I : Set O) = {y | v (algebraMap O F y) ≤ v (algebraMap O F x)} := by
  rw [isPrincipal_iff_exists_isGreatest hv]
  constructor <;> rintro ⟨x, hx⟩
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [SetLike.mem_coe, mem_ofPred_eq]
    constructor <;> intro h
    · exact hx.right (Set.mem_image_of_mem _ h)
    · rw [le_iff_dvd hv] at h
      exact Ideal.mem_of_dvd I h ha
  · refine ⟨v (algebraMap O F x), Set.mem_image_of_mem _ ?_, ?_⟩
    · simp [hx]
    · simp [hx, mem_upperBounds]

@[deprecated (since := "2026-07-09")]
alias isPrincipal_iff_exists_eq_setOf_valuation_le :=
  isPrincipal_iff_exists_eq_setOfPred_valuation_le

set_option backward.isDefEq.respectTransparency false in
/-
**Valuation.Integers.not_denselyOrdered_of_isPrincipalIdealRing** 是 Mathlib 中的一个
引理，位于命名空间 `Valuation.Integers`。
形式化陈述：not_denselyOrdered_of_isPrincipalIdealRing [IsPrincipalIdealRing O] (hv : 
Integers v O) : ¬ DenselyOrdered (range v)
参数：hv : Integers v O。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Valuation.map_add_lt`：map_add_lt {x y g} (hx : v x < g) (hy : v y < g) :
 v (x + y) < g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Right.mul_lt_one_of_le_of_lt`：Right.mul_lt_one_of_le_of_lt [MulRightMono
 α] {a b : α} (ha : a <= 1) (hb : b < 1) : a * b < 1
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `Valuation.Integers.map_le_one`：∀ {R : Type u} {Γ₀ : Type v} [inst : Comm
Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O :
 Type w} [inst_2 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `Valuation.Integers.isPrincipal_iff_exists_isGreatest`：isPrincipal_iff_ex
ists_isGreatest (hv : Integers v O) {I : Ideal O} : I.IsPrincipal ↔ exists x, Is
Greatest (v ∘ algebraMap O F '' I) x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 39 条，此处仅展示前 30 条）
-/
lemma not_denselyOrdered_of_isPrincipalIdealRing [IsPrincipalIdealRing O] (hv : Integers v O) :
    ¬ DenselyOrdered (range v) := by
  intro H
  -- nonunits as an ideal isn't defined here, nor shown to be equivalent to `v x < 1`
  set I : Ideal O := {
    carrier := v ∘ algebraMap O F ⁻¹' Iio (1 : Γ₀)
    add_mem' := fun {a b} ha hb ↦ by simpa using map_add_lt v ha hb
    zero_mem' := by simp
    smul_mem' := by
      intro c x
      simp only [mem_preimage, Function.comp_apply, mem_Iio, smul_eq_mul, map_mul]
      intro hx
      exact Right.mul_lt_one_of_le_of_lt (hv.map_le_one c) hx
  }
  obtain ⟨x, hx₁, hx⟩ :
    ∃ x, v (algebraMap O F x) < 1 ∧
      v (algebraMap O F x) ∈ upperBounds (Iio 1 ∩ range (v ∘ algebraMap O F)) := by
    simpa [I, IsGreatest, hv.isPrincipal_iff_exists_isGreatest, ← image_preimage_eq_inter_range]
      using IsPrincipalIdealRing.principal I
  obtain ⟨y, hy, hy₁⟩ : ∃ y, v (algebraMap O F x) < v y ∧ v y < 1 := by
    simpa only [Subtype.exists, Subtype.mk_lt_mk, exists_range_iff, exists_prop]
      using H.dense ⟨v (algebraMap O F x), mem_range_self _⟩ ⟨1, 1, v.map_one⟩ hx₁
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hy₁.le
  exact hy.not_ge <| hx ⟨hy₁, mem_range_self _⟩

end Integers

open Integers in
/-
**Valuation.Integer.not_isUnit_iff_valuation_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `V
aluation.Integer`。
形式化陈述：∀ {F : Type u} {Γ₀ : Type v} [inst : Field F] [inst_1 : LinearOrderedCommG
roupWithZero Γ₀] {v : Valuation F Γ₀}   {x : ↥v.integer}, ¬IsUnit x ↔ v ↑x < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Integer.not_isUnit_iff_valuation_lt_one {x : v.integer} : ¬IsUnit x ↔ v x < 1 := by
  rw [← not_le, not_iff_not, isUnit_iff_valuation_eq_one (F := F) (Γ₀ := Γ₀),
    le_antisymm_iff]
  exacts [and_iff_right x.2, integer.integers v]

namespace integer

/-
**Valuation.integer.v_irreducible_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.in
teger`。
形式化陈述：v_irreducible_lt_one {ϖ : v.integer} (h : Irreducible ϖ) : v ϖ < 1
参数：h : Irreducible ϖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valuation.Integers.valuation_irreducible_lt_one`：valuation_irreducible_l
t_one (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) : v (algebraMap O F ϖ) < 1
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
lemma v_irreducible_lt_one {ϖ : v.integer} (h : Irreducible ϖ) :
    v ϖ < 1 :=
  (Valuation.integer.integers v).valuation_irreducible_lt_one h
/-
**Valuation.integer.v_irreducible_pos** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.integ
er`。
形式化陈述：v_irreducible_pos {ϖ : v.integer} (h : Irreducible ϖ) : 0 < v ϖ
参数：h : Irreducible ϖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valuation.Integers.valuation_irreducible_pos`：valuation_irreducible_pos 
(hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) : 0 < v (algebraMap O F ϖ)
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
lemma v_irreducible_pos {ϖ : v.integer} (h : Irreducible ϖ) : 0 < v ϖ :=
  (Valuation.integer.integers v).valuation_irreducible_pos h
/-
**Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe** 是 Mathlib 中的一个引理，
位于命名空间 `Valuation.integer`。
形式化陈述：coe_span_singleton_eq_setOfPred_le_v_coe (x : v.integer) : (Ideal.span {x}
 : Set v.integer) = {y : v.integer | v y <= v x}
参数：x : v.integer。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap`：coe_
span_singleton_eq_setOfPred_le_v_algebraMap (hv : Integers v O) (x : O) : (Ideal
.span {x} : Set O) = {y : O | v (algebraMap O F y) <= v …
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
lemma coe_span_singleton_eq_setOfPred_le_v_coe (x : v.integer) :
    (Ideal.span {x} : Set v.integer) = {y : v.integer | v y ≤ v x} :=
  (Valuation.integer.integers v).coe_span_singleton_eq_setOfPred_le_v_algebraMap x

@[deprecated (since := "2026-07-09")]
alias coe_span_singleton_eq_setOf_le_v_coe := coe_span_singleton_eq_setOfPred_le_v_coe

end integer

end Field

section Ideal

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation R Γ₀)
local notation "𝓞" => v.integer

/-- The `v.integer`-submodule of `R` of elements whose valuation is less than or equal to a
certain value. -/
/-
**Valuation.leSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：leSubmodule (γ : Γ₀) : Submodule 𝓞 R where __
参数：γ : Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v.integer`-submodule of `R` of elements whose valuation is less than or equ
al to a
certain value.
-/
def leSubmodule (γ : Γ₀) : Submodule 𝓞 R where
  __ := leAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_le_of_le_one_of_le r.prop h

/-- The `v.integer`-submodule of `R` of elements whose valuation is less than a certain unit. -/
/-
**Valuation.ltSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：ltSubmodule (γ : Γ₀ˣ) : Submodule 𝓞 R where __
参数：γ : Γ₀ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `v.integer`-submodule of `R` of elements whose valuation is less than a cert
ain unit.
-/
def ltSubmodule (γ : Γ₀ˣ) : Submodule 𝓞 R where
  __ := ltAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h
/-
**Valuation.leSubmodule_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leSubmodule_monotone : Monotone (leSubmodule v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.leAddSubgroup_monotone`：leAddSubgroup_monotone (v : Valuation 
R Γ₀) : Monotone v.leAddSubgroup
-/
lemma leSubmodule_monotone : Monotone (leSubmodule v) :=
  leAddSubgroup_monotone v
/-
**Valuation.ltSubmodule_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ltSubmodule_monotone : Monotone (ltSubmodule v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.ltAddSubgroup_monotone`：ltAddSubgroup_monotone (v : Valuation 
R Γ₀) : Monotone v.ltAddSubgroup
-/
lemma ltSubmodule_monotone : Monotone (ltSubmodule v) :=
  ltAddSubgroup_monotone v
/-
**Valuation.ltSubmodule_le_leSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ltSubmodule_le_leSubmodule (γ : Γ₀ˣ) : ltSubmodule v γ <= leSubmodule v (γ
 : Γ₀)
参数：γ : Γ₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.ltAddSubgroup_le_leAddSubgroup`：ltAddSubgroup_le_leAddSubgroup
 (v : Valuation R Γ₀) (γ : Γ₀ˣ) : v.ltAddSubgroup γ <= v.leAddSubgroup γ
-/
lemma ltSubmodule_le_leSubmodule (γ : Γ₀ˣ) :
    ltSubmodule v γ ≤ leSubmodule v (γ : Γ₀) :=
  ltAddSubgroup_le_leAddSubgroup v γ

variable {v} in
@[simp]
/-
**Valuation.mem_leSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_leSubmodule_iff {γ : Γ₀} {x : R} : x in leSubmodule v γ ↔ v x <= γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_leSubmodule_iff {γ : Γ₀} {x : R} :
    x ∈ leSubmodule v γ ↔ v x ≤ γ :=
  Iff.rfl

variable {v} in
@[simp]
/-
**Valuation.mem_ltSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_ltSubmodule_iff {γ : Γ₀ˣ} {x : R} : x in ltSubmodule v γ ↔ v x < γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ltSubmodule_iff {γ : Γ₀ˣ} {x : R} :
    x ∈ ltSubmodule v γ ↔ v x < γ :=
  Iff.rfl

@[simp]
/-
**Valuation.leSubmodule_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leSubmodule_zero (K : Type*) [Field K] (v : Valuation K Γ₀) : leSubmodule 
v (0 : Γ₀) = ⊥
参数：K : Type*；v : Valuation K Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma leSubmodule_zero (K : Type*) [Field K] (v : Valuation K Γ₀) :
    leSubmodule v (0 : Γ₀) = ⊥ := by
  ext; simp
/-
**Valuation.leSubmodule_v_le_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leSubmodule_v_le_of_mem {K : Type*} [Field K] (v : Valuation K Γ₀) {S : Su
bmodule v.integer K} {x : K} (hx : x in S) : leSubmodule v (v x) <= S
参数：v : Valuation K Γ₀；hx : x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.leSubmodule_zero`：leSubmodule_zero (K : Type*) [Field K] (v : 
Valuation K Γ₀) : leSubmodule v (0 : Γ₀) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toMulPosStrictMono`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], MulPosStrictMono α
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
lemma leSubmodule_v_le_of_mem {K : Type*} [Field K] (v : Valuation K Γ₀)
    {S : Submodule v.integer K} {x : K} (hx : x ∈ S) :
    leSubmodule v (v x) ≤ S := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) ≤ 1 := by simp [div_le_one_of_le₀ hy]
  simpa [Subring.smul_def, div_mul_cancel₀ _ hx0] using S.smul_mem ⟨_, this⟩ hx
/-
**Valuation.ltSubmodule_v_le_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ltSubmodule_v_le_of_mem {K : Type*} [Field K] {v : Valuation K Γ₀} {S : Su
bmodule v.integer K} {x : K} (hx : x in S) (hxv : v x != 0) : ltSubmodule v (Uni
ts.mk0 _ hxv) <= S
参数：hx : x in S；hxv : v x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用引理 `Valuation.leSubmodule_v_le_of_mem`：leSubmodule_v_le_of_mem {K : Type*} [
Field K] (v : Valuation K Γ₀) {S : Submodule v.integer K} {x : K} (hx : x in S) 
: leSubmodule v (v x) <…
· 使用引理 `Valuation.ltSubmodule_le_leSubmodule`：ltSubmodule_le_leSubmodule (γ : Γ₀
ˣ) : ltSubmodule v γ <= leSubmodule v (γ : Γ₀)
-/
lemma ltSubmodule_v_le_of_mem {K : Type*} [Field K] {v : Valuation K Γ₀}
    {S : Submodule v.integer K} {x : K} (hx : x ∈ S) (hxv : v x ≠ 0) :
    ltSubmodule v (Units.mk0 _ hxv) ≤ S :=
  (leSubmodule_v_le_of_mem v hx).trans' (ltSubmodule_le_leSubmodule _ _)

-- the ideals do not use the submodules due to `Submodule.comap _ (Algebra.linearMap _ _)`
-- requiring commutativity

/-- The ideal of elements of the valuation subring whose valuation is less than or equal to a
certain value. -/
/-
**Valuation.leIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：leIdeal (γ : Γ₀) : Ideal 𝓞 where __
参数：γ : Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal of elements of the valuation subring whose valuation is less than or e
qual to a
certain value.
-/
def leIdeal (γ : Γ₀) : Ideal 𝓞 where
  __ := AddSubgroup.addSubgroupOf (leAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h :=
    -- need to specify the subgroup, it is not inferred otherwise
    (AddSubgroup.mem_addSubgroupOf (K := v.integer.toAddSubgroup)).mpr <| by
      simpa using mul_le_of_le_one_of_le r.prop h

/-- The ideal of elements of the valuation subring whose valuation is less than a certain unit. -/
/-
**Valuation.ltIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：ltIdeal (γ : Γ₀ˣ) : Ideal 𝓞 where __
参数：γ : Γ₀ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ideal of elements of the valuation subring whose valuation is less than a ce
rtain unit.
-/
def ltIdeal (γ : Γ₀ˣ) : Ideal 𝓞 where
  __ := AddSubgroup.addSubgroupOf (ltAddSubgroup v γ) v.integer.toAddSubgroup
  smul_mem' r x h := by
    change v ((r : R) * x) < γ -- not sure why simp can't get us to here
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

-- Can't use `leAddSubgroup` because `addSubgroupOf` is a dependent function
/-
**Valuation.leIdeal_mono** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leIdeal_mono : Monotone (leIdeal v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
-/
lemma leIdeal_mono : Monotone (leIdeal v) :=
  fun _ _ h _ ↦ h.trans'
/-
**Valuation.ltIdeal_mono** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ltIdeal_mono : Monotone (ltIdeal v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.val_le_val`：val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α
) <= b ↔ a <= b
-/
lemma ltIdeal_mono : Monotone (ltIdeal v) :=
  fun _ _ h _ ↦ (Units.val_le_val.mpr h).trans_lt'
/-
**Valuation.ltIdeal_le_leIdeal** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ltIdeal_le_leIdeal (γ : Γ₀ˣ) : ltIdeal v γ <= leIdeal v (γ : Γ₀)
参数：γ : Γ₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ltIdeal_le_leIdeal (γ : Γ₀ˣ) :
    ltIdeal v γ ≤ leIdeal v (γ : Γ₀) :=
  fun _ h ↦ h.le

variable {v} in
@[simp]
/-
**Valuation.mem_leIdeal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_leIdeal_iff {γ : Γ₀} {x : 𝓞} : x in leIdeal v γ ↔ v (x : R) <= γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_leIdeal_iff {γ : Γ₀} {x : 𝓞} :
    x ∈ leIdeal v γ ↔ v (x : R) ≤ γ :=
  Iff.rfl

variable {v} in
@[simp]
/-
**Valuation.mem_ltIdeal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_ltIdeal_iff {γ : Γ₀ˣ} {x : 𝓞} : x in ltIdeal v γ ↔ v (x : R) < γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ltIdeal_iff {γ : Γ₀ˣ} {x : 𝓞} :
    x ∈ ltIdeal v γ ↔ v (x : R) < γ :=
  Iff.rfl

@[simp]
/-
**Valuation.leIdeal_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leIdeal_zero (K : Type*) [Field K] (v : Valuation K Γ₀) : leIdeal v (0 : Γ
₀) = ⊥
参数：K : Type*；v : Valuation K Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma leIdeal_zero (K : Type*) [Field K] (v : Valuation K Γ₀) :
    leIdeal v (0 : Γ₀) = ⊥ := by
  ext; simp
/-
**Valuation.leSubmodule_comap_algebraMap_eq_leIdeal** 是 Mathlib 中的一个引理，位于命名空间 `V
aluation`。
形式化陈述：leSubmodule_comap_algebraMap_eq_leIdeal {K : Type*} [Field K] (v : Valuati
on K Γ₀) (γ : Γ₀) : (leSubmodule v γ).comap (Algebra.linearMap _ _) = leIdeal v 
γ
参数：v : Valuation K Γ₀；γ : Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma leSubmodule_comap_algebraMap_eq_leIdeal {K : Type*} [Field K] (v : Valuation K Γ₀) (γ : Γ₀) :
    (leSubmodule v γ).comap (Algebra.linearMap _ _) = leIdeal v γ :=
  Submodule.ext fun _ ↦ Iff.rfl
/-
**Valuation.leIdeal_map_algebraMap_eq_leSubmodule_min** 是 Mathlib 中的一个引理，位于命名空间 
`Valuation`。
形式化陈述：leIdeal_map_algebraMap_eq_leSubmodule_min {K : Type*} [Field K] (v : Valua
tion K Γ₀) (γ : Γ₀) : Submodule.map (Algebra.linearMap _ _) (leIdeal v γ) = leSu
bmodule v (min 1 γ)
参数：v : Valuation K Γ₀；γ : Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `min_cases`：min_cases (a b : α) : min a b = a ∧ a <= b ∨ min a b = b ∧ b 
< a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma leIdeal_map_algebraMap_eq_leSubmodule_min {K : Type*} [Field K] (v : Valuation K Γ₀)
    (γ : Γ₀) :
    Submodule.map (Algebra.linearMap _ _) (leIdeal v γ) = leSubmodule v (min 1 γ) := by
  ext x
  simp only [Submodule.mem_map, mem_leIdeal_iff, Algebra.linearMap_apply, mem_leSubmodule_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases min_cases 1 γ with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact y.prop
    · rw [h]
      exact hy
  · intro hx
    rcases min_cases 1 γ with ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h] at hx
    · exact ⟨⟨x, hx⟩, hx.trans h', rfl⟩
    · exact ⟨⟨x, hx.trans h'.le⟩, hx, rfl⟩

-- Ideally, this would follow from `leSubmodule_v_le_of_mem`
/-
**Valuation.leIdeal_v_le_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leIdeal_v_le_of_mem {K : Type*} [Field K] (v : Valuation K Γ₀) {I : Ideal 
v.integer} {x : v.integer} (hx : x in I) : leIdeal v (v (x : K)) <= I
参数：v : Valuation K Γ₀；hx : x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
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
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.leIdeal_zero`：leIdeal_zero (K : Type*) [Field K] (v : Valuatio
n K Γ₀) : leIdeal v (0 : Γ₀) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用引理 `div_le_one_of_le₀`：div_le_one_of_le₀ [ZeroLEOneClass G₀] (h : a <= b) (h
b : 0 <= b) : a / b <= 1
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toMulPosStrictMono`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], MulPosStrictMono α
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
lemma leIdeal_v_le_of_mem {K : Type*} [Field K] (v : Valuation K Γ₀)
    {I : Ideal v.integer} {x : v.integer} (hx : x ∈ I) :
    leIdeal v (v (x : K)) ≤ I := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  intro y hy
  have : v ((y : K) / x) ≤ 1 := by simpa using div_le_one_of_le₀ hy zero_le
  convert! I.smul_mem ⟨_, this⟩ hx using 1
  simp [Subtype.ext_iff, div_mul_cancel₀ _ (ZeroMemClass.coe_eq_zero.not.mpr hx0)]
/-
**Valuation.ltIdeal_v_le_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ltIdeal_v_le_of_mem {K : Type*} [Field K] {v : Valuation K Γ₀} {I : Ideal 
v.integer} {x : v.integer} (hx : x in I) (hxv : v (x : K) != 0) : ltIdeal v (Uni
ts.mk0 _ hxv) <= I
参数：hx : x in I；hxv : v (x : K) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用引理 `Valuation.leIdeal_v_le_of_mem`：leIdeal_v_le_of_mem {K : Type*} [Field K]
 (v : Valuation K Γ₀) {I : Ideal v.integer} {x : v.integer} (hx : x in I) : leId
eal v (v (x : K)) <…
· 使用引理 `Valuation.ltIdeal_le_leIdeal`：ltIdeal_le_leIdeal (γ : Γ₀ˣ) : ltIdeal v γ
 <= leIdeal v (γ : Γ₀)
-/
lemma ltIdeal_v_le_of_mem {K : Type*} [Field K] {v : Valuation K Γ₀}
    {I : Ideal v.integer} {x : v.integer} (hx : x ∈ I) (hxv : v (x : K) ≠ 0) :
    ltIdeal v (Units.mk0 _ hxv) ≤ I :=
  (leIdeal_v_le_of_mem v hx).trans' (ltIdeal_le_leIdeal _ _)

end Ideal

end Valuation

