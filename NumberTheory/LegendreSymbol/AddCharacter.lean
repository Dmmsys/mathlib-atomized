/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.ZMod.Units

/-!
# Additive characters of finite rings and fields

This file collects some results on additive characters whose domain is (the additive group of)
a finite ring or field.

## Main definitions and results

We define an additive character `ψ` to be *primitive* if `mulShift ψ a` is trivial only when
`a = 0`.

We show that when `ψ` is primitive, then the map `a ↦ mulShift ψ a` is injective
(`AddChar.to_mulShift_inj_of_isPrimitive`) and that `ψ` is primitive when `R` is a field
and `ψ` is nontrivial (`AddChar.IsNontrivial.isPrimitive`).

We also show that there are primitive additive characters on `R` (with suitable
target `R'`) when `R` is a field or `R = ZMod n` (`AddChar.primitiveCharFiniteField`
and `AddChar.primitiveZModChar`).

Finally, we show that the sum of all character values is zero when the character
is nontrivial (and the target is a domain); see `AddChar.sum_eq_zero_of_isNontrivial`.

## Tags

additive character
-/

@[expose] public section

assert_not_exists MeasureTheory.integral

universe u v

namespace AddChar

section Additive

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R : Type u} [CommRing R] {R' : Type v} [CommMonoid R']

/-- The values of an additive character on a ring of positive characteristic are roots of unity. -/
/-
**AddChar.val_mem_rootsOfUnity** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：val_mem_rootsOfUnity (φ : AddChar R R') (a : R) (h : 0 < ringChar R) : (φ.
val_isUnit a).unit in rootsOfUnity (ringChar R).toPNat' R'
参数：φ : AddChar R R'；a : R；h : 0 < ringChar R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AddChar.val_isUnit`：val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddCha
r A M) (a : A) : IsUnit (φ a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.toPNat'_coe`：∀ (n : ℕ), ↑n.toPNat' = if 0 < n then n else 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The values of an additive character on a ring of positive characteristic are roo
ts of unity.
-/
lemma val_mem_rootsOfUnity (φ : AddChar R R') (a : R) (h : 0 < ringChar R) :
    (φ.val_isUnit a).unit ∈ rootsOfUnity (ringChar R).toPNat' R' := by
  simp only [mem_rootsOfUnity', IsUnit.unit_spec, Nat.toPNat'_coe, h, ↓reduceIte,
    ← map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, map_zero_eq_one]

/-- An additive character is *primitive* iff all its multiplicative shifts by nonzero
elements are nontrivial. -/
/-
**AddChar.IsPrimitive** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：IsPrimitive (ψ : AddChar R R') : Prop
参数：ψ : AddChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive character is *primitive* iff all its multiplicative shifts by nonzer
o
elements are nontrivial.
-/
def IsPrimitive (ψ : AddChar R R') : Prop := ∀ ⦃a : R⦄, a ≠ 0 → mulShift ψ a ≠ 1

/-- The composition of a primitive additive character with an injective monoid homomorphism
is also primitive. -/
/-
**AddChar.IsPrimitive.compMulHom_of_isPrimitive** 是 Mathlib 中的一个定理，位于命名空间 `AddCh
ar.IsPrimitive`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {R' : Type v} [inst_1 : CommMonoid R'] 
{R'' : Type u_1} [inst_2 : CommMonoid R'']   {φ : AddChar R R'} {f : R' →* R''},
 φ.IsPrimitive → Function.Injective ⇑f → (f.compAddChar φ).IsPrimitive
参数：f.compAddChar φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `MonoidHom.compAddChar_injective_right`：∀ {B : Type u_2} {M : Type u_3} {
N : Type u_4} [inst : AddMonoid B] [inst_1 : Monoid M] [inst_2 : Monoid N]   (f 
: M →* N), Function.Injecti…

--- 原说明 ---
The composition of a primitive additive character with an injective monoid homom
orphism
is also primitive.
-/
lemma IsPrimitive.compMulHom_of_isPrimitive {R'' : Type*} [CommMonoid R''] {φ : AddChar R R'}
    {f : R' →* R''} (hφ : φ.IsPrimitive) (hf : Function.Injective f) :
    (f.compAddChar φ).IsPrimitive := fun a ha ↦ by
  simpa [DFunLike.ext_iff] using (MonoidHom.compAddChar_injective_right f hf).ne (hφ ha)

/-- The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive. -/
/-
**AddChar.to_mulShift_inj_of_isPrimitive** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : F
unction.Injective ψ.mulShift
参数：hψ : IsPrimitive ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddChar.mulShift_mul`：mulShift_mul (ψ : AddChar R M) (r s : R) : mulShif
t ψ r * mulShift ψ s = mulShift ψ (r + s)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `AddChar.mulShift_zero`：mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 
1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive.
-/
theorem to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    Function.Injective ψ.mulShift := by
  intro a b h
  apply_fun fun x => x * mulShift ψ (-b) at h
  simp only [mulShift_mul, mulShift_zero, add_neg_cancel] at h
  simpa [← sub_eq_add_neg, sub_eq_zero] using (hψ · h)

-- `AddCommGroup.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.
/-- When `R` is a field `F`, then a nontrivial additive character is primitive -/
/-
**AddChar.IsPrimitive.of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `AddChar.IsPrimitive`。
形式化陈述：∀ {R' : Type v} [inst : CommMonoid R'] {F : Type u} [inst_1 : Field F] {ψ 
: AddChar F R'}, ψ ≠ 1 → ψ.IsPrimitive
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AddChar.mulShift_mulShift`：mulShift_mulShift (ψ : AddChar R M) (r s : R)
 : mulShift (mulShift ψ r) s = mulShift ψ (r * s)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `AddChar.mulShift_one`：mulShift_one (ψ : AddChar R M) : mulShift ψ 1 = ψ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
When `R` is a field `F`, then a nontrivial additive character is primitive
-/
theorem IsPrimitive.of_ne_one {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : ψ ≠ 1) :
    IsPrimitive ψ :=
  fun a ha h ↦ hψ <| by simpa [mulShift_mulShift, ha] using! congr_arg (mulShift · a⁻¹) h

/-- If `r` is not a unit, then `e.mulShift r` is not primitive. -/
/-
**AddChar.not_isPrimitive_mulShift** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：not_isPrimitive_mulShift [Finite R] (e : AddChar R R') {r : R} (hr : ¬ IsU
nit r) : ¬ IsPrimitive (e.mulShift r)
参数：e : AddChar R R'；hr : ¬ IsUnit r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AddChar.mulShift_mulShift`：mulShift_mulShift (ψ : AddChar R M) (r s : R)
 : mulShift (mulShift ψ r) s = mulShift ψ (r * s)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `AddChar.mulShift_zero`：mulShift_zero (ψ : AddChar R M) : mulShift ψ 0 = 
1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `r` is not a unit, then `e.mulShift r` is not primitive.
-/
lemma not_isPrimitive_mulShift [Finite R] (e : AddChar R R') {r : R}
    (hr : ¬ IsUnit r) : ¬ IsPrimitive (e.mulShift r) := by
  simp only [IsPrimitive, not_forall]
  simp only [isUnit_iff_mem_nonZeroDivisors_of_finite,
    mem_nonZeroDivisors_iff_right, not_forall] at hr
  rcases hr with ⟨x, h, h'⟩
  exact ⟨x, h', by simp only [mulShift_mulShift, mul_comm r, h, mulShift_zero, not_ne_iff]⟩

/-- Definition for a primitive additive character on a finite ring `R` into a cyclotomic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and the
fact that the character is primitive. -/
/-
**AddChar.PrimitiveAddChar** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddChar`。
形式化陈述：(R : Type u) → [CommRing R] → (R' : Type v) → [Field R'] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition for a primitive additive character on a finite ring `R` into a cyclot
omic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and
 the
fact that the character is primitive.
-/
structure PrimitiveAddChar (R : Type u) [CommRing R] (R' : Type v) [Field R'] where
  /-- The first projection from `PrimitiveAddChar`, giving the cyclotomic field. -/
  n : ℕ+
  /-- The second projection from `PrimitiveAddChar`, giving the character. -/
  char : AddChar R (CyclotomicField n R')
  /-- The third projection from `PrimitiveAddChar`, showing that `χ.char` is primitive. -/
  prim : IsPrimitive char

/-!
### Additive characters on `ZMod n`
-/

section ZMod

variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R] (e : AddChar (ZMod N) R)

/-- If `e` is not primitive, then `e.mulShift d = 1` for some proper divisor `d` of `N`. -/
/-
**AddChar.exists_divisor_of_not_isPrimitive** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：exists_divisor_of_not_isPrimitive (he : ¬e.IsPrimitive) : exists d : Nat, 
d ∣ N ∧ d < N ∧ e.mulShift d = 1
参数：he : ¬e.IsPrimitive。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `ZMod.eq_unit_mul_divisor`：eq_unit_mul_divisor {N : Nat} (a : ZMod N) : e
xists d : Nat, d ∣ N ∧ exists (u : ZMod N), IsUnit u ∧ a = u * d
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ZMod.natCast_self`：natCast_self (n : Nat) : (n : ZMod n) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddChar.mulShift_unit_eq_one_iff`：mulShift_unit_eq_one_iff (ψ : AddChar 
R M) {u : R} (hu : IsUnit u) : ψ.mulShift u = 1 ↔ ψ = 1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
If `e` is not primitive, then `e.mulShift d = 1` for some proper divisor `d` of 
`N`.
-/
lemma exists_divisor_of_not_isPrimitive (he : ¬e.IsPrimitive) :
    ∃ d : ℕ, d ∣ N ∧ d < N ∧ e.mulShift d = 1 := by
  simp_rw [IsPrimitive, not_forall, not_ne_iff] at he
  rcases he with ⟨b, hb_ne, hb⟩
  -- We have `AddChar.mulShift e b = 1`, but `b ≠ 0`.
  obtain ⟨d, hd, u, hu, rfl⟩ := b.eq_unit_mul_divisor
  refine ⟨d, hd, lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos _) hd) ?_, ?_⟩
  · exact fun h ↦ by simp only [h, ZMod.natCast_self, mul_zero, ne_eq, not_true_eq_false] at hb_ne
  · rw [← mulShift_unit_eq_one_iff _ hu, ← hb, mul_comm]
    ext1 y
    rw [mulShift_apply, mulShift_apply, mulShift_apply, mul_assoc]

end ZMod

section ZModChar

variable {C : Type v} [CommMonoid C]

section ZModCharDef


/-- We can define an additive character on `ZMod n` when we have an `n`th root of unity `ζ : C`. -/
/-
**AddChar.zmodChar** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：zmodChar (n : Nat) [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) : AddChar (ZMod n) 
C where toFun a
参数：n : Nat；hζ : ζ ^ n = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can define an additive character on `ZMod n` when we have an `n`th root of un
ity `ζ : C`.
-/
def zmodChar (n : ℕ) [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) : AddChar (ZMod n) C where
  toFun a := ζ ^ a.val
  map_zero_eq_one' := by simp only [ZMod.val_zero, pow_zero]
  map_add_eq_mul' x y := by simp only [ZMod.val_add, ← pow_eq_pow_mod _ hζ, ← pow_add]

/-- The additive character on `ZMod n` defined using `ζ` sends `a` to `ζ^a`. -/
/-
**AddChar.zmodChar_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：zmodChar_apply {n : Nat} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : ZMod n) 
: zmodChar n hζ a = ζ ^ a.val
参数：hζ : ζ ^ n = 1；a : ZMod n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive character on `ZMod n` defined using `ζ` sends `a` to `ζ^a`.
-/
theorem zmodChar_apply {n : ℕ} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : ZMod n) :
    zmodChar n hζ a = ζ ^ a.val :=
  rfl
/-
**AddChar.zmodChar_apply'** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：zmodChar_apply' {n : Nat} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : Nat) : 
zmodChar n hζ a = ζ ^ a
参数：hζ : ζ ^ n = 1；a : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_eq_pow_mod`：pow_eq_pow_mod (m : Nat) (ha : a ^ n = 1) : a ^ m = a ^ 
(m % n)
· 使用定理 `AddChar.zmodChar_apply`：zmodChar_apply {n : Nat} [NeZero n] {ζ : C} (hζ 
: ζ ^ n = 1) (a : ZMod n) : zmodChar n hζ a = ζ ^ a.val
· 使用定理 `ZMod.val_natCast`：val_natCast (n a : Nat) : (a : ZMod n).val = a % n
-/
theorem zmodChar_apply' {n : ℕ} [NeZero n] {ζ : C} (hζ : ζ ^ n = 1) (a : ℕ) :
    zmodChar n hζ a = ζ ^ a := by
  rw [pow_eq_pow_mod a hζ, zmodChar_apply, ZMod.val_natCast]

end ZModCharDef

/-- An additive character on `ZMod n` is nontrivial iff it takes a value `≠ 1` on `1`. -/
/-
**AddChar.zmod_char_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：zmod_char_ne_one_iff (n : Nat) [NeZero n] (ψ : AddChar (ZMod n) C) : ψ != 
1 ↔ ψ 1 != 1
参数：n : Nat；ψ : AddChar (ZMod n) C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.ne_one_iff`：ne_one_iff : ψ != 1 ↔ exists x, ψ x != 1
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用引理 `AddChar.map_nsmul_eq_pow`：map_nsmul_eq_pow (ψ : AddChar A M) (n : Nat) (
x : A) : ψ (n • x) = ψ x ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a

--- 原说明 ---
An additive character on `ZMod n` is nontrivial iff it takes a value `≠ 1` on `1
`.
-/
theorem zmod_char_ne_one_iff (n : ℕ) [NeZero n] (ψ : AddChar (ZMod n) C) : ψ ≠ 1 ↔ ψ 1 ≠ 1 := by
  rw [ne_one_iff]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  contrapose!
  rintro h₁ a
  have ha₁ : a = a.val • (1 : ZMod ↑n) := by
    rw [nsmul_eq_mul, mul_one]; exact (ZMod.natCast_zmod_val a).symm
  rw [ha₁, map_nsmul_eq_pow, h₁, one_pow]

/-- A primitive additive character on `ZMod n` takes the value `1` only at `0`. -/
/-
**AddChar.IsPrimitive.zmod_char_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddChar.Is
Primitive`。
形式化陈述：∀ {C : Type v} [inst : CommMonoid C] (n : ℕ) [NeZero n] {ψ : AddChar (ZMod
 n) C},   ψ.IsPrimitive → ∀ (a : ZMod n), ψ a = 1 ↔ a = 0
参数：n : ℕ；ZMod n；a : ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.zmod_char_ne_one_iff`：zmod_char_ne_one_iff (n : Nat) [NeZero n] 
(ψ : AddChar (ZMod n) C) : ψ != 1 ↔ ψ 1 != 1
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1

--- 原说明 ---
A primitive additive character on `ZMod n` takes the value `1` only at `0`.
-/
theorem IsPrimitive.zmod_char_eq_one_iff (n : ℕ) [NeZero n]
    {ψ : AddChar (ZMod n) C} (hψ : IsPrimitive ψ) (a : ZMod n) :
    ψ a = 1 ↔ a = 0 := by
  refine ⟨fun h => not_imp_comm.mp (@hψ a) ?_, fun ha => by rw [ha, map_zero_eq_one]⟩
  rw [zmod_char_ne_one_iff n (mulShift ψ a), mulShift_apply, mul_one, h, Classical.not_not]

/-- The converse: if the additive character takes the value `1` only at `0`,
then it is primitive. -/
/-
**AddChar.zmod_char_primitive_of_eq_one_only_at_zero** 是 Mathlib 中的一个定理，位于命名空间 `
AddChar`。
形式化陈述：zmod_char_primitive_of_eq_one_only_at_zero (n : Nat) (ψ : AddChar (ZMod n)
 C) (hψ : forall a, ψ a = 1 -> a = 0) : IsPrimitive ψ
参数：n : Nat；ψ : AddChar (ZMod n) C；hψ : forall a, ψ a = 1 -> a = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)

--- 原说明 ---
The converse: if the additive character takes the value `1` only at `0`,
then it is primitive.
-/
theorem zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : AddChar (ZMod n) C)
    (hψ : ∀ a, ψ a = 1 → a = 0) : IsPrimitive ψ := by
  intro a ha hf
  have h : mulShift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg (↑) hf) 1
  rw [mulShift_apply, mul_one] at h; norm_cast at h
  exact ha (hψ a h)

/-- The additive character on `ZMod n` associated to a primitive `n`th root of unity
is primitive -/
/-
**AddChar.zmodChar_primitive_of_primitive_root** 是 Mathlib 中的一个定理，位于命名空间 `AddCha
r`。
形式化陈述：zmodChar_primitive_of_primitive_root (n : Nat) [NeZero n] {ζ : C} (h : IsP
rimitiveRoot ζ n) : IsPrimitive (zmodChar n ((IsPrimitiveRoot.iff_def ζ n).mp h)
.left)
参数：n : Nat；h : IsPrimitiveRoot ζ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.zmod_char_primitive_of_eq_one_only_at_zero`：zmod_char_primitive_
of_eq_one_only_at_zero (n : Nat) (ψ : AddChar (ZMod n) C) (hψ : forall a, ψ a = 
1 -> a = 0) : IsPrimitive ψ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPrimitiveRoot.iff_def`：∀ {M : Type u_1} [inst : CommMonoid M] (ζ : M) 
(k : ℕ), IsPrimitiveRoot ζ k ↔ ζ ^ k = 1 ∧ ∀ (l : ℕ), ζ ^ l = 1 → k ∣ l
· 使用定理 `ZMod.val_eq_zero`：∀ {n : ℕ} (a : ZMod n), a.val = 0 ↔ a = 0
· 使用定理 `IsPrimitiveRoot.pow_inj`：pow_inj (h : IsPrimitiveRoot ζ k) ⦃i j : Nat⦄ (
hi : i < k) (hj : j < k) (H : ζ ^ i = ζ ^ j) : i = j
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `AddChar.zmodChar_apply`：zmodChar_apply {n : Nat} [NeZero n] {ζ : C} (hζ 
: ζ ^ n = 1) (a : ZMod n) : zmodChar n hζ a = ζ ^ a.val

--- 原说明 ---
The additive character on `ZMod n` associated to a primitive `n`th root of unity
is primitive
-/
theorem zmodChar_primitive_of_primitive_root (n : ℕ) [NeZero n] {ζ : C} (h : IsPrimitiveRoot ζ n) :
    IsPrimitive (zmodChar n ((IsPrimitiveRoot.iff_def ζ n).mp h).left) := by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  rw [zmodChar_apply, ← pow_zero ζ] at ha
  exact (ZMod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (ZMod.val_lt a) (NeZero.pos _) ha)

/-- There is a primitive additive character on `ZMod n` if the characteristic of the target
does not divide `n` -/
/-
**AddChar.primitiveZModChar** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：primitiveZModChar (n : Nat+) (F' : Type v) [Field F'] (h : (n : F') != 0) 
: PrimitiveAddChar (ZMod n) F'
参数：n : Nat+；F' : Type v；h : (n : F') != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.pnat`：∀ {a : ℕ+}, NeZero ↑a

--- 原说明 ---
There is a primitive additive character on `ZMod n` if the characteristic of the
 target
does not divide `n`
-/
noncomputable def primitiveZModChar (n : ℕ+) (F' : Type v) [Field F'] (h : (n : F') ≠ 0) :
    PrimitiveAddChar (ZMod n) F' :=
  have : NeZero (n : F') := ⟨h⟩
  ⟨n, zmodChar n (IsCyclotomicExtension.zeta_pow n F' _),
    zmodChar_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec n F' _)⟩

end ZModChar

end Additive

/-!
### Existence of a primitive additive character on a finite field
-/

/-- There is a primitive additive character on the finite field `F` if the characteristic
of the target is different from that of `F`.

We obtain it as the composition of the trace from `F` to `ZMod p` with a primitive
additive character on `ZMod p`, where `p` is the characteristic of `F`. -/
/-
**AddChar.FiniteField.primitiveChar** 是 Mathlib 中的一个定义，位于命名空间 `AddChar.FiniteFie
ld`。
形式化陈述：(F : Type u_1) →   (F' : Type u_2) →     [inst : Field F] → [Finite F] → [
inst_2 : Field F'] → ringChar F' ≠ ringChar F → AddChar.PrimitiveAddChar F F'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a primitive additive character on the finite field `F` if the character
istic
of the target is different from that of `F`.

We obtain it as the composition of the trace from `F` to `ZMod p` with a primiti
ve
additive character on `ZMod p`, where `p` is the characteristic of `F`.
-/
noncomputable def FiniteField.primitiveChar (F F' : Type*) [Field F] [Finite F] [Field F']
    (h : ringChar F' ≠ ringChar F) : PrimitiveAddChar F F' := by
  let p := ringChar F
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let pp := p.toPNat hp.1.pos
  have hp₂ : ¬ringChar F' ∣ p := by
    rcases CharP.char_is_prime_or_zero F' (ringChar F') with hq | hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [hq]
      exact fun hf => Nat.Prime.ne_zero hp.1 (zero_dvd_iff.mp hf)
  let ψ := primitiveZModChar pp F' (neZero_iff.mp (NeZero.of_not_dvd F' hp₂))
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  let ψ' := ψ.char.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ' : ψ' ≠ 1 := by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mul] at ha
    exact ne_one_iff.2
      ⟨a, fun hf => ha <| (ψ.prim.zmod_char_eq_one_iff pp <| Algebra.trace (ZMod p) F a).mp hf⟩
  exact ⟨ψ.n, ψ', IsPrimitive.of_ne_one hψ'⟩
/-!
### The sum of all character values
-/

section sum

variable {R : Type*} [AddGroup R] [Fintype R] {R' : Type*} [CommRing R']

/-- The sum over the values of a nontrivial additive character vanishes if the target ring
is a domain. -/
/-
**AddChar.sum_eq_zero_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：sum_eq_zero_of_ne_one [IsDomain R'] {ψ : AddChar R R'} (hψ : ψ != 1) : ∑ a
, ψ a = 0
参数：hψ : ψ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AddChar.ne_one_iff`：ne_one_iff : ψ != 1 ↔ exists x, ψ x != 1
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `AddGroup.addLeft_bijective`：∀ {G : Type u_5} [inst : AddGroup G] (a : G)
, Function.Bijective fun x => a + x
· 使用定理 `eq_zero_of_mul_eq_self_left`：eq_zero_of_mul_eq_self_left [IsRightCancelM
ulZero M₀] (h₁ : b != 1) (h₂ : b * a = a) : a = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y

--- 原说明 ---
The sum over the values of a nontrivial additive character vanishes if the targe
t ring
is a domain.
-/
theorem sum_eq_zero_of_ne_one [IsDomain R'] {ψ : AddChar R R'} (hψ : ψ ≠ 1) : ∑ a, ψ a = 0 := by
  rcases ne_one_iff.1 hψ with ⟨b, hb⟩
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_eq_mul] at h₁
  have h₂ : ∑ a : R, ψ a = Finset.univ.sum ↑ψ := rfl
  rw [← Finset.mul_sum, h₂] at h₁
  exact eq_zero_of_mul_eq_self_left hb h₁

/-- The sum over the values of the trivial additive character is the cardinality of the source. -/
/-
**AddChar.sum_eq_card_of_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：sum_eq_card_of_eq_one {ψ : AddChar R R'} (hψ : ψ = 1) : ∑ a, ψ a = Fintype
.card R
参数：hψ : ψ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The sum over the values of the trivial additive character is the cardinality of 
the source.
-/
theorem sum_eq_card_of_eq_one {ψ : AddChar R R'} (hψ : ψ = 1) :
    ∑ a, ψ a = Fintype.card R := by simp [hψ]

end sum

/-- The sum over the values of `mulShift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise. -/
/-
**AddChar.sum_mulShift** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：sum_mulShift {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] {R' : Ty
pe*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b : R) (hψ : IsPrimitive ψ)
 : ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0
参数：b : R；hψ : IsPrimitive ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `AddChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {ψ : 
AddChar R R'} (hψ : ψ != 1) : ∑ a, ψ a = 0

--- 原说明 ---
The sum over the values of `mulShift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise.
-/
theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b : R)
    (hψ : IsPrimitive ψ) : ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0 := by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_eq_one, Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact mod_cast sum_eq_zero_of_ne_one (hψ h)

/-!
### Complex-valued additive characters
-/

section Ring

variable {R : Type*} [CommRing R]

/-- Post-composing an additive character to `ℂ` with complex conjugation gives the inverse
character. -/
/-
**AddChar.starComp_eq_inv** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：starComp_eq_inv (hR : 0 < ringChar R) {φ : AddChar R Complex} : (starRingE
nd Complex).compAddChar φ = φ⁻¹
参数：hR : 0 < ringChar R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.ext`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [inst_
1 : Monoid M] (f g : AddChar A M),   (∀ (x : A), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.inv_apply'`：inv_apply' (ψ : AddChar A M) (a : A) : ψ⁻¹ a = (ψ a)
⁻¹
· 使用引理 `AddChar.val_isUnit`：val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddCha
r A M) (a : A) : IsUnit (φ a)
· 使用引理 `Complex.norm_eq_one_of_mem_rootsOfUnity`：Complex.norm_eq_one_of_mem_root
sOfUnity {ζ : Complexˣ} {n : Nat} [NeZero n] (hζ : ζ in rootsOfUnity n Complex) 
: ‖(ζ : Complex)‖ = 1
· 使用定理 `NeZero.pnat`：∀ {a : ℕ+}, NeZero ↑a
· 使用引理 `AddChar.val_mem_rootsOfUnity`：val_mem_rootsOfUnity (φ : AddChar R R') (a
 : R) (h : 0 < ringChar R) : (φ.val_isUnit a).unit in rootsOfUnity (ringChar R).
toPNat' R'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.inv_eq_conj`：∀ {z : ℂ}, ‖z‖ = 1 → z⁻¹ = (starRingEnd ℂ) z

--- 原说明 ---
Post-composing an additive character to `ℂ` with complex conjugation gives the i
nverse
character.
-/
lemma starComp_eq_inv (hR : 0 < ringChar R) {φ : AddChar R ℂ} :
    (starRingEnd ℂ).compAddChar φ = φ⁻¹ := by
  ext1 a
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply, inv_apply']
  have H := Complex.norm_eq_one_of_mem_rootsOfUnity <| φ.val_mem_rootsOfUnity a hR
  exact (Complex.inv_eq_conj H).symm
/-
**AddChar.starComp_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：starComp_apply (hR : 0 < ringChar R) {φ : AddChar R Complex} (a : R) : (st
arRingEnd Complex) (φ a) = φ⁻¹ a
参数：hR : 0 < ringChar R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddChar.starComp_eq_inv`：starComp_eq_inv (hR : 0 < ringChar R) {φ : AddC
har R Complex} : (starRingEnd Complex).compAddChar φ = φ⁻¹
-/
lemma starComp_apply (hR : 0 < ringChar R) {φ : AddChar R ℂ} (a : R) :
    (starRingEnd ℂ) (φ a) = φ⁻¹ a := by
  rw [← starComp_eq_inv hR]
  rfl

end Ring

end AddChar

