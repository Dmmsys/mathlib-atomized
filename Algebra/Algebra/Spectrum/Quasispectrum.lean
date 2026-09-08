/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Algebra.Unitization

/-!
# Quasiregularity and quasispectrum

For a non-unital ring `R`, an element `r : R` is *quasiregular* if it is invertible in the monoid
`(R, ∘)` where `x ∘ y := y + x + x * y` with identity `0 : R`. We implement this both as a type
synonym `PreQuasiregular` which has an associated `Monoid` instance (note: *not* an `AddMonoid`
instance despite the fact that `0 : R` is the identity in this monoid) so that one may access
the quasiregular elements of `R` as `(PreQuasiregular R)ˣ`, but also as a predicate
`IsQuasiregular`.

Quasiregularity is closely tied to invertibility. Indeed, `(PreQuasiregular A)ˣ` is isomorphic to
the subgroup of `Unitization R A` whose scalar part is `1`, whenever `A` is a non-unital
`R`-algebra, and moreover this isomorphism is implemented by the map
`(x : A) ↦ (1 + x : Unitization R A)`. It is because of this isomorphism, and the associated ties
with multiplicative invertibility, that we choose a `Monoid` (as opposed to an `AddMonoid`)
structure on `PreQuasiregular`.  In addition, in unital rings, we even have
`IsQuasiregular x ↔ IsUnit (1 + x)`.

The *quasispectrum* of `a : A` (with respect to `R`) is defined in terms of quasiregularity, and
this is the natural analogue of the `spectrum` for non-unital rings. Indeed, it is true that
`quasispectrum R a = spectrum R a ∪ {0}` when `A` is unital.

In Mathlib, the quasispectrum is the domain of the continuous functions associated to the
*non-unital* continuous functional calculus.

## Main definitions

+ `PreQuasiregular R`: a structure wrapping `R` that inherits a distinct `Monoid` instance when `R`
  is a non-unital semiring.
+ `Unitization.unitsFstOne`: the subgroup with carrier `{ x : (Unitization R A)ˣ | x.fst = 1 }`.
+ `unitsFstOne_mulEquiv_quasiregular`: the group isomorphism between
  `Unitization.unitsFstOne` and the units of `PreQuasiregular` (i.e., the quasiregular elements)
  which sends `(1, x) ↦ x`.
+ `IsQuasiregular x`: the proposition that `x : R` is a unit with respect to the monoid structure on
  `PreQuasiregular R`, i.e., there is some `u : (PreQuasiregular R)ˣ` such that `u.val` is
  identified with `x` (via the natural equivalence between `R` and `PreQuasiregular R`).
+ `quasispectrum R a`: in an algebra over the semifield `R`, this is the set
  `{r : R | (hr : IsUnit r) → ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}`, which should be thought of
  as a version of the `spectrum` which is applicable in non-unital algebras.

## Main theorems

+ `isQuasiregular_iff_isUnit`: in a unital ring, `x` is quasiregular if and only if `1 + x` is
  a unit.
+ `quasispectrum_eq_spectrum_union_zero`: in a unital algebra `A` over a semifield `R`, the
  quasispectrum of `a : A` is the `spectrum` with zero added.
+ `Unitization.isQuasiregular_inr_iff`: `a : A` is quasiregular if and only if it is quasiregular
  in `Unitization R A` (via the coercion `Unitization.inr`).
+ `Unitization.quasispectrum_eq_spectrum_inr`: the quasispectrum of `a` in a non-unital `R`-algebra
  `A` is precisely the spectrum of `a` in `Unitization R A` (via the coercion `Unitization.inr`).
-/

@[expose] public section

/-- A type synonym for non-unital rings where an alternative monoid structure is introduced.
If `R` is a non-unital semiring, then `PreQuasiregular R` is equipped with the monoid structure
with binary operation `fun x y ↦ y + x + x * y` and identity `0`. Elements of `R` which are
invertible in this monoid satisfy the predicate `IsQuasiregular`. -/
/-
**PreQuasiregular** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for non-unital rings where an alternative monoid structure is int
roduced.
If `R` is a non-unital semiring, then `PreQuasiregular R` is equipped with the m
onoid structure
with binary operation `fun x y ↦ y + x + x * y` and identity `0`. Elements of `R
` which are
invertible in this monoid satisfy the predicate `IsQuasiregular`.
-/
structure PreQuasiregular (R : Type*) where
  /-- The value wrapped into a term of `PreQuasiregular`. -/
  val : R

namespace PreQuasiregular

variable {R : Type*} [NonUnitalSemiring R]

/-- The identity map between `R` and `PreQuasiregular R`. -/
@[simps]
/-
**PreQuasiregular.equiv** 是 Mathlib 中的一个定义，位于命名空间 `PreQuasiregular`。
形式化陈述：equiv : R ≃ PreQuasiregular R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map between `R` and `PreQuasiregular R`.
-/
def equiv : R ≃ PreQuasiregular R where
  toFun := .mk
  invFun := PreQuasiregular.val
/-
**PreQuasiregular.instOne** 是 Mathlib 中的一个实例，位于命名空间 `PreQuasiregular`。
形式化陈述：instOne : One (PreQuasiregular R) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne : One (PreQuasiregular R) where
  one := equiv 0

@[simp]
/-
**PreQuasiregular.val_one** 是 Mathlib 中的一个引理，位于命名空间 `PreQuasiregular`。
形式化陈述：val_one : (1 : PreQuasiregular R).val = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_one : (1 : PreQuasiregular R).val = 0 := rfl
/-
**PreQuasiregular.instMul** 是 Mathlib 中的一个实例，位于命名空间 `PreQuasiregular`。
形式化陈述：instMul : Mul (PreQuasiregular R) where mul x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMul : Mul (PreQuasiregular R) where
  mul x y := .mk (y.val + x.val + x.val * y.val)

@[simp]
/-
**PreQuasiregular.val_mul** 是 Mathlib 中的一个引理，位于命名空间 `PreQuasiregular`。
形式化陈述：val_mul (x y : PreQuasiregular R) : (x * y).val = y.val + x.val + x.val * 
y.val
参数：x y : PreQuasiregular R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_mul (x y : PreQuasiregular R) : (x * y).val = y.val + x.val + x.val * y.val := rfl
/-
**PreQuasiregular.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `PreQuasiregular`。
形式化陈述：instMonoid : Monoid (PreQuasiregular R) where one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid : Monoid (PreQuasiregular R) where
  one := equiv 0
  mul x y := .mk (y.val + x.val + x.val * y.val)
  mul_one _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  one_mul _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  mul_assoc x y z := equiv.symm.injective <| by simp [mul_add, add_mul, mul_assoc]; abel

@[simp]
/-
**PreQuasiregular.inv_add_add_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `PreQuasireg
ular`。
形式化陈述：inv_add_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) : u⁻¹.val.val + u.val.v
al + u.val.val * u⁻¹.val.val = 0
参数：u : (PreQuasiregular R)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
lemma inv_add_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0 := by
  simpa [-Units.mul_inv] using congr($(u.mul_inv).val)

@[simp]
/-
**PreQuasiregular.add_inv_add_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `PreQuasireg
ular`。
形式化陈述：add_inv_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) : u.val.val + u⁻¹.val.v
al + u⁻¹.val.val * u.val.val = 0
参数：u : (PreQuasiregular R)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
-/
lemma add_inv_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0 := by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

end PreQuasiregular

namespace Unitization
open PreQuasiregular

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

variable (R A) in
/-- The subgroup of the units of `Unitization R A` whose scalar part is `1`. -/
/-
**Unitization.unitsFstOne** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：unitsFstOne : Subgroup (Unitization R A)ˣ where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of the units of `Unitization R A` whose scalar part is `1`.
-/
def unitsFstOne : Subgroup (Unitization R A)ˣ where
  carrier := {x | x.val.fst = 1}
  one_mem' := rfl
  mul_mem' {x} {y} (hx : x.val.fst = 1) (hy : y.val.fst = 1) := by simp [hx, hy]
  inv_mem' {x} (hx : x.val.fst = 1) := by
    simpa [-Units.mul_inv, hx] using congr(fstHom R A $(x.mul_inv))

@[simp]
/-
**Unitization.mem_unitsFstOne** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：mem_unitsFstOne {x : (Unitization R A)ˣ} : x in unitsFstOne R A ↔ x.val.fs
t = 1
参数：Unitization R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_unitsFstOne {x : (Unitization R A)ˣ} : x ∈ unitsFstOne R A ↔ x.val.fst = 1 := Iff.rfl

@[simp]
/-
**Unitization.unitsFstOne_val_val_fst** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：unitsFstOne_val_val_fst (x : (unitsFstOne R A)) : x.val.val.fst = 1
参数：x : (unitsFstOne R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Unitization.mem_unitsFstOne`：mem_unitsFstOne {x : (Unitization R A)ˣ} : 
x in unitsFstOne R A ↔ x.val.fst = 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma unitsFstOne_val_val_fst (x : (unitsFstOne R A)) : x.val.val.fst = 1 :=
  mem_unitsFstOne.mp x.property

@[simp]
/-
**Unitization.unitsFstOne_val_inv_val_fst** 是 Mathlib 中的一个引理，位于命名空间 `Unitization
`。
形式化陈述：unitsFstOne_val_inv_val_fst (x : (unitsFstOne R A)) : x.val⁻¹.val.fst = 1
参数：x : (unitsFstOne R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Unitization.mem_unitsFstOne`：mem_unitsFstOne {x : (Unitization R A)ˣ} : 
x in unitsFstOne R A ↔ x.val.fst = 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma unitsFstOne_val_inv_val_fst (x : (unitsFstOne R A)) : x.val⁻¹.val.fst = 1 :=
  mem_unitsFstOne.mp x⁻¹.property

variable (R) in
/-- If `A` is a non-unital `R`-algebra, then the subgroup of units of `Unitization R A` whose
scalar part is `1 : R` (i.e., `Unitization.unitsFstOne`) is isomorphic to the group of units of
`PreQuasiregular A`. -/
@[simps]
/-
**Unitization.unitsFstOne_mulEquiv_quasiregular** 是 Mathlib 中的一个定义，位于命名空间 `Uniti
zation`。
形式化陈述：unitsFstOne_mulEquiv_quasiregular : unitsFstOne R A ≃* (PreQuasiregular A)
ˣ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `A` is a non-unital `R`-algebra, then the subgroup of units of `Unitization R
 A` whose
scalar part is `1 : R` (i.e., `Unitization.unitsFstOne`) is isomorphic to the gr
oup of units of
`PreQuasiregular A`.
-/
def unitsFstOne_mulEquiv_quasiregular : unitsFstOne R A ≃* (PreQuasiregular A)ˣ where
  toFun x :=
    { val := PreQuasiregular.equiv x.val.val.snd
      inv := PreQuasiregular.equiv x⁻¹.val.val.snd
      val_inv := PreQuasiregular.equiv.symm.injective <| by
        simpa [-Units.mul_inv] using congr($(x.val.mul_inv).snd)
      inv_val := PreQuasiregular.equiv.symm.injective <| by
        simpa [-Units.inv_mul] using congr($(x.val.inv_mul).snd) }
  invFun x :=
    { val :=
      { val := 1 + PreQuasiregular.equiv.symm x.val
        inv := 1 + PreQuasiregular.equiv.symm x⁻¹.val
        val_inv := by
          convert congr((1 + $(inv_add_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero]
        inv_val := by
          convert congr((1 + $(add_inv_add_mul_eq_zero x) : Unitization R A))
          · simp only [mul_one, PreQuasiregular.equiv_symm_apply, one_mul, mul_add,
              add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero] }
      property := by simp }
  left_inv x := Subtype.ext <| Units.ext <| by simpa using x.val.val.inl_fst_add_inr_snd_eq
  right_inv x := Units.ext <| by simp [-PreQuasiregular.equiv_symm_apply]
  map_mul' x y := Units.ext <| PreQuasiregular.equiv.symm.injective <| by simp

end Unitization

section PreQuasiregular

open PreQuasiregular

variable {R : Type*} [NonUnitalSemiring R]

/-- In a non-unital semiring `R`, an element `x : R` satisfies `IsQuasiregular` if it is a unit
under the monoid operation `fun x y ↦ y + x + x * y`. -/
/-
**IsQuasiregular** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsQuasiregular (x : R) : Prop
参数：x : R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
In a non-unital semiring `R`, an element `x : R` satisfies `IsQuasiregular` if i
t is a unit
under the monoid operation `fun x y ↦ y + x + x * y`.
-/
def IsQuasiregular (x : R) : Prop :=
  ∃ u : (PreQuasiregular R)ˣ, equiv.symm u.val = x

@[simp]
/-
**isQuasiregular_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuasiregular_zero : IsQuasiregular 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isQuasiregular_zero : IsQuasiregular 0 := ⟨1, rfl⟩
/-
**isQuasiregular_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuasiregular_iff {x : R} : IsQuasiregular x ↔ exists y, y + x + x * y = 
0 ∧ x + y + y * x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PreQuasiregular.equiv_symm_apply`：∀ {R : Type u_1} (self : PreQuasiregul
ar R), PreQuasiregular.equiv.symm self = self.val
· 使用引理 `PreQuasiregular.inv_add_add_mul_eq_zero`：inv_add_add_mul_eq_zero (u : (P
reQuasiregular R)ˣ) : u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `PreQuasiregular.add_inv_add_mul_eq_zero`：add_inv_add_mul_eq_zero (u : (P
reQuasiregular R)ˣ) : u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma isQuasiregular_iff {x : R} :
    IsQuasiregular x ↔ ∃ y, y + x + x * y = 0 ∧ x + y + y * x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨equiv.symm u⁻¹.val, by simp⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨equiv x, equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply equiv.symm.injective
      assumption
/-
**isQuasiregular_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuasiregular_iff' {x : R} : IsQuasiregular x ↔ IsUnit (PreQuasiregular.e
quiv x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isQuasiregular_iff' {x : R} : IsQuasiregular x ↔ IsUnit (PreQuasiregular.equiv x) := by
  simp only [IsQuasiregular, IsUnit, Equiv.apply_symm_apply,
    ← PreQuasiregular.equiv (R := R).injective.eq_iff]

end PreQuasiregular

/-
**IsQuasiregular.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsQuasiregular.map {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemirin
g S] [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) {x : R} (hx : IsQuasi
regular x) : IsQuasiregular (f x)
参数：f : F；hx : IsQuasiregular x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isQuasiregular_iff`：isQuasiregular_iff {x : R} : IsQuasiregular x ↔ exis
ts y, y + x + x * y = 0 ∧ x + y + y * x = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
-/
lemma IsQuasiregular.map {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) {x : R} (hx : IsQuasiregular x) :
    IsQuasiregular (f x) := by
  rw [isQuasiregular_iff] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨f y, by simpa using And.intro congr(f $(hy₁)) congr(f $(hy₂))⟩
/-
**IsQuasiregular.isUnit_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsQuasiregular.isUnit_one_add {R : Type*} [Semiring R] {x : R} (hx : IsQua
siregular x) : IsUnit (1 + x)
参数：hx : IsQuasiregular x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isQuasiregular_iff`：isQuasiregular_iff {x : R} : IsQuasiregular x ↔ exis
ts y, y + x + x * y = 0 ∧ x + y + y * x = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `_private.Mathlib.Algebra.Algebra.Spectrum.Quasispectrum.0.IsQuasiregular
.isUnit_one_add._abel_1_1`：∀ {R : Type u_1} [inst : Semiring R] {x : R} (y : R),
 1 + x + (y + x * y) = 1 + (y + x + x * y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.Algebra.Algebra.Spectrum.Quasispectrum.0.IsQuasiregular
.isUnit_one_add._abel_1_2`：∀ {R : Type u_1} [inst : Semiring R] {x : R} (y : R),
 1 + y + (x + y * x) = 1 + (x + y + y * x)
-/
lemma IsQuasiregular.isUnit_one_add {R : Type*} [Semiring R] {x : R} (hx : IsQuasiregular x) :
    IsUnit (1 + x) := by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) <;> [noncomm_ring; simp]
  · convert congr(1 + $(hy₂)) <;> [noncomm_ring; simp]
/-
**isQuasiregular_iff_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuasiregular_iff_isUnit {R : Type*} [Ring R] {x : R} : IsQuasiregular x 
↔ IsUnit (1 + x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsQuasiregular.isUnit_one_add`：IsQuasiregular.isUnit_one_add {R : Type*}
 [Semiring R] {x : R} (hx : IsQuasiregular x) : IsUnit (1 + x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isQuasiregular_iff`：isQuasiregular_iff {x : R} : IsQuasiregular x ↔ exis
ts y, y + x + x * y = 0 ∧ x + y + y * x = 0
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `_private.Mathlib.Algebra.Algebra.Spectrum.Quasispectrum.0.isQuasiregular
_iff_isUnit._abel_1_2`：∀ {R : Type u_1} [inst : Ring R] {x : R} (hx : IsUnit (1 
+ x)),   ↑hx.unit⁻¹ + -1 + x + (x * ↑hx.unit⁻¹ + -x) = ↑hx.unit⁻¹ + x * ↑hx.unit
⁻¹ …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `_private.Mathlib.Algebra.Algebra.Spectrum.Quasispectrum.0.isQuasiregular
_iff_isUnit._abel_1_1`：∀ {R : Type u_1} [inst : Ring R] {x : R} (hx : IsUnit (1 
+ x)),   x + (↑hx.unit⁻¹ + -1) + (↑hx.unit⁻¹ * x + -x) = ↑hx.unit⁻¹ + -1 + 1 + (
↑hx…
-/
lemma isQuasiregular_iff_isUnit {R : Type*} [Ring R] {x : R} :
    IsQuasiregular x ↔ IsUnit (1 + x) := by
  refine ⟨IsQuasiregular.isUnit_one_add, fun hx ↦ ?_⟩
  rw [isQuasiregular_iff]
  use hx.unit⁻¹ - 1
  constructor
  case' h.left => have := congr($(hx.mul_val_inv) - 1)
  case' h.right => have := congr($(hx.val_inv_mul) - 1)
  all_goals
    rw [← sub_add_cancel (↑hx.unit⁻¹ : R) 1, sub_self] at this
    convert this
    noncomm_ring

-- interestingly, this holds even in the semiring case.
/-
**isQuasiregular_iff_isUnit'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isQuasiregular_iff_isUnit' (R : Type*) {A : Type*} [CommSemiring R] [NonUn
italSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {x : A}
 : IsQuasiregular x ↔ IsUnit (1 + x : Unitization R A)
参数：R : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Unitization.val_unitsFstOne_mulEquiv_quasiregular_apply`：∀ (R : Type u_1
) {A : Type u_2} [inst : CommSemiring R] [inst_1 : NonUnitalSemiring A] [inst_2 
: _root_.Module R A]   [inst_3 : IsScalarTowe…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma isQuasiregular_iff_isUnit' (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {x : A} :
    IsQuasiregular x ↔ IsUnit (1 + x : Unitization R A) := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨u, rfl⟩
    exact (Unitization.unitsFstOne_mulEquiv_quasiregular R).symm u |>.val.isUnit
  · exact ⟨(Unitization.unitsFstOne_mulEquiv_quasiregular R) ⟨hx.unit, by simp⟩, by simp⟩

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A]

/-- If `A` is a non-unital `R`-algebra, the `R`-quasispectrum of `a : A` consists of those `r : R`
such that if `r` is invertible (in `R`), then `-(r⁻¹ • a)` is not quasiregular.

The quasispectrum is precisely the spectrum in the unitization when `R` is a commutative ring.
See `Unitization.quasispectrum_eq_spectrum_inr`. -/
/-
**quasispectrum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：quasispectrum (a : A) : Set R
参数：a : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a non-unital `R`-algebra, the `R`-quasispectrum of `a : A` consists of
 those `r : R`
such that if `r` is invertible (in `R`), then `-(r⁻¹ • a)` is not quasiregular.

The quasispectrum is precisely the spectrum in the unitization when `R` is a com
mutative ring.
See `Unitization.quasispectrum_eq_spectrum_inr`.
-/
def quasispectrum (a : A) : Set R :=
  {r : R | (hr : IsUnit r) → ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}

variable {R} in
/-
**quasispectrum.not_isUnit_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum.not_isUnit_mem (a : A) {r : R} (hr : ¬ IsUnit r) : r in quas
ispectrum R a
参数：a : A；hr : ¬ IsUnit r。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasispectrum.not_isUnit_mem (a : A) {r : R} (hr : ¬ IsUnit r) : r ∈ quasispectrum R a :=
  fun hr' ↦ (hr hr').elim

@[simp]
/-
**quasispectrum.zero_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum.zero_mem [Nontrivial R] (a : A) : 0 in quasispectrum R a
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `quasispectrum.not_isUnit_mem`：quasispectrum.not_isUnit_mem (a : A) {r : 
R} (hr : ¬ IsUnit r) : r in quasispectrum R a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma quasispectrum.zero_mem [Nontrivial R] (a : A) : 0 ∈ quasispectrum R a :=
  quasispectrum.not_isUnit_mem a <| by simp
/-
**quasispectrum.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasispectrum.nonempty [Nontrivial R] (a : A) : (quasispectrum R a).Nonemp
ty
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用引理 `quasispectrum.zero_mem`：quasispectrum.zero_mem [Nontrivial R] (a : A) : 
0 in quasispectrum R a
-/
theorem quasispectrum.nonempty [Nontrivial R] (a : A) : (quasispectrum R a).Nonempty :=
  Set.nonempty_of_mem <| quasispectrum.zero_mem R a
/-
**quasispectrum.instZero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：quasispectrum.instZero [Nontrivial R] (a : A) : Zero (quasispectrum R a) w
here zero
参数：a : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `quasispectrum.zero_mem`：quasispectrum.zero_mem [Nontrivial R] (a : A) : 
0 in quasispectrum R a
-/
instance quasispectrum.instZero [Nontrivial R] (a : A) : Zero (quasispectrum R a) where
  zero := ⟨0, quasispectrum.zero_mem R a⟩

variable {R}

set_option backward.isDefEq.respectTransparency false in
/-- A version of `NonUnitalAlgHom.quasispectrum_apply_subset` which allows for `quasispectrum R`,
where `R` is a *semi*ring, but `φ` must still function over a scalar ring `S`. In this case, we
need `S` to be explicit. The primary use case is, for instance, `R := ℝ≥0` and `S := ℝ` or
`S := ℂ`. -/
/-
**NonUnitalAlgHom.quasispectrum_apply_subset'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NonUnitalAlgHom.quasispectrum_apply_subset' {F R : Type*} (S : Type*) {A B
 : Type*} [CommSemiring R] [Semiring S] [NonUnitalRing A] [NonUnitalRing B] [Mod
ule R S] [Module S A] [Module R A] [Module S B] [Module R B] [IsScalarTower R S 
A] [IsScalarTower R S B] [FunLike F A B] [NonUnitalAlgHomClass F S A B] (φ : F) 
(a : A) : quasispectrum R (φ a) subseteq quasispectrum R a
参数：S : Type*；φ : F；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用引理 `IsQuasiregular.map`：IsQuasiregular.map {F R S : Type*} [NonUnitalSemirin
g R] [NonUnitalSemiring S] [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F)
 {x : R}…
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …

--- 原说明 ---
A version of `NonUnitalAlgHom.quasispectrum_apply_subset` which allows for `quas
ispectrum R`,
where `R` is a *semi*ring, but `φ` must still function over a scalar ring `S`. I
n this case, we
need `S` to be explicit. The primary use case is, for instance, `R := ℝ≥0` and `
S := ℝ` or
`S := ℂ`.
-/
lemma NonUnitalAlgHom.quasispectrum_apply_subset' {F R : Type*} (S : Type*) {A B : Type*}
    [CommSemiring R] [Semiring S] [NonUnitalRing A] [NonUnitalRing B] [Module R S]
    [Module S A] [Module R A] [Module S B] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B]
    [FunLike F A B] [NonUnitalAlgHomClass F S A B] (φ : F) (a : A) :
    quasispectrum R (φ a) ⊆ quasispectrum R a := by
  refine Set.compl_subset_compl.mp fun x ↦ ?_
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
    forall_exists_index]
  refine fun hx this ↦ ⟨hx, ?_⟩
  rw [Units.smul_def, ← smul_one_smul S] at this ⊢
  simpa [-smul_assoc] using this.map φ

/-- If `φ` is non-unital algebra homomorphism over a scalar ring `R`, then
`quasispectrum R (φ a) ⊆ quasispectrum R a`. -/
/-
**NonUnitalAlgHom.quasispectrum_apply_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NonUnitalAlgHom.quasispectrum_apply_subset {F R A B : Type*} [CommRing R] 
[NonUnitalRing A] [NonUnitalRing B] [Module R A] [Module R B] [FunLike F A B] [N
onUnitalAlgHomClass F R A B] (φ : F) (a : A) : quasispectrum R (φ a) subseteq qu
asispectrum R a
参数：φ : F；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalAlgHom.quasispectrum_apply_subset'`：NonUnitalAlgHom.quasispectr
um_apply_subset' {F R : Type*} (S : Type*) {A B : Type*} [CommSemiring R] [Semir
ing S] [NonUnitalRing A] [NonUnit…

--- 原说明 ---
If `φ` is non-unital algebra homomorphism over a scalar ring `R`, then
`quasispectrum R (φ a) ⊆ quasispectrum R a`.
-/
lemma NonUnitalAlgHom.quasispectrum_apply_subset {F R A B : Type*}
    [CommRing R] [NonUnitalRing A] [NonUnitalRing B] [Module R A] [Module R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (φ : F) (a : A) :
    quasispectrum R (φ a) ⊆ quasispectrum R a :=
  NonUnitalAlgHom.quasispectrum_apply_subset' R φ a

@[simp]
/-
**quasispectrum.coe_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum.coe_zero [Nontrivial R] (a : A) : (0 : quasispectrum R a) = 
(0 : R)
参数：a : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasispectrum.coe_zero [Nontrivial R] (a : A) : (0 : quasispectrum R a) = (0 : R) := rfl
/-
**quasispectrum.mem_of_not_quasiregular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum.mem_of_not_quasiregular (a : A) {r : Rˣ} (hr : ¬ IsQuasiregu
lar (-(r⁻¹ • a))) : (r : R) in quasispectrum R a
参数：a : A；hr : ¬ IsQuasiregular (-(r⁻¹ • a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.unit_of_val_units`：unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)
) : h.unit = a
-/
lemma quasispectrum.mem_of_not_quasiregular (a : A) {r : Rˣ}
    (hr : ¬ IsQuasiregular (-(r⁻¹ • a))) : (r : R) ∈ quasispectrum R a :=
  fun _ ↦ by simpa using hr
/-
**quasispectrum_eq_spectrum_union** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum_eq_spectrum_union (R : Type*) {A : Type*} [CommSemiring R] [
Ring A] [Algebra R A] (a : A) : quasispectrum R a = spectrum R a union {r : R | 
¬ IsUnit r}
参数：R : Type*；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quasispectrum.eq_1`：∀ (R : Type u_1) {A : Type u_2} [inst : CommSemiring
 R] [inst_1 : NonUnitalRing A] [inst_2 : _root_.Module R A] (a : A),   quasispec
trum R a…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `isQuasiregular_iff_isUnit`：isQuasiregular_iff_isUnit {R : Type*} [Ring R
] {x : R} : IsQuasiregular x ↔ IsUnit (1 + x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `IsUnit.smul_sub_iff_sub_inv_smul`：IsUnit.smul_sub_iff_sub_inv_smul [Grou
p G] [Monoid R] [AddGroup R] [DistribMulAction G R] [IsScalarTower G R R] [SMulC
ommClass G R R] (r : G…
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma quasispectrum_eq_spectrum_union (R : Type*) {A : Type*} [CommSemiring R]
    [Ring A] [Algebra R A] (a : A) : quasispectrum R a = spectrum R a ∪ {r : R | ¬ IsUnit r} := by
  ext r
  rw [quasispectrum]
  simp only [Set.mem_ofPred_eq, Set.mem_union, ← imp_iff_or_not, spectrum.mem_iff]
  congr! 1 with hr
  rw [not_iff_not, isQuasiregular_iff_isUnit, ← sub_eq_add_neg, Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.smul_sub_iff_sub_inv_smul hr.unit a).symm
/-
**spectrum_subset_quasispectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_subset_quasispectrum (R : Type*) {A : Type*} [CommSemiring R] [Ri
ng A] [Algebra R A] (a : A) : spectrum R a subseteq quasispectrum R a
参数：R : Type*；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `quasispectrum_eq_spectrum_union`：quasispectrum_eq_spectrum_union (R : Ty
pe*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A] (a : A) : quasispectrum
 R a = spectrum R a u…
-/
lemma spectrum_subset_quasispectrum (R : Type*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    (a : A) : spectrum R a ⊆ quasispectrum R a :=
  quasispectrum_eq_spectrum_union R a ▸ Set.subset_union_left
/-
**quasispectrum_eq_spectrum_union_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum_eq_spectrum_union_zero (R : Type*) {A : Type*} [Semifield R]
 [Ring A] [Algebra R A] (a : A) : quasispectrum R a = spectrum R a union {0}
参数：R : Type*；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `quasispectrum_eq_spectrum_union`：quasispectrum_eq_spectrum_union (R : Ty
pe*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A] (a : A) : quasispectrum
 R a = spectrum R a u…
-/
lemma quasispectrum_eq_spectrum_union_zero (R : Type*) {A : Type*} [Semifield R] [Ring A]
    [Algebra R A] (a : A) : quasispectrum R a = spectrum R a ∪ {0} := by
  convert! quasispectrum_eq_spectrum_union R a
  simp
/-
**mem_quasispectrum_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_quasispectrum_iff {R A : Type*} [Semifield R] [Ring A] [Algebra R A] {
a : A} {x : R} : x in quasispectrum R a ↔ x = 0 ∨ x in spectrum R a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_quasispectrum_iff {R A : Type*} [Semifield R] [Ring A]
    [Algebra R A] {a : A} {x : R} :
    x ∈ quasispectrum R a ↔ x = 0 ∨ x ∈ spectrum R a := by
  simp [quasispectrum_eq_spectrum_union_zero]

namespace Unitization
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-
**Unitization.isQuasiregular_inr_iff** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：isQuasiregular_inr_iff (a : A) : IsQuasiregular (a : Unitization R A) ↔ Is
Quasiregular a
参数：a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isQuasiregular_iff`：isQuasiregular_iff {x : R} : IsQuasiregular x ↔ exis
ts y, y + x + x * y = 0 ∧ x + y + y * x = 0
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitization.fstHom_apply`：∀ (R : Type u_2) (A : Type u_3) [inst : CommSe
miring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A]   [inst_3 
: IsScalarTowe…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Unitization.inr_injective`：inr_injective [Zero R] : Function.Injective (
(↑) : A -> Unitization R A)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Unitization.inr_add`：inr_add [AddZeroClass R] [Add A] (m₁ m₂ : A) : (↑(m
₁ + m₂) : Unitization R A) = m₁ + m₂
· 使用定理 `Unitization.inr_mul`：inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [
SMulWithZero R A] (a₁ a₂ : A) : (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂
· 使用引理 `IsQuasiregular.map`：IsQuasiregular.map {F R S : Type*} [NonUnitalSemirin
g R] [NonUnitalSemiring S] [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F)
 {x : R}…
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
-/
lemma isQuasiregular_inr_iff (a : A) :
    IsQuasiregular (a : Unitization R A) ↔ IsQuasiregular a := by
  refine ⟨fun ha ↦ ?_, IsQuasiregular.map (inrNonUnitalAlgHom R A)⟩
  rw [isQuasiregular_iff] at ha ⊢
  obtain ⟨y, hy₁, hy₂⟩ := ha
  lift y to A using by simpa using congr(fstHom R A $(hy₁))
  refine ⟨y, ?_, ?_⟩ <;> exact inr_injective (R := R) <| by simpa
/-
**Unitization.zero_mem_spectrum_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：zero_mem_spectrum_inr (R S : Type*) {A : Type*} [CommSemiring R] [CommRing
 S] [Nontrivial S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S
 A A] [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) : 0 in sp
ectrum R (a : Unitization S A)
参数：R S : Type*；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.zero_mem_iff`：zero_mem_iff {a : A} : (0 : R) in σ a ↔ ¬IsUnit a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
-/
lemma zero_mem_spectrum_inr (R S : Type*) {A : Type*} [CommSemiring R]
    [CommRing S] [Nontrivial S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    0 ∈ spectrum R (a : Unitization S A) := by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  simpa [-Units.mul_inv, hu] using congr($(u.mul_inv).fst)
/-
**Unitization.mem_spectrum_inr_of_not_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Unitizat
ion`。
形式化陈述：mem_spectrum_inr_of_not_isUnit {R A : Type*} [CommRing R] [NonUnitalRing A
] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a : A) (r : R) (hr :
 ¬ IsUnit r) : r in spectrum R (a : Unitization R A)
参数：a : A；r : R；hr : ¬ IsUnit r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Unitization.fstHom_apply`：∀ (R : Type u_2) (A : Type u_3) [inst : CommSe
miring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A]   [inst_3 
: IsScalarTowe…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
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
lemma mem_spectrum_inr_of_not_isUnit {R A : Type*} [CommRing R]
    [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (a : A) (r : R) (hr : ¬ IsUnit r) : r ∈ spectrum R (a : Unitization R A) :=
  fun h ↦ hr <| by simpa [map_sub] using h.map (fstHom R A)
/-
**Unitization.quasispectrum_eq_spectrum_inr** 是 Mathlib 中的一个引理，位于命名空间 `Unitizati
on`。
形式化陈述：quasispectrum_eq_spectrum_inr (R : Type*) {A : Type*} [CommRing R] [NonUni
talRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a : A) : qu
asispectrum R a = spectrum R (a : Unitization R A)
参数：R : Type*；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Unitization.mem_spectrum_inr_of_not_isUnit`：mem_spectrum_inr_of_not_isUn
it {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTower R A 
A] [SMulCommClass R A A] (a : A)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_eq_left`：union_eq_left {s t : Set α} : s union t = s ↔ t subse
teq s
· 使用引理 `quasispectrum_eq_spectrum_union`：quasispectrum_eq_spectrum_union (R : Ty
pe*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A] (a : A) : quasispectrum
 R a = spectrum R a u…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Unitization.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (
r : S) (m : A) : (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
· 使用定理 `Unitization.inr_neg`：inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Uni
tization R A) = -m
· 使用引理 `Unitization.isQuasiregular_inr_iff`：isQuasiregular_inr_iff (a : A) : IsQ
uasiregular (a : Unitization R A) ↔ IsQuasiregular a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasispectrum_eq_spectrum_inr (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization R A) := by
  ext r
  have : { r | ¬ IsUnit r} ⊆ spectrum R _ := mem_spectrum_inr_of_not_isUnit a
  rw [← Set.union_eq_left.mpr this, ← quasispectrum_eq_spectrum_union]
  apply forall_congr' fun hr ↦ ?_
  rw [not_iff_not, Units.smul_def, Units.smul_def, ← inr_smul, ← inr_neg, isQuasiregular_inr_iff]
/-
**Unitization.quasispectrum_eq_spectrum_inr'** 是 Mathlib 中的一个引理，位于命名空间 `Unitizat
ion`。
形式化陈述：quasispectrum_eq_spectrum_inr' (R S : Type*) {A : Type*} [Semifield R] [Fi
eld S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A] [SMulC
ommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) : quasispectrum R a =
 spectrum R (a : Unitization S A)
参数：R S : Type*；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `Unitization.zero_mem_spectrum_inr`：zero_mem_spectrum_inr (R S : Type*) {
A : Type*} [CommSemiring R] [CommRing S] [Nontrivial S] [NonUnitalRing A] [Algeb
ra R S] [Module S A] [I…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Unitization.inr_smul`：inr_smul [Zero R] [SMulZeroClass S R] [SMul S A] (
r : S) (m : A) : (↑(r • m) : Unitization R A) = r • (m : Unitization R A)
· 使用定理 `Unitization.inr_neg`：inr_neg [AddGroup R] [Neg A] (m : A) : (↑(-m) : Uni
tization R A) = -m
· 使用引理 `Unitization.isQuasiregular_inr_iff`：isQuasiregular_inr_iff (a : A) : IsQ
uasiregular (a : Unitization R A) ↔ IsQuasiregular a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasispectrum_eq_spectrum_inr' (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization S A) := by
  ext r
  have := Set.singleton_subset_iff.mpr (zero_mem_spectrum_inr R S a)
  rw [← Set.union_eq_self_of_subset_right this, ← quasispectrum_eq_spectrum_union_zero]
  apply forall_congr' fun x ↦ ?_
  rw [not_iff_not, Units.smul_def, Units.smul_def, ← inr_smul, ← inr_neg, isQuasiregular_inr_iff]
/-
**Unitization.quasispectrum_inr_eq** 是 Mathlib 中的一个引理，位于命名空间 `Unitization`。
形式化陈述：quasispectrum_inr_eq (R S : Type*) {A : Type*} [Semifield R] [Field S] [No
nUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A] [SMulCommClass S
 A A] [Module R A] [IsScalarTower R S A] (a : A) : quasispectrum R (a : Unitizat
ion S A) = quasispectrum R a
参数：R S : Type*；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用引理 `Unitization.zero_mem_spectrum_inr`：zero_mem_spectrum_inr (R S : Type*) {
A : Type*} [CommSemiring R] [CommRing S] [Nontrivial S] [NonUnitalRing A] [Algeb
ra R S] [Module S A] [I…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
lemma quasispectrum_inr_eq (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R (a : Unitization S A) = quasispectrum R a := by
  rw [quasispectrum_eq_spectrum_union_zero, quasispectrum_eq_spectrum_inr' R S]
  simpa using zero_mem_spectrum_inr _ _ _

end Unitization

/-
**quasispectrum.mul_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrum.mul_comm {R A : Type*} [CommRing R] [NonUnitalRing A] [Modul
e R A] [IsScalarTower R A A] [SMulCommClass R A A] (a b : A) : quasispectrum R (
a * b) = quasispectrum R (b * a)
参数：a b : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr`：quasispectrum_eq_spectrum_inr
 (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTo
wer R A A] [SMulCommClass R A A…
· 使用定理 `Unitization.inr_mul`：inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [
SMulWithZero R A] (a₁ a₂ : A) : (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `spectrum.setOfPred_isUnit_inter_mul_comm`：setOfPred_isUnit_inter_mul_com
m (a b : A) : {r | IsUnit r} inter σ (a * b) = {r | IsUnit r} inter σ (b * a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用引理 `quasispectrum.not_isUnit_mem`：quasispectrum.not_isUnit_mem (a : A) {r : 
R} (hr : ¬ IsUnit r) : r in quasispectrum R a
-/
lemma quasispectrum.mul_comm {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (a b : A) :
    quasispectrum R (a * b) = quasispectrum R (b * a) := by
  rw [← Set.inter_union_compl (quasispectrum R (a * b)) {r | IsUnit r},
    ← Set.inter_union_compl (quasispectrum R (b * a)) {r | IsUnit r}]
  congr! 1
  · simpa [Set.inter_comm _ {r | IsUnit r}, Unitization.quasispectrum_eq_spectrum_inr,
      Unitization.inr_mul] using spectrum.setOfPred_isUnit_inter_mul_comm _ _
  · rw [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr]
    all_goals exact fun _ ↦ quasispectrum.not_isUnit_mem _

/-- A class for `𝕜`-algebras with a partial order where the ordering is compatible with the
(quasi)spectrum. -/
/-
**NonnegSpectrumClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_3) →   (A : Type u_4) →     [inst : CommSemiring 𝕜] →       [P
artialOrder 𝕜] → [inst_2 : NonUnitalRing A] → [PartialOrder A] → [_root_.Module 
𝕜 A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class for `𝕜`-algebras with a partial order where the ordering is compatible w
ith the
(quasi)spectrum.
-/
class NonnegSpectrumClass (𝕜 A : Type*) [CommSemiring 𝕜] [PartialOrder 𝕜]
    [NonUnitalRing A] [PartialOrder A]
    [Module 𝕜 A] : Prop where
  quasispectrum_nonneg_of_nonneg : ∀ a : A, 0 ≤ a → ∀ x ∈ quasispectrum 𝕜 a, 0 ≤ x

export NonnegSpectrumClass (quasispectrum_nonneg_of_nonneg)

namespace NonnegSpectrumClass

/-
**NonnegSpectrumClass.iff_spectrum_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `NonnegSpect
rumClass`。
形式化陈述：iff_spectrum_nonneg {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [
PartialOrder A] [Algebra 𝕜 A] : NonnegSpectrumClass 𝕜 A ↔ forall a : A, 0 <= a -
> forall x in spectrum 𝕜 a, 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iff_spectrum_nonneg {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] : NonnegSpectrumClass 𝕜 A ↔ ∀ a : A, 0 ≤ a → ∀ x ∈ spectrum 𝕜 a, 0 ≤ x := by
  simp [show NonnegSpectrumClass 𝕜 A ↔ _ from ⟨fun ⟨h⟩ ↦ h, (⟨·⟩)⟩,
    quasispectrum_eq_spectrum_union_zero]

alias ⟨_, of_spectrum_nonneg⟩ := iff_spectrum_nonneg
/-
**NonnegSpectrumClass.nonneg_of_mem_quasispectrum** 是 Mathlib 中的一个引理，位于命名空间 `Non
negSpectrumClass`。
形式化陈述：nonneg_of_mem_quasispectrum {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] 
[PartialOrder A] [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : 0 <= a) {x
 : 𝕜} (hx : x in quasispectrum 𝕜 a) : 0 <= x
参数：ha : 0 <= a；hx : x in quasispectrum 𝕜 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`：∀ {𝕜 : Type u_3} {A 
: Type u_4} {inst : CommSemiring 𝕜} {inst_1 : PartialOrder 𝕜} {inst_2 : NonUnita
lRing A}   {inst_3 : PartialOrder A} {in…
-/
lemma nonneg_of_mem_quasispectrum {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [PartialOrder A]
    [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : 0 ≤ a) {x : 𝕜}
    (hx : x ∈ quasispectrum 𝕜 a) : 0 ≤ x := quasispectrum_nonneg_of_nonneg a ha x hx

grind_pattern nonneg_of_mem_quasispectrum => x ∈ quasispectrum 𝕜 a

end NonnegSpectrumClass

/-
**spectrum_nonneg_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] 
[Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpectrumClass 𝕜 A] ⦃a : A⦄ (ha : 
0 <= a) ⦃x : 𝕜⦄ (hx : x in spectrum 𝕜 a) : 0 <= x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`：∀ {𝕜 : Type u_3} {A 
: Type u_4} {inst : CommSemiring 𝕜} {inst_1 : PartialOrder 𝕜} {inst_2 : NonUnita
lRing A}   {inst_3 : PartialOrder A} {in…
· 使用引理 `spectrum_subset_quasispectrum`：spectrum_subset_quasispectrum (R : Type*)
 {A : Type*} [CommSemiring R] [Ring A] [Algebra R A] (a : A) : spectrum R a subs
eteq quasispectrum …
-/
lemma spectrum_nonneg_of_nonneg {𝕜 A : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
    [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] [NonnegSpectrumClass 𝕜 A] ⦃a : A⦄ (ha : 0 ≤ a) ⦃x : 𝕜⦄ (hx : x ∈ spectrum 𝕜 a) :
    0 ≤ x :=
  NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg a ha x (spectrum_subset_quasispectrum 𝕜 a hx)

grind_pattern spectrum_nonneg_of_nonneg => x ∈ spectrum 𝕜 a

/-! ### Restriction of the spectrum -/

/-- Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, we say that
the spectrum of `a` restricts via a function `f : S → R` if `f` is a left inverse of
`algebraMap R S`, and `f` is a right inverse of `algebraMap R S` on `spectrum S a`.

For example, when `f = Complex.re` (so `S := ℂ` and `R := ℝ`), `SpectrumRestricts a f` means that
the `ℂ`-spectrum of `a` is contained within `ℝ`. This arises naturally when `a` is selfadjoint
and `A` is a C⋆-algebra.

This is the property allows us to restrict a continuous functional calculus over `S` to a
continuous functional calculus over `R`. -/
/-
**QuasispectrumRestricts** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {S : Type u_4} →     {A : Type u_5} →       [inst : Com
mSemiring R] →         [inst_1 : CommSemiring S] →           [inst_2 : NonUnital
Ring A] → [_root_.Module R A] → [_root_.Module S A] → [Algebra R S] → A → (S → R
) → Prop
参数：S → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, 
we say that
the spectrum of `a` restricts via a function `f : S → R` if `f` is a left invers
e of
`algebraMap R S`, and `f` is a right inverse of `algebraMap R S` on `spectrum S 
a`.

For example, when `f = Complex.re` (so `S := ℂ` and `R := ℝ`), `SpectrumRestrict
s a f` means that
the `ℂ`-spectrum of `a` is contained within `ℝ`. This arises naturally when `a` 
is selfadjoint
and `A` is a C⋆-algebra.

This is the property allows us to restrict a continuous functional calculus over
 `S` to a
continuous functional calculus over `R`.
-/
structure QuasispectrumRestricts
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S → R) : Prop where
  /-- `f` is a right inverse of `algebraMap R S` when restricted to `quasispectrum S a`. -/
  rightInvOn : (quasispectrum S a).RightInvOn f (algebraMap R S)
  /-- `f` is a left inverse of `algebraMap R S`. -/
  left_inv : Function.LeftInverse f (algebraMap R S)
/-
**quasispectrumRestricts_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：quasispectrumRestricts_iff {R S A : Type*} [CommSemiring R] [CommSemiring 
S] [NonUnitalRing A] [Module R A] [Module S A] [Algebra R S] (a : A) (f : S -> R
) : QuasispectrumRestricts a f ↔ (quasispectrum S a).RightInvOn f (algebraMap R 
S) ∧ Function.LeftInverse f (algebraMap R S)
参数：a : A；f : S -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quasispectrumRestricts_iff
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S → R) :
    QuasispectrumRestricts a f ↔ (quasispectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

@[simp]
/-
**quasispectrum.algebraMap_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasispectrum.algebraMap_mem_iff (S : Type*) {R A : Type*} [Semifield R] [
Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A] [SMu
lCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} {r : R} : algebraMa
p R S r in quasispectrum S a ↔ r in quasispectrum R a
参数：S : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem quasispectrum.algebraMap_mem_iff (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ quasispectrum S a ↔ r ∈ quasispectrum R a := by
  simp_rw [Unitization.quasispectrum_eq_spectrum_inr' _ S a, spectrum.algebraMap_mem_iff]

protected alias ⟨quasispectrum.of_algebraMap_mem, quasispectrum.algebraMap_mem⟩ :=
  quasispectrum.algebraMap_mem_iff

@[simp]
/-
**quasispectrum.preimage_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasispectrum.preimage_algebraMap (S : Type*) {R A : Type*} [Semifield R] 
[Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A] [SM
ulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} : algebraMap R S ⁻
¹' quasispectrum S a = quasispectrum R a
参数：S : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `quasispectrum.algebraMap_mem_iff`：quasispectrum.algebraMap_mem_iff (S : 
Type*) {R A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [Mo
dule S A] [IsScalarTow…
-/
theorem quasispectrum.preimage_algebraMap (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' quasispectrum S a = quasispectrum R a :=
  Set.ext fun _ => quasispectrum.algebraMap_mem_iff _

namespace QuasispectrumRestricts

section NonUnital

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]
variable [Algebra R S] {a : A} {f : S → R}

/-
**QuasispectrumRestricts.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumRestri
cts`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} {A : Type u_5} [inst : Semifield R] [inst_
1 : Field S] [inst_2 : NonUnitalRing A]   [inst_3 : _root_.Module R A] [inst_4 :
 _root_.Module S A] [inst_5 : Algebra R S] {a : A} {f : S → R},   QuasispectrumR
estricts a f → f 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
protected theorem map_zero (h : QuasispectrumRestricts a f) : f 0 = 0 := by
  rw [← h.left_inv 0, map_zero (algebraMap R S)]
/-
**QuasispectrumRestricts.of_subset_range_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Q
uasispectrumRestricts`。
形式化陈述：of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S)) (h : quas
ispectrum S a subseteq Set.range (algebraMap R S)) : QuasispectrumRestricts a f 
where rightInvOn
参数：hf : f.LeftInverse (algebraMap R S)；h : quasispectrum S a subseteq Set.range 
(algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S))
    (h : quasispectrum S a ⊆ Set.range (algebraMap R S)) : QuasispectrumRestricts a f where
  rightInvOn := fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf
/-
**QuasispectrumRestricts.of_quasispectrum_eq** 是 Mathlib 中的一个引理，位于命名空间 `Quasispe
ctrumRestricts`。
形式化陈述：of_quasispectrum_eq {a b : A} {f : S -> R} (ha : QuasispectrumRestricts a 
f) (h : quasispectrum S a = quasispectrum S b) : QuasispectrumRestricts b f wher
e rightInvOn
参数：ha : QuasispectrumRestricts a f；h : quasispectrum S a = quasispectrum S b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasispectrumRestricts.rightInvOn`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnita
lRing A] [inst_3 : _roo…
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
-/
lemma of_quasispectrum_eq {a b : A} {f : S → R} (ha : QuasispectrumRestricts a f)
    (h : quasispectrum S a = quasispectrum S b) : QuasispectrumRestricts b f where
  rightInvOn := h ▸ ha.rightInvOn
  left_inv := ha.left_inv

variable [IsScalarTower S A A] [SMulCommClass S A A]
/-
**QuasispectrumRestricts.mul_comm_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuasispectrumRe
stricts`。
形式化陈述：mul_comm_iff {f : S -> R} {a b : A} : QuasispectrumRestricts (a * b) f ↔ Q
uasispectrumRestricts (b * a) f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `quasispectrum.mul_comm`：quasispectrum.mul_comm {R A : Type*} [CommRing R
] [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a 
b : A) : qua…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mul_comm_iff {f : S → R} {a b : A} :
    QuasispectrumRestricts (a * b) f ↔ QuasispectrumRestricts (b * a) f := by
  simp only [quasispectrumRestricts_iff, quasispectrum.mul_comm]

alias ⟨mul_comm, _⟩ := mul_comm_iff

variable [IsScalarTower R S A]
/-
**QuasispectrumRestricts.algebraMap_image** 是 Mathlib 中的一个定理，位于命名空间 `Quasispectr
umRestricts`。
形式化陈述：algebraMap_image (h : QuasispectrumRestricts a f) : algebraMap R S '' quas
ispectrum R a = quasispectrum S a
参数：h : QuasispectrumRestricts a f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quasispectrum.preimage_algebraMap`：quasispectrum.preimage_algebraMap (S 
: Type*) {R A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [
Module S A] [IsScalarTo…
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `quasispectrum.of_algebraMap_mem`：∀ (S : Type u_3) {R : Type u_4} {A : Ty
pe u_5} [inst : Semifield R] [inst_1 : Field S] [inst_2 : NonUnitalRing A]   [in
st_3 : Algebra R S] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.rightInvOn`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnita
lRing A] [inst_3 : _roo…
-/
theorem algebraMap_image (h : QuasispectrumRestricts a f) :
    algebraMap R S '' quasispectrum R a = quasispectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [quasispectrum.preimage_algebraMap] using
      (quasispectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨quasispectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩
/-
**QuasispectrumRestricts.image** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumRestricts
`。
形式化陈述：image (h : QuasispectrumRestricts a f) : f '' quasispectrum S a = quasispe
ctrum R a
参数：h : QuasispectrumRestricts a f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.algebraMap_image`：algebraMap_image (h : Quasispec
trumRestricts a f) : algebraMap R S '' quasispectrum R a = quasispectrum S a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image (h : QuasispectrumRestricts a f) : f '' quasispectrum S a = quasispectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']
/-
**QuasispectrumRestricts.apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumRestr
icts`。
形式化陈述：apply_mem (h : QuasispectrumRestricts a f) {s : S} (hs : s in quasispectru
m S a) : f s in quasispectrum R a
参数：h : QuasispectrumRestricts a f；hs : s in quasispectrum S a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasispectrumRestricts.image`：image (h : QuasispectrumRestricts a f) : f
 '' quasispectrum S a = quasispectrum R a
-/
theorem apply_mem (h : QuasispectrumRestricts a f) {s : S} (hs : s ∈ quasispectrum S a) :
    f s ∈ quasispectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩
/-
**QuasispectrumRestricts.subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Quasispectru
mRestricts`。
形式化陈述：subset_preimage (h : QuasispectrumRestricts a f) : quasispectrum S a subse
teq f ⁻¹' quasispectrum R a
参数：h : QuasispectrumRestricts a f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `QuasispectrumRestricts.image`：image (h : QuasispectrumRestricts a f) : f
 '' quasispectrum S a = quasispectrum R a
-/
theorem subset_preimage (h : QuasispectrumRestricts a f) :
    quasispectrum S a ⊆ f ⁻¹' quasispectrum R a :=
  h.image ▸ (quasispectrum S a).subset_preimage_image f
/-
**QuasispectrumRestricts.comp** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumRestricts`
。
形式化陈述：∀ {R₁ : Type u_6} {R₂ : Type u_7} {R₃ : Type u_8} {A : Type u_9} [inst : S
emifield R₁] [inst_1 : Field R₂]   [inst_2 : Field R₃] [inst_3 : NonUnitalRing A
] [inst_4 : _root_.Module R₁ A] [inst_5 : _root_.Module R₂ A]   [inst_6 : _root_
.Module R₃ A] [inst_7 : Algebra R₁ R₂] [inst_8 : Algebra R₂ R₃] [inst_9 : Algebr
a R₁ R₃]   [IsScalarTower R₁ R₂ R₃] [IsScalarTower R₂ R₃ A] [IsScalarTower R₃ A 
A] [SMulCommClass R₃ A A] {a : A} {f : R₃ → R₂}   {g : R₂ → R₁} {e : R₃ → R₁},  
 g ∘ f = e → QuasispectrumRestricts a f → QuasispectrumRestricts a g → Quasispec
trumRestricts a e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Set.RightInvOn.comp`：comp (hf : RightInvOn f' f t) (hg : RightInvOn g' g
 p) (g'pt : MapsTo g' p t) : RightInvOn (f' ∘ g') (g ∘ f) p
· 使用定理 `QuasispectrumRestricts.rightInvOn`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnita
lRing A] [inst_3 : _roo…
· 使用定理 `QuasispectrumRestricts.apply_mem`：apply_mem (h : QuasispectrumRestricts 
a f) {s : S} (hs : s in quasispectrum S a) : f s in quasispectrum R a
· 使用定理 `Function.LeftInverse.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3
} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β},   Function.LeftInverse f g → 
Function.LeftIn…
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
-/
protected lemma comp {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
    [NonUnitalRing A] [Module R₁ A] [Module R₂ A] [Module R₃ A] [Algebra R₁ R₂] [Algebra R₂ R₃]
    [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃] [IsScalarTower R₂ R₃ A] [IsScalarTower R₃ A A]
    [SMulCommClass R₃ A A] {a : A} {f : R₃ → R₂} {g : R₂ → R₁} {e : R₃ → R₁} (hfge : g ∘ f = e)
    (hf : QuasispectrumRestricts a f) (hg : QuasispectrumRestricts a g) :
    QuasispectrumRestricts a e where
  left_inv := by
    convert! hfge ▸ hf.left_inv.comp hg.left_inv
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
  rightInvOn := by
    convert! hfge ▸ hg.rightInvOn.comp hf.rightInvOn fun _ ↦ hf.apply_mem
    congrm (⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))

end NonUnital

end QuasispectrumRestricts

/-- A (reducible) alias of `QuasispectrumRestricts` which enforces stronger type class assumptions
on the types involved, as it's really intended for the `spectrum`. The separate definition also
allows for dot notation. -/
@[reducible]
/-
**SpectrumRestricts** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SpectrumRestricts {R S A : Type*} [Semifield R] [Semifield S] [Ring A] [Al
gebra R A] [Algebra S A] [Algebra R S] (a : A) (f : S -> R) : Prop
参数：a : A；f : S -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (reducible) alias of `QuasispectrumRestricts` which enforces stronger type cla
ss assumptions
on the types involved, as it's really intended for the `spectrum`. The separate 
definition also
allows for dot notation.
-/
def SpectrumRestricts
    {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R A] [Algebra S A] [Algebra R S] (a : A) (f : S → R) : Prop :=
  QuasispectrumRestricts a f

namespace SpectrumRestricts

section Unital

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

/-
**SpectrumRestricts.rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestricts`。
形式化陈述：rightInvOn (h : SpectrumRestricts a f) : (spectrum S a).RightInvOn f (alge
braMap R S)
参数：h : SpectrumRestricts a f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.RightInvOn.mono`：mono (hf : RightInvOn f' f t) (ht : t₁ subseteq t) 
: RightInvOn f' f t₁
· 使用定理 `QuasispectrumRestricts.rightInvOn`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnita
lRing A] [inst_3 : _roo…
· 使用引理 `spectrum_subset_quasispectrum`：spectrum_subset_quasispectrum (R : Type*)
 {A : Type*} [CommSemiring R] [Ring A] [Algebra R A] (a : A) : spectrum R a subs
eteq quasispectrum …
-/
theorem rightInvOn (h : SpectrumRestricts a f) : (spectrum S a).RightInvOn f (algebraMap R S) :=
  (QuasispectrumRestricts.rightInvOn h).mono <| spectrum_subset_quasispectrum _ _
/-
**SpectrumRestricts.of_rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestricts`。
形式化陈述：of_rightInvOn (h₁ : Function.LeftInverse f (algebraMap R S)) (h₂ : (spectr
um S a).RightInvOn f (algebraMap R S)) : SpectrumRestricts a f where rightInvOn 
x hx
参数：h₁ : Function.LeftInverse f (algebraMap R S)；h₂ : (spectrum S a).RightInvOn f
 (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_quasispectrum_iff`：mem_quasispectrum_iff {R A : Type*} [Semifield R]
 [Ring A] [Algebra R A] {a : A} {x : R} : x in quasispectrum R a ↔ x = 0 ∨ x in 
spectrum R …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_rightInvOn (h₁ : Function.LeftInverse f (algebraMap R S))
    (h₂ : (spectrum S a).RightInvOn f (algebraMap R S)) : SpectrumRestricts a f where
  rightInvOn x hx := by
    obtain (rfl | hx) := mem_quasispectrum_iff.mp hx
    · simpa using h₁ 0
    · exact h₂ hx
  left_inv := h₁
/-
**SpectrumRestricts._root_.spectrumRestricts_iff** 是 Mathlib 中的一个引理，位于命名空间 `Spec
trumRestricts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.spectrumRestricts_iff :
    SpectrumRestricts a f ↔ (spectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) :=
  ⟨fun h ↦ ⟨h.rightInvOn, h.left_inv⟩, fun h ↦ .of_rightInvOn h.2 h.1⟩
/-
**SpectrumRestricts.of_subset_range_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Spectr
umRestricts`。
形式化陈述：of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S)) (h : spec
trum S a subseteq Set.range (algebraMap R S)) : SpectrumRestricts a f where righ
tInvOn
参数：hf : f.LeftInverse (algebraMap R S)；h : spectrum S a subseteq Set.range (alge
braMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_quasispectrum_iff`：mem_quasispectrum_iff {R A : Type*} [Semifield R]
 [Ring A] [Algebra R A] {a : A} {x : R} : x in quasispectrum R a ↔ x = 0 ∨ x in 
spectrum R …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S))
    (h : spectrum S a ⊆ Set.range (algebraMap R S)) : SpectrumRestricts a f where
  rightInvOn := fun s hs => by
    rw [mem_quasispectrum_iff] at hs
    obtain (rfl | hs) := hs
    · simpa using hf 0
    · obtain ⟨r, rfl⟩ := h hs
      rw [hf r]
  left_inv := hf
/-
**SpectrumRestricts.of_spectrum_eq** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`
。
形式化陈述：of_spectrum_eq {a b : A} {f : S -> R} (ha : SpectrumRestricts a f) (h : sp
ectrum S a = spectrum S b) : SpectrumRestricts b f where rightInvOn
参数：ha : SpectrumRestricts a f；h : spectrum S a = spectrum S b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.rightInvOn`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnita
lRing A] [inst_3 : _roo…
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
-/
lemma of_spectrum_eq {a b : A} {f : S → R} (ha : SpectrumRestricts a f)
    (h : spectrum S a = spectrum S b) : SpectrumRestricts b f where
  rightInvOn := by
    rw [quasispectrum_eq_spectrum_union_zero, ← h, ← quasispectrum_eq_spectrum_union_zero]
    exact QuasispectrumRestricts.rightInvOn ha
  left_inv := ha.left_inv
/-
**SpectrumRestricts.mul_comm_iff** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：mul_comm_iff {R S A : Type*} [Semifield R] [Field S] [Ring A] [Algebra R S
] [Algebra R A] [Algebra S A] {a b : A} {f : S -> R} : SpectrumRestricts (a * b)
 f ↔ SpectrumRestricts (b * a) f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `QuasispectrumRestricts.mul_comm_iff`：mul_comm_iff {f : S -> R} {a b : A}
 : QuasispectrumRestricts (a * b) f ↔ QuasispectrumRestricts (b * a) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma mul_comm_iff {R S A : Type*} [Semifield R] [Field S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] {a b : A} {f : S → R} :
    SpectrumRestricts (a * b) f ↔ SpectrumRestricts (b * a) f :=
  QuasispectrumRestricts.mul_comm_iff

alias ⟨mul_comm, _⟩ := mul_comm_iff

variable [IsScalarTower R S A]
/-
**SpectrumRestricts.algebraMap_image** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestrict
s`。
形式化陈述：algebraMap_image (h : SpectrumRestricts a f) : algebraMap R S '' spectrum 
R a = spectrum S a
参数：h : SpectrumRestricts a f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.preimage_algebraMap`：preimage_algebraMap (S : Type*) {R A : Typ
e*} [CommSemiring R] [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Alge
bra S A] [IsScalar…
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `spectrum.of_algebraMap_mem`：∀ (S : Type u_1) {R : Type u_2} {A : Type u_
3} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Ring A]   [inst_3
 : Algebra R S] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.rightInvOn`：rightInvOn (h : SpectrumRestricts a f) : (
spectrum S a).RightInvOn f (algebraMap R S)
-/
theorem algebraMap_image (h : SpectrumRestricts a f) :
    algebraMap R S '' spectrum R a = spectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [spectrum.preimage_algebraMap] using
      (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩
/-
**SpectrumRestricts.image** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestricts`。
形式化陈述：image (h : SpectrumRestricts a f) : f '' spectrum S a = spectrum R a
参数：h : SpectrumRestricts a f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image (h : SpectrumRestricts a f) : f '' spectrum S a = spectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']
/-
**SpectrumRestricts.apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestricts`。
形式化陈述：apply_mem (h : SpectrumRestricts a f) {s : S} (hs : s in spectrum S a) : f
 s in spectrum R a
参数：h : SpectrumRestricts a f；hs : s in spectrum S a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
-/
theorem apply_mem (h : SpectrumRestricts a f) {s : S} (hs : s ∈ spectrum S a) :
    f s ∈ spectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩
/-
**SpectrumRestricts.subset_preimage** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestricts
`。
形式化陈述：subset_preimage (h : SpectrumRestricts a f) : spectrum S a subseteq f ⁻¹' 
spectrum R a
参数：h : SpectrumRestricts a f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
-/
theorem subset_preimage (h : SpectrumRestricts a f) : spectrum S a ⊆ f ⁻¹' spectrum R a :=
  h.image ▸ (spectrum S a).subset_preimage_image f

end Unital

end SpectrumRestricts

/-
**quasispectrumRestricts_iff_spectrumRestricts_inr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasispectrumRestricts_iff_spectrumRestricts_inr (S : Type*) {R A : Type*}
 [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [Module R A] [Module S 
A] [IsScalarTower S A A] [SMulCommClass S A A] [IsScalarTower R S A] {a : A} {f 
: S -> R} : QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A)
 f
参数：S : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasispectrumRestricts_iff`：quasispectrumRestricts_iff {R S A : Type*} [
CommSemiring R] [CommSemiring S] [NonUnitalRing A] [Module R A] [Module S A] [Al
gebra R S] (a : …
· 使用定理 `spectrumRestricts_iff`：∀ {R : Type u_3} {S : Type u_4} {A : Type u_5} [i
nst : Semifield R] [inst_1 : Semifield S] [inst_2 : Ring A]   [inst_3 : Algebra 
R S] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem quasispectrumRestricts_iff_spectrumRestricts_inr (S : Type*) {R A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [IsScalarTower R S A] {a : A} {f : S → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  rw [quasispectrumRestricts_iff, spectrumRestricts_iff,
    ← Unitization.quasispectrum_eq_spectrum_inr']

/-- The difference from `quasispectrumRestricts_iff_spectrumRestricts_inr` is that the
`Unitization` may be taken with respect to a different scalar field. -/
/-
**quasispectrumRestricts_iff_spectrumRestricts_inr'** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：quasispectrumRestricts_iff_spectrumRestricts_inr' {R S' A : Type*} (S : Ty
pe*) [Semifield R] [Semifield S'] [Field S] [NonUnitalRing A] [Module R A] [Modu
le S' A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A] [Algebra R S']
 [Algebra S' S] [Algebra R S] [IsScalarTower S' S A] [IsScalarTower R S A] {a : 
A} {f : S' -> R} : QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitizati
on S A) f
参数：S : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Unitization.quasispectrum_inr_eq`：quasispectrum_inr_eq (R S : Type*) {A 
: Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [I
sScalarTower S A A] [S…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The difference from `quasispectrumRestricts_iff_spectrumRestricts_inr` is that t
he
`Unitization` may be taken with respect to a different scalar field.
-/
lemma quasispectrumRestricts_iff_spectrumRestricts_inr'
    {R S' A : Type*} (S : Type*) [Semifield R] [Semifield S'] [Field S] [NonUnitalRing A]
    [Module R A] [Module S' A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S'] [Algebra S' S] [Algebra R S] [IsScalarTower S' S A] [IsScalarTower R S A]
    {a : A} {f : S' → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  simp only [quasispectrumRestricts_iff, SpectrumRestricts, Unitization.quasispectrum_inr_eq]
/-
**quasispectrumRestricts_iff_spectrumRestricts** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasispectrumRestricts_iff_spectrumRestricts {R S A : Type*} [Semifield R]
 [Semifield S] [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S
 -> R} : QuasispectrumRestricts a f ↔ SpectrumRestricts a f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem quasispectrumRestricts_iff_spectrumRestricts {R S A : Type*} [Semifield R] [Semifield S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts a f := by rfl
