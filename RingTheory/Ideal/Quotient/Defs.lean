/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Congruence.Defs
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `RingCon.Quotient` for quotients of (possibly non-commutative) semirings.

## Main definitions

- `Ideal.instHasQuotient`: the quotient of a commutative ring `R` by an ideal `I : Ideal R`
- `Ideal.Quotient.commRing`: the ring structure of the ideal quotient
- `Ideal.Quotient.mk`: map an element of `R` to the quotient `R ⧸ I`
- `Ideal.Quotient.lift`: turn a map `R → S` into a map `R ⧸ I → S`
- `Ideal.quotEquivOfEq`: quotienting by equal ideals gives isomorphic rings
-/

@[expose] public section


universe u v w

namespace Ideal

open Set

variable {R : Type u} [Ring R] (I J : Ideal R) {a b : R}
variable {S : Type v}

/-- The quotient `R/I` of a ring `R` by an ideal `I`,
defined to equal the quotient of `I` as an `R`-submodule of `R`. -/
/-
**Ideal.instHasQuotient** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：instHasQuotient : HasQuotient R (Ideal R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient `R/I` of a ring `R` by an ideal `I`,
defined to equal the quotient of `I` as an `R`-submodule of `R`.
-/
instance instHasQuotient : HasQuotient R (Ideal R) := Submodule.hasQuotient

/-- Shortcut instance for commutative rings. -/
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shortcut instance for commutative rings.
-/
instance {R} [CommRing R] : HasQuotient R (Ideal R) := inferInstance

namespace Quotient

variable {I} {x y : R}

/-
**Ideal.Quotient.one** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：one (I : Ideal R) : One (R ⧸ I)
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one (I : Ideal R) : One (R ⧸ I) :=
  ⟨Submodule.Quotient.mk 1⟩

set_option backward.isDefEq.respectTransparency false in
/-- On `Ideal`s, `Submodule.quotientRel` is a ring congruence. -/
/-
**Ideal.Quotient.ringCon** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：{R : Type u} → [inst : Ring R] → (I : Ideal R) → [I.IsTwoSided] → RingCon 
R
参数：I : Ideal R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On `Ideal`s, `Submodule.quotientRel` is a ring congruence.
-/
protected def ringCon (I : Ideal R) [I.IsTwoSided] : RingCon R where
  __ := QuotientAddGroup.con I.toAddSubgroup
  mul' {a₁ b₁ a₂ b₂} h₁ h₂ := by
    rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
    exact mul_sub_mul_mem I h₁ h₂

/-- **Quotient ring**: the quotient of a ring by a two-sided ideal is a ring. -/
@[wikidata Q619436]
/-
**Ideal.Quotient.ring** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：ring (I : Ideal R) [I.IsTwoSided] : Ring (R ⧸ I)
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Quotient ring**: the quotient of a ring by a two-sided ideal is a ring.
-/
instance ring (I : Ideal R) [I.IsTwoSided] : Ring (R ⧸ I) :=
  inferInstanceAs <| Ring (Quotient.ringCon I).Quotient
/-
**Ideal.Quotient.semiring** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：semiring {R} [CommRing R] (I : Ideal R) : Semiring (R ⧸ I)
参数：I : Ideal R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
instance semiring {R} [CommRing R] (I : Ideal R) : Semiring (R ⧸ I) := (ring I).toSemiring
/-
**Ideal.Quotient.commSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：commSemiring {R} [CommRing R] (I : Ideal R) : CommSemiring (R ⧸ I) where m
ul_comm
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemiring {R} [CommRing R] (I : Ideal R) : CommSemiring (R ⧸ I) where
  mul_comm := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (mul_comm a b)
/-
**Ideal.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [CommRing R] (I : Ideal R) : Ring (R ⧸ I) := ring I
/-
**Ideal.Quotient.commRing** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
形式化陈述：commRing {R} [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) where  variable
 [I.IsTwoSided]  -- Sanity test to make sure no diamonds have emerged in `commRi
ng` example : (ring I).toAddCommGroup = Submodule.Quotient.addCommGroup I
参数：I : Ideal R。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing {R} [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) where

variable [I.IsTwoSided]

-- Sanity test to make sure no diamonds have emerged in `commRing`
/-
**Ideal.Quotient.** 是 Mathlib 中的一个示例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (ring I).toAddCommGroup = Submodule.Quotient.addCommGroup I := by
  with_reducible_and_instances rfl

variable (I) in
/-- The ring homomorphism from a ring `R` to a quotient ring `R/I`. -/
/-
**Ideal.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk : R ->+* R ⧸ I where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from a ring `R` to a quotient ring `R/I`.
-/
def mk : R →+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
/-
**Ideal.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe R (R ⧸ I) :=
  ⟨Ideal.Quotient.mk I⟩

/-- Two `RingHom`s from the quotient by an ideal are equal if their
compositions with `Ideal.Quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
/-
**Ideal.Quotient.ringHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ I ->+* S⦄ (h : f.comp (mk I) =
 g.comp (mk I)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2

--- 原说明 ---
Two `RingHom`s from the quotient by an ideal are equal if their
compositions with `Ideal.Quotient.mk'` are equal.

See note [partially-applied ext lemmas].
-/
theorem ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ I →+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) :
    f = g :=
  RingHom.ext fun x => Quotient.inductionOn' x <| (RingHom.congr_fun h :)
/-
**Ideal.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (R ⧸ I) :=
  ⟨mk I 37⟩
/-
**Ideal.Quotient.eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R} [inst_1 : I.IsTwoSi
ded],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔ x - y ∈ I
参数：Ideal.Quotient.mk I；Ideal.Quotient.mk I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
-/
protected theorem eq : mk I x = mk I y ↔ x - y ∈ I :=
  Submodule.Quotient.eq I

@[simp]
/-
**Ideal.Quotient.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x := rfl
/-
**Ideal.Quotient.eq_zero_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：eq_zero_iff_mem : mk I a = 0 ↔ a in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
-/
theorem eq_zero_iff_mem : mk I a = 0 ↔ a ∈ I :=
  Submodule.Quotient.mk_eq_zero _
/-
**Ideal.Quotient.mk_eq_mk_iff_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`
。
形式化陈述：mk_eq_mk_iff_sub_mem (x y : R) : mk I x = mk I y ↔ x - y in I
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_mk_iff_sub_mem (x y : R) : mk I x = mk I y ↔ x - y ∈ I := by
  rw [← eq_zero_iff_mem, map_sub, sub_eq_zero]
/-
**Ideal.Quotient.mk_eq_one_iff_sub_mem** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quotient
`。
形式化陈述：mk_eq_one_iff_sub_mem (x : R) : mk I x = 1 ↔ x - 1 in I
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.mk_eq_mk_iff_sub_mem`：mk_eq_mk_iff_sub_mem (x y : R) : mk
 I x = mk I y ↔ x - y in I
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
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mk_eq_one_iff_sub_mem (x : R) : mk I x = 1 ↔ x - 1 ∈ I := by
  rw [← mk_eq_mk_iff_sub_mem, map_one]

@[simp]
/-
**Ideal.Quotient.mk_out** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotient.out x) = x
参数：x : R ⧸ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotient.out x) = x :=
  Quotient.out_eq x
/-
**Ideal.Quotient.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：mk_surjective : Function.Surjective (mk I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem mk_surjective : Function.Surjective (mk I) := fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl
/-
**Ideal.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RingHomSurjective (mk I) :=
  ⟨mk_surjective⟩

/-- If `I` is an ideal of a commutative ring `R`, if `q : R → R/I` is the quotient map, and if
`s ⊆ R` is a subset, then `q⁻¹(q(s)) = ⋃ᵢ(i + s)`, the union running over all `i ∈ I`. -/
/-
**Ideal.Quotient.quotient_ring_saturate** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotien
t`。
形式化陈述：quotient_ring_saturate (s : Set R) : mk I ⁻¹' mk I '' s = ⋃ x : I, (fun y 
=> x.1 + y) '' s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_eq_sub_sub_swap`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (
a b c : α), a - (b + c) = a - c - b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a

--- 原说明 ---
If `I` is an ideal of a commutative ring `R`, if `q : R → R/I` is the quotient m
ap, and if
`s ⊆ R` is a subset, then `q⁻¹(q(s)) = ⋃ᵢ(i + s)`, the union running over all `i
 ∈ I`.
-/
theorem quotient_ring_saturate (s : Set R) :
    mk I ⁻¹' mk I '' s = ⋃ x : I, (fun y => x.1 + y) '' s := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩

variable [Semiring S] (I)

/-- Given a ring homomorphism `f : R →+* S` sending all elements of an ideal to zero,
lift it to the quotient by this ideal. -/
/-
**Ideal.Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：lift (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) : R ⧸ I ->+* S
参数：f : R ->+* S；H : forall a : R, a in I -> f a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a ring homomorphism `f : R →+* S` sending all elements of an ideal to zero
,
lift it to the quotient by this ideal.
-/
def lift (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) : R ⧸ I →+* S :=
  { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }

@[simp]
/-
**Ideal.Quotient.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：lift_mk (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) : lift I f H 
(mk I a) = f a
参数：f : R ->+* S；H : forall a : R, a in I -> f a = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) :
    lift I f H (mk I a) = f a :=
  rfl
/-
**Ideal.Quotient.lift_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quotient`。
形式化陈述：lift_comp_mk (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) : (lift 
I f H).comp (mk I) = f
参数：f : R ->+* S；H : forall a : R, a in I -> f a = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_comp_mk (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) :
    (lift I f H).comp (mk I) = f := rfl
/-
**Ideal.Quotient.lift_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.
Quotient`。
形式化陈述：lift_surjective_of_surjective {f : R ->+* S} (H : forall a : R, a in I -> 
f a = 0) (hf : Function.Surjective f) : Function.Surjective (Ideal.Quotient.lift
 I f H)
参数：H : forall a : R, a in I -> f a = 0；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_surjective_of_surjective {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hf : Function.Surjective f) : Function.Surjective (Ideal.Quotient.lift I f H) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  use Ideal.Quotient.mk I x
  simp only [Ideal.Quotient.lift_mk]

variable {S T U : Ideal R} [S.IsTwoSided] [T.IsTwoSided] [U.IsTwoSided]

/-- The ring homomorphism from the quotient by a smaller ideal to the quotient by a larger ideal.

This is the `Ideal.Quotient` version of `Quot.Factor`

When the two ideals are of the form `I^m` and `I^n` and `n ≤ m`,
please refer to the dedicated version `Ideal.Quotient.factorPow`. -/
/-
**Ideal.Quotient.factor** 是 Mathlib 中的一个定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor (H : S <= T) : R ⧸ S ->+* R ⧸ T
参数：H : S <= T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from the quotient by a smaller ideal to the quotient by a 
larger ideal.

This is the `Ideal.Quotient` version of `Quot.Factor`

When the two ideals are of the form `I^m` and `I^n` and `n ≤ m`,
please refer to the dedicated version `Ideal.Quotient.factorPow`.
-/
def factor (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
  Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

@[simp]
/-
**Ideal.Quotient.factor_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor_mk (H : S <= T) (x : R) : factor H (mk S x) = mk T x
参数：H : S <= T；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factor_mk (H : S ≤ T) (x : R) : factor H (mk S x) = mk T x :=
  rfl

@[simp]
/-
**Ideal.Quotient.factor_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor_eq : factor (le_refl S) = RingHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factor_eq : factor (le_refl S) = RingHom.id _ := by
  ext
  simp

@[simp]
/-
**Ideal.Quotient.factor_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor_comp_mk (H : S <= T) : (factor H).comp (mk S) = mk T
参数：H : S <= T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `Ideal.Quotient.factor_mk`：factor_mk (H : S <= T) (x : R) : factor H (mk 
S x) = mk T x
-/
theorem factor_comp_mk (H : S ≤ T) : (factor H).comp (mk S) = mk T := by
  ext x
  rw [RingHom.comp_apply, factor_mk]

@[simp]
/-
**Ideal.Quotient.factor_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor_comp (H1 : S <= T) (H2 : T <= U) : (factor H2).comp (factor H1) = f
actor (H1.trans H2)
参数：H1 : S <= T；H2 : T <= U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.Quotient.factor_comp_mk`：factor_comp_mk (H : S <= T) : (factor H).
comp (mk S) = mk T
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factor_comp (H1 : S ≤ T) (H2 : T ≤ U) :
    (factor H2).comp (factor H1) = factor (H1.trans H2) := by
  ext
  simp

@[simp]
/-
**Ideal.Quotient.factor_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor_comp_apply (H1 : S <= T) (H2 : T <= U) (x : R ⧸ S) : factor H2 (fac
tor H1 x) = factor (H1.trans H2) x
参数：H1 : S <= T；H2 : T <= U；x : R ⧸ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.Quotient.factor_comp`：factor_comp (H1 : S <= T) (H2 : T <= U) : (f
actor H2).comp (factor H1) = factor (H1.trans H2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factor_comp_apply (H1 : S ≤ T) (H2 : T ≤ U) (x : R ⧸ S) :
    factor H2 (factor H1 x) = factor (H1.trans H2) x := by
  rw [← RingHom.comp_apply]
  simp
/-
**Ideal.Quotient.factor_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ideal.Quotient`。
形式化陈述：factor_surjective (H : S <= T) : Function.Surjective (factor H)
参数：H : S <= T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.lift_surjective_of_surjective`：lift_surjective_of_surject
ive {f : R ->+* S} (H : forall a : R, a in I -> f a = 0) (hf : Function.Surjecti
ve f) : Function.Surjective (Ideal…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
lemma factor_surjective (H : S ≤ T) : Function.Surjective (factor H) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective

end Quotient

variable {I J} [I.IsTwoSided] [J.IsTwoSided]

/-- Quotienting by equal ideals gives equivalent rings.

See also `Submodule.quotEquivOfEq` and `Ideal.quotientEquivAlgOfEq`.
-/
/-
**Ideal.quotEquivOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：quotEquivOfEq (h : I = J) : R ⧸ I ≃+* R ⧸ J
参数：h : I = J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quotienting by equal ideals gives equivalent rings.

See also `Submodule.quotEquivOfEq` and `Ideal.quotientEquivAlgOfEq`.
-/
def quotEquivOfEq (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl }

@[simp]
/-
**Ideal.quotEquivOfEq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotEquivOfEq_mk (h : I = J) (x : R) : quotEquivOfEq h (Ideal.Quotient.mk 
I x) = Ideal.Quotient.mk J x
参数：h : I = J；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotEquivOfEq_mk (h : I = J) (x : R) :
    quotEquivOfEq h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl

@[simp]
/-
**Ideal.quotEquivOfEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotEquivOfEq_symm (h : I = J) : (Ideal.quotEquivOfEq h).symm = Ideal.quot
EquivOfEq h.symm
参数：h : I = J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.ext`：ext {f g : R ≃+* S} (h : forall x, f x = g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem quotEquivOfEq_symm (h : I = J) :
    (Ideal.quotEquivOfEq h).symm = Ideal.quotEquivOfEq h.symm := by ext; rfl
/-
**Ideal.quotEquivOfEq_eq_factor** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotEquivOfEq_eq_factor (h : I = J) (x : R ⧸ I) : Ideal.quotEquivOfEq h x 
= Ideal.Quotient.factor (h ▸ le_refl I) x
参数：h : I = J；x : R ⧸ I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotEquivOfEq_eq_factor (h : I = J) (x : R ⧸ I) :
    Ideal.quotEquivOfEq h x = Ideal.Quotient.factor (h ▸ le_refl I) x := rfl

end Ideal

