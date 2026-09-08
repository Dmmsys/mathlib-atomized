/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Ideals over/under ideals in integral extensions

This file proves some going-up results for integral algebras.

## Implementation notes

The proofs of the `comap_ne_bot` and `comap_lt_comap` families use an approach
specific for their situation: we construct an element in `I.comap f` from the
coefficients of a minimal polynomial.
Once mathlib has more material on the localization at a prime ideal, the results
can be proven using more general going-up/going-down theory.
-/

@[expose] public section

open Polynomial Submodule

open scoped Pointwise

namespace Ideal

section

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

/-
**Ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Ideal`。
形式化陈述：coeff_zero_mem_comap_of_root_mem_of_eval_mem {r : S} (hr : r in I) {p : R[
X]} (hp : p.eval₂ f r in I) : p.coeff 0 in I.comap f
参数：hr : r in I；hp : p.eval₂ f r in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.add_mem_iff_right`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a
 b : α}, a ∈ I → (a + b ∈ I ↔ b ∈ I)
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `Polynomial.eval₂_add`：eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.ev
al₂ f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.divX_mul_X_add`：divX_mul_X_add (p : R[X]) : divX p * X + C (p
.coeff 0) = p
-/
theorem coeff_zero_mem_comap_of_root_mem_of_eval_mem {r : S} (hr : r ∈ I) {p : R[X]}
    (hp : p.eval₂ f r ∈ I) : p.coeff 0 ∈ I.comap f := by
  rw [← p.divX_mul_X_add, eval₂_add, eval₂_C, eval₂_mul, eval₂_X] at hp
  refine mem_comap.mpr ((I.add_mem_iff_right ?_).mp hp)
  exact I.mul_mem_left _ hr
/-
**Ideal.coeff_zero_mem_comap_of_root_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：coeff_zero_mem_comap_of_root_mem {r : S} (hr : r in I) {p : R[X]} (hp : p.
eval₂ f r = 0) : p.coeff 0 in I.comap f
参数：hr : r in I；hp : p.eval₂ f r = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.coeff_zero_mem_comap_of_root_mem_of_eval_mem`：coeff_zero_mem_comap
_of_root_mem_of_eval_mem {r : S} (hr : r in I) {p : R[X]} (hp : p.eval₂ f r in I
) : p.coeff 0 in I.comap f
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coeff_zero_mem_comap_of_root_mem {r : S} (hr : r ∈ I) {p : R[X]} (hp : p.eval₂ f r = 0) :
    p.coeff 0 ∈ I.comap f :=
  coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)
/-
**Ideal.exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem** 是 Mathlib 
中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {r : S} (r_non
_zero_divisor : forall {x}, x * r = 0 -> x = 0) (hr : r in I) {p : R[X]} : p != 
0 -> p.eval₂ f r = 0 -> exists i, p.coeff i != 0 ∧ p.coeff i in I.comap f
参数：r_non_zero_divisor : forall {x}, x * r = 0 -> x = 0；hr : r in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ideal.coeff_zero_mem_comap_of_root_mem`：coeff_zero_mem_comap_of_root_mem
 {r : S} (hr : r in I) {p : R[X]} (hp : p.eval₂ f r = 0) : p.coeff 0 in I.comap 
f
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `Polynomial.eval₂_mul`：eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.ev
al₂ f x
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
-/
theorem exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {r : S}
    (r_non_zero_divisor : ∀ {x}, x * r = 0 → x = 0) (hr : r ∈ I) {p : R[X]} :
    p ≠ 0 → p.eval₂ f r = 0 → ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f := by
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a coeff_eq_zero a_ne_zero _ _ hp
    refine ⟨0, ?_, coeff_zero_mem_comap_of_root_mem hr hp⟩
    simp [coeff_eq_zero, a_ne_zero]
  · intro p p_nonzero ih _ hp
    rw [eval₂_mul, eval₂_X] at hp
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (r_non_zero_divisor hp)
    refine ⟨i + 1, ?_, ?_⟩
    · simp [hi]
    · simpa [hi] using mem

/-- Let `P` be an ideal in `R[x]`.  The map
`R[x]/P → (R / (P ∩ R))[x] / (P / (P ∩ R))`
is injective.
-/
/-
**Ideal.injective_quotient_le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：injective_quotient_le_comap_map (P : Ideal R[X]) : Function.Injective Idea
l.quotientMap (Ideal.map (Polynomial.mapRingHom (Quotient.mk (P.comap (C : R ->+
* R[X])))) P) (Polynomial.mapRingHom (Ideal.Quotient.mk (P.comap (C : R ->+* R[X
])))) le_comap_map
参数：P : Ideal R[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.quotientMap_injective'`：quotientMap_injective' {J : Ideal R} {I : 
Ideal S} [I.IsTwoSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} (h : 
I.comap f <= J) : …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Polynomial.map_surjective`：map_surjective (hf : Function.Surjective f) :
 Function.Surjective (map f)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ideal.polynomial_mem_ideal_of_coeff_mem_ideal`：polynomial_mem_ideal_of_c
oeff_mem_ideal (I : Ideal R[X]) (p : R[X]) (hp : forall n : Nat, p.coeff n in I.
comap (C : R ->+* R[X])) : p in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.ext_iff`：ext_iff {p q : R[X]} : p = q ↔ forall n, coeff p n =
 coeff q n
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b

--- 原说明 ---
Let `P` be an ideal in `R[x]`.  The map
`R[x]/P → (R / (P ∩ R))[x] / (P / (P ∩ R))`
is injective.
-/
theorem injective_quotient_le_comap_map (P : Ideal R[X]) :
    Function.Injective <|
      Ideal.quotientMap
        (Ideal.map (Polynomial.mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)
        (Polynomial.mapRingHom (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))))
        le_comap_map := by
  refine quotientMap_injective' (le_of_eq ?_)
  rw [comap_map_of_surjective (mapRingHom (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))))
      (map_surjective (Ideal.Quotient.mk (P.comap (C : R →+* R[X]))) Ideal.Quotient.mk_surjective)]
  refine le_antisymm (sup_le le_rfl ?_) (le_sup_of_le_left le_rfl)
  refine fun p hp =>
    polynomial_mem_ideal_of_coeff_mem_ideal P p fun n => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  simpa only [coeff_map, coe_mapRingHom] using! ext_iff.mp (Ideal.mem_bot.mp (mem_comap.mp hp)) n

/-- The identity in this lemma asserts that the "obvious" square
```
    R    → (R / (P ∩ R))
    ↓          ↓
R[x] / P → (R / (P ∩ R))[x] / (P / (P ∩ R))
```
commutes.  It is used, for instance, in the proof of `quotient_mk_comp_C_is_integral_of_jacobson`,
in the file `Mathlib/RingTheory/Jacobson/Polynomial.lean`.
-/
/-
**Ideal.quotient_mk_maps_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：quotient_mk_maps_eq (P : Ideal R[X]) : ((Quotient.mk (map (mapRingHom (Quo
tient.mk (P.comap (C : R ->+* R[X])))) P)).comp C).comp (Quotient.mk (P.comap (C
 : R ->+* R[X]))) = (Ideal.quotientMap (map (mapRingHom (Quotient.mk (P.comap (C
 : R ->+* R[X])))) P) (mapRingHom (Quotient.mk (P.comap (C : R ->+* R[X])))) le_
comap_map).comp ((Quotient.mk P).comp C)
参数：P : Ideal R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The identity in this lemma asserts that the "obvious" square
```
    R    → (R / (P ∩ R))
    ↓          ↓
R[x] / P → (R / (P ∩ R))[x] / (P / (P ∩ R))
```
commutes.  It is used, for instance, in the proof of `quotient_mk_comp_C_is_inte
gral_of_jacobson`,
in the file `Mathlib/RingTheory/Jacobson/Polynomial.lean`.
-/
theorem quotient_mk_maps_eq (P : Ideal R[X]) :
    ((Quotient.mk (map (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)).comp C).comp
        (Quotient.mk (P.comap (C : R →+* R[X]))) =
      (Ideal.quotientMap (map (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) P)
            (mapRingHom (Quotient.mk (P.comap (C : R →+* R[X])))) le_comap_map).comp
        ((Quotient.mk P).comp C) := by
  ext
  simp

/-- This technical lemma asserts the existence of a polynomial `p` in an ideal `P ⊂ R[x]`
that is non-zero in the quotient `R / (P ∩ R) [x]`.  The assumptions are equivalent to
`P ≠ 0` and `P ∩ R = (0)`.
-/
/-
**Ideal.exists_nonzero_mem_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_nonzero_mem_of_ne_bot {P : Ideal R[X]} (Pb : P != ⊥) (hP : forall x
 : R, C x in P -> x = 0) : exists p : R[X], p in P ∧ Polynomial.map (Quotient.mk
 (P.comap (C : R ->+* R[X]))) p != 0
参数：Pb : P != ⊥；hP : forall x : R, C x in P -> x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.nonzero_mem_of_bot_lt`：nonzero_mem_of_bot_lt {p : Submodule R 
M} (bot_lt : ⊥ < p) : exists a : p, a != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.map_injective`：map_injective (hf : Function.Injective f) : Fu
nction.Injective (map f)
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K

--- 原说明 ---
This technical lemma asserts the existence of a polynomial `p` in an ideal `P ⊂ 
R[x]`
that is non-zero in the quotient `R / (P ∩ R) [x]`.  The assumptions are equival
ent to
`P ≠ 0` and `P ∩ R = (0)`.
-/
theorem exists_nonzero_mem_of_ne_bot {P : Ideal R[X]} (Pb : P ≠ ⊥) (hP : ∀ x : R, C x ∈ P → x = 0) :
    ∃ p : R[X], p ∈ P ∧ Polynomial.map (Quotient.mk (P.comap (C : R →+* R[X]))) p ≠ 0 := by
  obtain ⟨m, hm⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr Pb)
  refine ⟨m, Submodule.coe_mem m, fun pp0 => hm (Submodule.coe_eq_zero.mp ?_)⟩
  refine
    (injective_iff_map_eq_zero (Polynomial.mapRingHom (Ideal.Quotient.mk
      (P.comap (C : R →+* R[X]))))).mp
      ?_ _ pp0
  refine map_injective _ ((RingHom.injective_iff_ker_eq_bot (Ideal.Quotient.mk (P.comap C))).mpr ?_)
  rw [mk_ker]
  exact (Submodule.eq_bot_iff _).mpr fun x hx => hP x (mem_comap.mp hx)

end

section IsDomain

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S] {f : R →+* S} {I J : Ideal S}

/-
**Ideal.exists_coeff_ne_zero_mem_comap_of_root_mem** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal`。
形式化陈述：exists_coeff_ne_zero_mem_comap_of_root_mem [IsDomain S] {r : S} (r_ne_zero
 : r != 0) (hr : r in I) {p : R[X]} : p != 0 -> p.eval₂ f r = 0 -> exists i, p.c
oeff i != 0 ∧ p.coeff i in I.comap f
参数：r_ne_zero : r != 0；hr : r in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem`：exist
s_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {r : S} (r_non_zero_divis
or : forall {x}, x * r = 0 -> x = 0) (hr : r in I) {p :…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem exists_coeff_ne_zero_mem_comap_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r ≠ 0)
    (hr : r ∈ I) {p : R[X]} :
    p ≠ 0 → p.eval₂ f r = 0 → ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f :=
  exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
    (fun {_} h => Or.resolve_right (mul_eq_zero.mp h) r_ne_zero) hr
/-
**Ideal.exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff** 是 Mathlib 中的一个定理，
位于命名空间 `Ideal`。
形式化陈述：exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff [IsPrime I] (hIJ : I 
<= J) {r : S} (hr : r in (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotien
t.mk (I.comap f)) != 0) (hpI : p.eval₂ f r in I) : exists i, p.coeff i in (J.com
ap f : Set R) \ I.comap f
参数：hIJ : I <= J；hr : r in (J : Set S) \ I；p_ne_zero : p.map (Quotient.mk (I.coma
p f)) != 0；hpI : p.eval₂ f r in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Ideal.exists_coeff_ne_zero_mem_comap_of_root_mem`：exists_coeff_ne_zero_m
em_comap_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r != 0) (hr : r in I) {p 
: R[X]} : p != 0 -> p.eval₂ f r = 0 ->…
· 使用定理 `Ideal.mem_quotient_iff_mem`：mem_quotient_iff_mem {I J : Ideal R} [I.IsTw
oSided] (hIJ : I <= J) {x : R} : Quotient.mk I x in J.map (Quotient.mk I) ↔ x in
 J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
-/
theorem exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff [IsPrime I] (hIJ : I ≤ J) {r : S}
    (hr : r ∈ (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotient.mk (I.comap f)) ≠ 0)
    (hpI : p.eval₂ f r ∈ I) : ∃ i, p.coeff i ∈ (J.comap f : Set R) \ I.comap f := by
  obtain ⟨hrJ, hrI⟩ := hr
  have rbar_ne_zero : Ideal.Quotient.mk I r ≠ 0 := mt (Quotient.mk_eq_zero I).mp hrI
  have rbar_mem_J : Ideal.Quotient.mk I r ∈ J.map (Ideal.Quotient.mk I) := mem_map_of_mem _ hrJ
  have quotient_f : ∀ x ∈ I.comap f, (Ideal.Quotient.mk I).comp f x = 0 := by
    simp [Quotient.eq_zero_iff_mem]
  have rbar_root :
    (p.map (Ideal.Quotient.mk (I.comap f))).eval₂ (Quotient.lift (I.comap f) _ quotient_f)
        (Ideal.Quotient.mk I r) =
      0 := by
    convert! Quotient.eq_zero_iff_mem.mpr hpI
    exact _root_.trans (eval₂_map _ _ _) (hom_eval₂ p f (Ideal.Quotient.mk I) r).symm
  obtain ⟨i, ne_zero, mem⟩ :=
    exists_coeff_ne_zero_mem_comap_of_root_mem rbar_ne_zero rbar_mem_J p_ne_zero rbar_root
  rw [coeff_map] at ne_zero mem
  refine ⟨i, (mem_quotient_iff_mem hIJ).mp ?_, mt ?_ ne_zero⟩
  · simpa using mem
  simp [Quotient.eq_zero_iff_mem]
/-
**Ideal.comap_lt_comap_of_root_mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_lt_comap_of_root_mem_sdiff [I.IsPrime] (hIJ : I <= J) {r : S} (hr : 
r in (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotient.mk (I.comap f)) !=
 0) (hp : p.eval₂ f r in I) : I.comap f < J.comap f
参数：hIJ : I <= J；hr : r in (J : Set S) \ I；p_ne_zero : p.map (Quotient.mk (I.coma
p f)) != 0；hp : p.eval₂ f r in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff`：exists_coeff
_mem_comap_sdiff_comap_of_root_mem_sdiff [IsPrime I] (hIJ : I <= J) {r : S} (hr 
: r in (J : Set S) \ I) {p : R[X]} (p_ne_zero : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
-/
theorem comap_lt_comap_of_root_mem_sdiff [I.IsPrime] (hIJ : I ≤ J) {r : S}
    (hr : r ∈ (J : Set S) \ I) {p : R[X]} (p_ne_zero : p.map (Quotient.mk (I.comap f)) ≠ 0)
    (hp : p.eval₂ f r ∈ I) : I.comap f < J.comap f :=
  let ⟨i, hJ, hI⟩ := exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff hIJ hr p_ne_zero hp
  SetLike.lt_iff_le_and_exists.mpr ⟨comap_mono hIJ, p.coeff i, hJ, hI⟩
/-
**Ideal.mem_of_one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_of_one_mem (h : (1 : S) in I) (x) : x in I
参数：h : (1 : S) in I；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
-/
theorem mem_of_one_mem (h : (1 : S) ∈ I) (x) : x ∈ I :=
  (I.eq_top_iff_one.mpr h).symm ▸ mem_top
/-
**Ideal.comap_lt_comap_of_integral_mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_lt_comap_of_integral_mem_sdiff [Algebra R S] [hI : I.IsPrime] (hIJ :
 I <= J) {x : S} (mem : x in (J : Set S) \ I) (integral : IsIntegral R x) : I.co
map (algebraMap R S) < J.comap (algebraMap R S)
参数：hIJ : I <= J；mem : x in (J : Set S) \ I；integral : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_lt_comap_of_root_mem_sdiff`：comap_lt_comap_of_root_mem_sdiff
 [I.IsPrime] (hIJ : I <= J) {r : S} (hr : r in (J : Set S) \ I) {p : R[X]} (p_ne
_zero : p.map (Quotient.mk (…
· 使用定理 `Polynomial.map_monic_ne_zero`：map_monic_ne_zero (hp : p.Monic) [Nontrivi
al S] : p.map f != 0
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
theorem comap_lt_comap_of_integral_mem_sdiff [Algebra R S] [hI : I.IsPrime] (hIJ : I ≤ J) {x : S}
    (mem : x ∈ (J : Set S) \ I) (integral : IsIntegral R x) :
    I.comap (algebraMap R S) < J.comap (algebraMap R S) := by
  obtain ⟨p, p_monic, hpx⟩ := integral
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem (map_monic_ne_zero p_monic) ?_
  convert! I.zero_mem
/-
**Ideal.comap_ne_bot_of_root_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_ne_bot_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r != 0) (hr : r
 in I) {p : R[X]} (p_ne_zero : p != 0) (hp : p.eval₂ f r = 0) : I.comap f != ⊥
参数：r_ne_zero : r != 0；hr : r in I；p_ne_zero : p != 0；hp : p.eval₂ f r = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_coeff_ne_zero_mem_comap_of_root_mem`：exists_coeff_ne_zero_m
em_comap_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r != 0) (hr : r in I) {p 
: R[X]} : p != 0 -> p.eval₂ f r = 0 ->…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
theorem comap_ne_bot_of_root_mem [IsDomain S] {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I) {p : R[X]}
    (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0) : I.comap f ≠ ⊥ := fun h =>
  let ⟨_, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp
  absurd (mem_bot.mp (eq_bot_iff.mp h mem)) hi
/-
**Ideal.isMaximal_of_isIntegral_of_isMaximal_comap** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal`。
形式化陈述：isMaximal_of_isIntegral_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegr
al R S] (I : Ideal S) [I.IsPrime] (hI : IsMaximal (I.comap (algebraMap R S))) : 
IsMaximal I
参数：I : Ideal S；hI : IsMaximal (I.comap (algebraMap R S))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.comap_eq_top_iff`：comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔
 I = ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.comap_lt_comap_of_integral_mem_sdiff`：comap_lt_comap_of_integral_m
em_sdiff [Algebra R S] [hI : I.IsPrime] (hIJ : I <= J) {x : S} (mem : x in (J : 
Set S) \ I) (integral : IsIntegr…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem isMaximal_of_isIntegral_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S]
    (I : Ideal S) [I.IsPrime] (hI : IsMaximal (I.comap (algebraMap R S))) : IsMaximal I :=
  ⟨⟨mt comap_eq_top_iff.mpr hI.1.1, fun _ I_lt_J =>
      let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
      comap_eq_top_iff.1 <|
        hI.1.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩
          (Algebra.IsIntegral.isIntegral x))⟩⟩
/-
**Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：isMaximal_of_isIntegral_of_isMaximal_comap' (f : R ->+* S) (hf : f.IsInteg
ral) (I : Ideal S) [I.IsPrime] (hI : IsMaximal (I.comap f)) : IsMaximal I
参数：f : R ->+* S；hf : f.IsIntegral；I : Ideal S；hI : IsMaximal (I.comap f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`：isMaximal_of_isIntegra
l_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S] (I : Ideal S) [I.IsP
rime] (hI : IsMaximal (I.comap (algebr…
-/
theorem isMaximal_of_isIntegral_of_isMaximal_comap' (f : R →+* S) (hf : f.IsIntegral) (I : Ideal S)
    [I.IsPrime] (hI : IsMaximal (I.comap f)) : IsMaximal I :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_of_isIntegral_of_isMaximal_comap (R := R) (S := S) I hI

variable [Algebra R S]
/-
**Ideal.comap_ne_bot_of_algebraic_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_ne_bot_of_algebraic_mem [IsDomain S] {x : S} (x_ne_zero : x != 0) (x
_mem : x in I) (hx : IsAlgebraic R x) : I.comap (algebraMap R S) != ⊥
参数：x_ne_zero : x != 0；x_mem : x in I；hx : IsAlgebraic R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_ne_bot_of_root_mem`：comap_ne_bot_of_root_mem [IsDomain S] {r
 : S} (r_ne_zero : r != 0) (hr : r in I) {p : R[X]} (p_ne_zero : p != 0) (hp : p
.eval₂ f r = 0) : I.…
-/
theorem comap_ne_bot_of_algebraic_mem [IsDomain S] {x : S} (x_ne_zero : x ≠ 0) (x_mem : x ∈ I)
    (hx : IsAlgebraic R x) : I.comap (algebraMap R S) ≠ ⊥ :=
  let ⟨_, p_ne_zero, hp⟩ := hx
  comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp
/-
**Ideal.comap_ne_bot_of_integral_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：comap_ne_bot_of_integral_mem [Nontrivial R] [IsDomain S] {x : S} (x_ne_zer
o : x != 0) (x_mem : x in I) (hx : IsIntegral R x) : I.comap (algebraMap R S) !=
 ⊥
参数：x_ne_zero : x != 0；x_mem : x in I；hx : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_ne_bot_of_algebraic_mem`：comap_ne_bot_of_algebraic_mem [IsDo
main S] {x : S} (x_ne_zero : x != 0) (x_mem : x in I) (hx : IsAlgebraic R x) : I
.comap (algebraMap R S) !…
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
-/
theorem comap_ne_bot_of_integral_mem [Nontrivial R] [IsDomain S] {x : S} (x_ne_zero : x ≠ 0)
    (x_mem : x ∈ I) (hx : IsIntegral R x) : I.comap (algebraMap R S) ≠ ⊥ :=
  comap_ne_bot_of_algebraic_mem x_ne_zero x_mem hx.isAlgebraic
/-
**Ideal.eq_bot_of_comap_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_bot_of_comap_eq_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S
] (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥
参数：hI : I.comap (algebraMap R S) = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_ne_bot_of_integral_mem`：comap_ne_bot_of_integral_mem [Nontri
vial R] [IsDomain S] {x : S} (x_ne_zero : x != 0) (x_mem : x in I) (hx : IsInteg
ral R x) : I.comap (alge…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem eq_bot_of_comap_eq_bot [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S]
    (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  by_cases hx0 : x = 0
  · exact hx0.symm ▸ Ideal.zero_mem ⊥
  · exact absurd hI (comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x))
/-
**Ideal.isMaximal_comap_of_isIntegral_of_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal`。
形式化陈述：isMaximal_comap_of_isIntegral_of_isMaximal [Algebra.IsIntegral R S] (I : I
deal S) [hI : I.IsMaximal] : IsMaximal (I.comap (algebraMap R S))
参数：I : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.maximal_of_isField`：maximal_of_isField {R} [CommRing R] (
I : Ideal R) (hqf : IsField (R ⧸ I)) : I.IsMaximal
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `isField_of_isIntegral_of_isField`：isField_of_isIntegral_of_isField (hRS 
: Function.Injective (algebraMap R S)) (hS : IsField S) : IsField R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.algebraMap_quotient_injective`：algebraMap_quotient_injective {R} [
CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] : Function.Injective (alg
ebraMap (R ⧸ I.comap (alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.maximal_ideal_iff_isField_quotient`：maximal_ideal_iff_isF
ield_quotient {R} [CommRing R] (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I)
-/
theorem isMaximal_comap_of_isIntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S)
    [hI : I.IsMaximal] : IsMaximal (I.comap (algebraMap R S)) := by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  have : IsPrime (I.comap (algebraMap R S)) := comap_isPrime _ _
  exact isField_of_isIntegral_of_isField
    algebraMap_quotient_injective (by rwa [← Quotient.maximal_ideal_iff_isField_quotient])
/-
**Ideal.isMaximal_comap_of_isIntegral_of_isMaximal'** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：isMaximal_comap_of_isIntegral_of_isMaximal' {R S : Type*} [CommRing R] [Co
mmRing S] (f : R ->+* S) (hf : f.IsIntegral) (I : Ideal S) [I.IsMaximal] : IsMax
imal (I.comap f)
参数：f : R ->+* S；hf : f.IsIntegral；I : Ideal S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`：isMaximal_comap_of_isI
ntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S) [hI : I.IsMaximal] :
 IsMaximal (I.comap (algebraMap R S))
-/
theorem isMaximal_comap_of_isIntegral_of_isMaximal' {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (I : Ideal S) [I.IsMaximal] : IsMaximal (I.comap f) :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := S) I

section IsIntegral

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

/-
**Ideal.IsIntegral.comap_lt_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsIntegral`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {A : Type u_3} [inst_1 : CommRing A] 
[inst_2 : Algebra R A]   [Algebra.IsIntegral R A] {I J : Ideal A} [I.IsPrime],  
 I < J → Ideal.comap (algebraMap R A) I < Ideal.comap (algebraMap R A) J
参数：algebraMap R A；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ideal.comap_lt_comap_of_integral_mem_sdiff`：comap_lt_comap_of_integral_m
em_sdiff [Algebra R S] [hI : I.IsPrime] (hIJ : I <= J) {x : S} (mem : x in (J : 
Set S) \ I) (integral : IsIntegr…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem IsIntegral.comap_lt_comap {I J : Ideal A} [I.IsPrime] (I_lt_J : I < J) :
    I.comap (algebraMap R A) < J.comap (algebraMap R A) :=
  let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_le_comap :=
  IsIntegral.comap_lt_comap
/-
**Ideal.IsIntegral.isMaximal_of_isMaximal_comap** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
.IsIntegral`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {A : Type u_3} [inst_1 : CommRing A] 
[inst_2 : Algebra R A]   [Algebra.IsIntegral R A] (I : Ideal A) [I.IsPrime], (Id
eal.comap (algebraMap R A) I).IsMaximal → I.IsMaximal
参数：I : Ideal A；Ideal.comap (algebraMap R A) I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`：isMaximal_of_isIntegra
l_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S] (I : Ideal S) [I.IsP
rime] (hI : IsMaximal (I.comap (algebr…
-/
theorem IsIntegral.isMaximal_of_isMaximal_comap (I : Ideal A) [I.IsPrime]
    (hI : IsMaximal (I.comap (algebraMap R A))) : IsMaximal I :=
  isMaximal_of_isIntegral_of_isMaximal_comap I hI

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.isMaximal_of_isMaximal_comap :=
  IsIntegral.isMaximal_of_isMaximal_comap
/-
**Ideal.IsIntegral.mem_minimalPrimes_map_under** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.
IsIntegral`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {A : Type u_3} [inst_1 : CommRing A] 
[inst_2 : Algebra R A]   [Algebra.IsIntegral R A] (I : Ideal A) [I.IsPrime], I ∈
 (Ideal.map (algebraMap R A) (Ideal.under R I)).minimalPrimes
参数：I : Ideal A；Ideal.map (algebraMap R A) (Ideal.under R I)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Ideal.IsIntegral.comap_lt_comap`：∀ {R : Type u_1} [inst : CommRing R] {A
 : Type u_3} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.IsIntegral 
R A] {I J : Ideal A} …
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
-/
theorem IsIntegral.mem_minimalPrimes_map_under (I : Ideal A) [I.IsPrime] :
    I ∈ ((I.under R).map (algebraMap R A)).minimalPrimes := by
  refine ⟨⟨inferInstance, map_comap_le⟩, fun r ⟨hr, hpr⟩ hrq ↦ ?_⟩
  contrapose! hpr
  exact mt map_le_iff_le_comap.mp (not_le_of_gt (IsIntegral.comap_lt_comap (hrq.lt_of_not_ge hpr)))

variable [IsDomain A]

variable (R) in
/-
**Ideal.IsIntegral.comap_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsIntegral`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] {A : Type u_3} [inst_1 : CommRing A] 
[inst_2 : Algebra R A]   [Algebra.IsIntegral R A] [IsDomain A] [Nontrivial R] {I
 : Ideal A}, I ≠ ⊥ → Ideal.comap (algebraMap R A) I ≠ ⊥
参数：R : Type u_1；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Ideal.comap_ne_bot_of_integral_mem`：comap_ne_bot_of_integral_mem [Nontri
vial R] [IsDomain S] {x : S} (x_ne_zero : x != 0) (x_mem : x in I) (hx : IsInteg
ral R x) : I.comap (alge…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem IsIntegral.comap_ne_bot [Nontrivial R] {I : Ideal A} (I_ne_bot : I ≠ ⊥) :
    I.comap (algebraMap R A) ≠ ⊥ :=
  let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot
  comap_ne_bot_of_integral_mem x_ne_zero x_mem (Algebra.IsIntegral.isIntegral x)

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.comap_ne_bot :=
  IsIntegral.comap_ne_bot

variable (R) in
/-
**Ideal.IsIntegral.eq_bot_of_comap_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsInt
egral`。
形式化陈述：∀ (R : Type u_1) [inst : CommRing R] {A : Type u_3} [inst_1 : CommRing A] 
[inst_2 : Algebra R A]   [Algebra.IsIntegral R A] [IsDomain A] [Nontrivial R] {I
 : Ideal A}, Ideal.comap (algebraMap R A) I = ⊥ → I = ⊥
参数：R : Type u_1；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Ideal.IsIntegral.comap_ne_bot`：∀ (R : Type u_1) [inst : CommRing R] {A :
 Type u_3} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.IsIntegral R 
A] [IsDomain A] [No…
-/
theorem IsIntegral.eq_bot_of_comap_eq_bot [Nontrivial R] {I : Ideal A} :
    I.comap (algebraMap R A) = ⊥ → I = ⊥ := by
  contrapose
  exact IsIntegral.comap_ne_bot R

@[deprecated (since := "2026-05-08")] alias IsIntegralClosure.eq_bot_of_comap_eq_bot :=
    IsIntegral.eq_bot_of_comap_eq_bot

end IsIntegral

@[deprecated (since := "2026-05-08")] alias IntegralClosure.comap_lt_comap :=
  IsIntegral.comap_lt_comap

@[deprecated (since := "2026-05-08")] alias IntegralClosure.isMaximal_of_isMaximal_comap :=
  IsIntegral.isMaximal_of_isMaximal_comap

section

variable [IsDomain S]

@[deprecated (since := "2026-05-08")] alias IntegralClosure.comap_ne_bot := IsIntegral.comap_ne_bot

@[deprecated (since := "2026-05-08")] alias IntegralClosure.eq_bot_of_comap_eq_bot :=
  IsIntegral.eq_bot_of_comap_eq_bot

/-- `comap (algebraMap R S)` is a surjection from the prime spec of `R` to prime spec of `S`.
`hP : (algebraMap R S).ker ≤ P` is a slight generalization of the extension being injective -/
/-
**Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain** 是 Mathlib 中的一个定理，位于命
名空间 `Ideal`。
形式化陈述：exists_ideal_over_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S]
 (P : Ideal R) [IsPrime P] (hP : RingHom.ker (algebraMap R S) <= P) : exists Q :
 Ideal S, IsPrime Q ∧ Q.comap (algebraMap R S) = P
参数：P : Ideal R；hP : RingHom.ker (algebraMap R S) <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isDomain_localization`：isDomain_localization {M : Submono
id R} (hM : M <= nonZeroDivisors R) : IsDomain (Localization M)
· 使用定理 `le_nonZeroDivisors_of_noZeroDivisors`：le_nonZeroDivisors_of_noZeroDiviso
rs {S : Submonoid M₀} (hS : (0 : M₀) ∉ S) : S <= M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.exists_maximal`：exists_maximal [Nontrivial α] : exists M : Ideal α
, M.IsMaximal
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `isIntegral_localization`：isIntegral_localization [Algebra.IsIntegral R S
] : (map Sₘ (algebraMap R S) (show _ <= (Algebra.algebraMapSubmonoid S M).comap 
_ from M.le_c…
· 使用定理 `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`：isMaximal_comap_of_isI
ntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S) [hI : I.IsMaximal] :
 IsMaximal (I.comap (algebraMap R S))
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `Localization.AtPrime.under_maximalIdeal`：∀ {R : Type u_1} [inst : CommSe
miring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.under R (IsLocalRing.maximalId
eal (Localization I.primeComp…

--- 原说明 ---
`comap (algebraMap R S)` is a surjection from the prime spec of `R` to prime spe
c of `S`.
`hP : (algebraMap R S).ker ≤ P` is a slight generalization of the extension bein
g injective
-/
theorem exists_ideal_over_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S] (P : Ideal R)
    [IsPrime P] (hP : RingHom.ker (algebraMap R S) ≤ P) :
    ∃ Q : Ideal S, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have hP0 : (0 : S) ∉ Algebra.algebraMapSubmonoid S P.primeCompl := by
    rintro ⟨x, ⟨hx, x0⟩⟩
    exact absurd (hP x0) hx
  let Rₚ := Localization P.primeCompl
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S P.primeCompl)
  let : IsDomain (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :=
    IsLocalization.isDomain_localization (le_nonZeroDivisors_of_noZeroDivisors hP0)
  obtain ⟨Qₚ : Ideal Sₚ, Qₚ_maximal⟩ := exists_maximal Sₚ
  have : Algebra.IsIntegral Rₚ Sₚ := ⟨isIntegral_localization⟩
  have Qₚ_max : IsMaximal (comap _ Qₚ) :=
    isMaximal_comap_of_isIntegral_of_isMaximal (R := Rₚ) (S := Sₚ) Qₚ
  refine ⟨comap (algebraMap S Sₚ) Qₚ, ⟨comap_isPrime _ Qₚ, ?_⟩⟩
  convert! Localization.AtPrime.under_maximalIdeal (I := P)
  rw [comap_comap, ← IsLocalRing.eq_maximalIdeal Qₚ_max,
    ← IsLocalization.map_comp (P := S) (Q := Sₚ) (g := algebraMap R S)
    (M := P.primeCompl) (T := Algebra.algebraMapSubmonoid S P.primeCompl) (S := Rₚ)
    (fun p hp => Algebra.mem_algebraMapSubmonoid_of_mem ⟨p, hp⟩)]
  rfl

end

/-- More general going-up theorem than `exists_ideal_over_prime_of_isIntegral_of_isDomain`.
Generalized to arbitrary length chains in `Ideal.exists_ltSeries_of_hasGoingUp`. -/
/-
**Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime** 是 Mathlib 中的一个定理，位于命名
空间 `Ideal`。
形式化陈述：exists_ideal_over_prime_of_isIntegral_of_isPrime [Algebra.IsIntegral R S] 
(P : Ideal R) [IsPrime P] (I : Ideal S) [IsPrime I] (hIP : I.comap (algebraMap R
 S) <= P) : exists Q >= I, IsPrime Q ∧ Q.comap (algebraMap R S) = P
参数：P : Ideal R；I : Ideal S；hIP : I.comap (algebraMap R S) <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain`：exists_ideal_ov
er_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S] (P : Ideal R) [IsPri
me P] (hP : RingHom.ker (algebraMap R S) <= P…
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `Ideal.algebraMap_quotient_injective`：algebraMap_quotient_injective {R} [
CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] : Function.Injective (alg
ebraMap (R ⧸ I.comap (alg…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ker_le_comap`：ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f <
= comap f K
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a

--- 原说明 ---
More general going-up theorem than `exists_ideal_over_prime_of_isIntegral_of_isD
omain`.
Generalized to arbitrary length chains in `Ideal.exists_ltSeries_of_hasGoingUp`.
-/
theorem exists_ideal_over_prime_of_isIntegral_of_isPrime
    [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) [IsPrime I] (hIP : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q' : Ideal (S ⧸ I), ⟨Q'_prime, hQ'⟩⟩ :=
    @exists_ideal_over_prime_of_isIntegral_of_isDomain (R ⧸ I.comap (algebraMap R S)) _ (S ⧸ I) _
      Ideal.quotientAlgebra _ _
      (map (Ideal.Quotient.mk (I.comap (algebraMap R S))) P)
      (map_isPrime_of_surjective Quotient.mk_surjective (by simp [hIP]))
      (le_trans (le_of_eq ((RingHom.injective_iff_ker_eq_bot _).1 algebraMap_quotient_injective))
        bot_le)
  refine ⟨Q'.comap _, le_trans (le_of_eq mk_ker.symm) (ker_le_comap _), ⟨comap_isPrime _ Q', ?_⟩⟩
  rw [comap_comap]
  refine _root_.trans ?_ (_root_.trans (congr_arg (comap (Ideal.Quotient.mk
    (comap (algebraMap R S) I))) hQ') ?_)
  · rw [comap_comap]
    exact congr_arg (comap · Q') (RingHom.ext fun r => rfl)
  · refine _root_.trans (comap_map_of_surjective _ Quotient.mk_surjective _) (sup_eq_left.2 ?_)
    simpa [← RingHom.ker_eq_comap_bot] using hIP
/-
**Ideal.exists_ideal_over_prime_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_ideal_over_prime_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal 
R) [IsPrime P] (I : Ideal S) (hIP : I.comap (algebraMap R S) <= P) : exists Q >=
 I, IsPrime Q ∧ Q.comap (algebraMap R S) = P
参数：P : Ideal R；I : Ideal S；hIP : I.comap (algebraMap R S) <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.exists_ideal_comap_le_prime`：exists_ideal_comap_le_prime {S} [Comm
Semiring S] [FunLike F R S] [RingHomClass F R S] {f : F} (P : Ideal R) [P.IsPrim
e] (I : Ideal S) (le : …
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`：exists_ideal_ove
r_prime_of_isIntegral_of_isPrime [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime
 P] (I : Ideal S) [IsPrime I] (hIP : I.comap…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem exists_ideal_over_prime_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P]
    (I : Ideal S) (hIP : I.comap (algebraMap R S) ≤ P) :
    ∃ Q ≥ I, IsPrime Q ∧ Q.comap (algebraMap R S) = P := by
  have ⟨P', hP, hP', hP''⟩ := exists_ideal_comap_le_prime P I hIP
  obtain ⟨Q, hQ, hQ', hQ''⟩ := exists_ideal_over_prime_of_isIntegral_of_isPrime P P' hP''
  exact ⟨Q, hP.trans hQ, hQ', hQ''⟩
/-
**Ideal.nonempty_primesOver** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：nonempty_primesOver [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal
 R) [P.IsPrime] : Nonempty (primesOver P S)
参数：P : Ideal R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral`：exists_ideal_over_prime_of_
isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P] (I : Ideal S) (hIP
 : I.comap (algebraMap R S) <= P)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FaithfulSMul.ker_algebraMap_eq_bot`：FaithfulSMul.ker_algebraMap_eq_bot (
R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A] : Ri
ngHom.ker (algebraMap R …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance nonempty_primesOver [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal R) [P.IsPrime] :
    Nonempty (primesOver P S) := by
  obtain ⟨Q, _, hQ₁, hQ₂⟩ := exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal S)
    (by simp [← RingHom.ker_eq_comap_bot])
  exact ⟨Q, ⟨hQ₁, (liesOver_iff _ _).mpr hQ₂.symm⟩⟩

/-- `comap (algebraMap R S)` is a surjection from the max spec of `S` to max spec of `R`.
`hP : (algebraMap R S).ker ≤ P` is a slight generalization of the extension being injective -/
/-
**Ideal.exists_ideal_over_maximal_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：exists_ideal_over_maximal_of_isIntegral [Algebra.IsIntegral R S] (P : Idea
l R) [P_max : IsMaximal P] (hP : RingHom.ker (algebraMap R S) <= P) : exists Q :
 Ideal S, IsMaximal Q ∧ Q.comap (algebraMap R S) = P
参数：P : Ideal R；hP : RingHom.ker (algebraMap R S) <= P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral`：exists_ideal_over_prime_of_
isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime P] (I : Ideal S) (hIP
 : I.comap (algebraMap R S) <= P)…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`：isMaximal_of_isIntegra
l_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S] (I : Ideal S) [I.IsP
rime] (hI : IsMaximal (I.comap (algebr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`comap (algebraMap R S)` is a surjection from the max spec of `S` to max spec of
 `R`.
`hP : (algebraMap R S).ker ≤ P` is a slight generalization of the extension bein
g injective
-/
theorem exists_ideal_over_maximal_of_isIntegral [Algebra.IsIntegral R S]
    (P : Ideal R) [P_max : IsMaximal P] (hP : RingHom.ker (algebraMap R S) ≤ P) :
    ∃ Q : Ideal S, IsMaximal Q ∧ Q.comap (algebraMap R S) = P := by
  obtain ⟨Q, -, Q_prime, hQ⟩ := exists_ideal_over_prime_of_isIntegral P ⊥ hP
  exact ⟨Q, isMaximal_of_isIntegral_of_isMaximal_comap _ (hQ.symm ▸ P_max), hQ⟩
/-
**Ideal.exists_maximal_ideal_liesOver_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：exists_maximal_ideal_liesOver_of_isIntegral [Algebra.IsIntegral R S] [Fait
hfulSMul R S] (P : Ideal R) [P.IsMaximal] : exists (Q : Ideal S), Q.IsMaximal ∧ 
Q.LiesOver P
参数：P : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ideal.exists_ideal_over_maximal_of_isIntegral`：exists_ideal_over_maximal
_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [P_max : IsMaximal P] (hP 
: RingHom.ker (algebraMap R S) <= P…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
theorem exists_maximal_ideal_liesOver_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (P : Ideal R) [P.IsMaximal] :
    ∃ (Q : Ideal S), Q.IsMaximal ∧ Q.LiesOver P := by
  simp_rw [liesOver_iff, eq_comm (a := P)]
  exact exists_ideal_over_maximal_of_isIntegral P (by
    simp [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])
/-
**Ideal.map_eq_top_iff_of_ker_le** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：map_eq_top_iff_of_ker_le {R S} [CommRing R] [CommRing S] (f : R ->+* S) {I
 : Ideal R} (hf₁ : RingHom.ker f <= I) (hf₂ : f.IsIntegral) : I.map f = ⊤ ↔ I = 
⊤
参数：f : R ->+* S；hf₁ : RingHom.ker f <= I；hf₂ : f.IsIntegral。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.exists_ideal_over_maximal_of_isIntegral`：exists_ideal_over_maximal
_of_isIntegral [Algebra.IsIntegral R S] (P : Ideal R) [P_max : IsMaximal P] (hP 
: RingHom.ker (algebraMap R S) <= P…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
-/
lemma map_eq_top_iff_of_ker_le {R S} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} (hf₁ : RingHom.ker f ≤ I) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ := by
  constructor; swap
  · rintro rfl; exact Ideal.map_top _
  contrapose
  intro h
  obtain ⟨m, _, hm⟩ := Ideal.exists_le_maximal I h
  let _ := f.toAlgebra
  have : Algebra.IsIntegral _ _ := ⟨hf₂⟩
  obtain ⟨m', _, rfl⟩ := exists_ideal_over_maximal_of_isIntegral m (hf₁.trans hm)
  rw [← map_le_iff_le_comap] at hm
  exact (hm.trans_lt (lt_top_iff_ne_top.mpr (IsMaximal.ne_top ‹_›))).ne
/-
**Ideal.map_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：map_eq_top_iff {R S} [CommRing R] [CommRing S] (f : R ->+* S) {I : Ideal R
} (hf₁ : Function.Injective f) (hf₂ : f.IsIntegral) : I.map f = ⊤ ↔ I = ⊤
参数：f : R ->+* S；hf₁ : Function.Injective f；hf₂ : f.IsIntegral。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.map_eq_top_iff_of_ker_le`：map_eq_top_iff_of_ker_le {R S} [CommRing
 R] [CommRing S] (f : R ->+* S) {I : Ideal R} (hf₁ : RingHom.ker f <= I) (hf₂ : 
f.IsIntegral) : I.ma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
-/
lemma map_eq_top_iff {R S} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} (hf₁ : Function.Injective f) (hf₂ : f.IsIntegral) :
    I.map f = ⊤ ↔ I = ⊤ :=
  map_eq_top_iff_of_ker_le f (by simp [(RingHom.injective_iff_ker_eq_bot f).mp hf₁]) hf₂

/-- If `S` is an integral `R`-algebra such that `q` is the unique prime of `S` lying over
a prime `p` of `R`, then any `x ∉ q` divides some `r ∉ p`. -/
/-
**Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton** 是 Mathlib 中的一个
引理，位于命名空间 `Ideal`。
形式化陈述：exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton {p : Ideal R} [p.I
sPrime] {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q}) [Algebra.IsIntegra
l R S] (x : S) (hx : x ∉ q) : exists r ∉ p, x ∣ algebraMap _ _ r
参数：hq : p.primesOver S = {q}；x : S；hx : x ∉ q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ideal.exists_le_prime_disjoint`：exists_le_prime_disjoint (S : Submonoid 
α) (disjoint : Disjoint (I : Set α) S) : exists p : Ideal α, p.IsPrime ∧ I <= p 
∧ Disjoint (p : Set …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime`：exists_ideal_ove
r_prime_of_isIntegral_of_isPrime [Algebra.IsIntegral R S] (P : Ideal R) [IsPrime
 P] (I : Ideal S) [IsPrime I] (hIP : I.comap…
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `S` is an integral `R`-algebra such that `q` is the unique prime of `S` lying
 over
a prime `p` of `R`, then any `x ∉ q` divides some `r ∉ p`.
-/
lemma exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton
    {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] (hq : p.primesOver S = {q})
    [Algebra.IsIntegral R S] (x : S) (hx : x ∉ q) : ∃ r ∉ p, x ∣ algebraMap _ _ r := by
  simp only [dvd_def, eq_comm, mul_comm x]
  by_contra!
  obtain ⟨Q, hQ, hxQ, hQp⟩ := Ideal.exists_le_prime_disjoint (.span {x})
    (Algebra.algebraMapSubmonoid _ p.primeCompl)
    (by simpa [Set.disjoint_iff_forall_ne, Ideal.mem_span_singleton',
      Algebra.algebraMapSubmonoid, @forall_comm S])
  have hQp' : Q.under _ ≤ p := by
    intro x hxQ
    by_contra hxp
    exact Set.subset_compl_iff_disjoint_right.mpr hQp hxQ ⟨x, hxp, rfl⟩
  obtain ⟨Q', hQ'Q, hQ', hQ'p⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime _ _ hQp'
  obtain rfl : Q' = q := hq.le ⟨hQ', ⟨hQ'p.symm⟩⟩
  exact hx (hQ'Q (hxQ (Ideal.mem_span_singleton_self _)))

end IsDomain

section IsIntegral

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
  (P : Ideal B) (p : Ideal A) [P.LiesOver p]

variable (A) in
/-- If `B` is an integral `A`-algebra, `P` is a maximal ideal of `B`, then the pull back of
  `P` is also a maximal ideal of `A`. -/
/-
**Ideal.IsMaximal.under** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_2} [inst_1 : CommRing B] 
[inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : Ideal B) [P.IsMaximal], (
Ideal.under A P).IsMaximal
参数：A : Type u_1；P : Ideal B；Ideal.under A P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`：isMaximal_comap_of_isI
ntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S) [hI : I.IsMaximal] :
 IsMaximal (I.comap (algebraMap R S))

--- 原说明 ---
If `B` is an integral `A`-algebra, `P` is a maximal ideal of `B`, then the pull 
back of
  `P` is also a maximal ideal of `A`.
-/
instance IsMaximal.under [P.IsMaximal] : (P.under A).IsMaximal :=
  isMaximal_comap_of_isIntegral_of_isMaximal P
/-
**Ideal.IsMaximal.of_liesOver_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaxim
al`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {B : Type u_2} [inst_1 : CommRing B] 
[inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : Ideal B) (p : Ideal A) [P
.LiesOver p] [hpm : p.IsMaximal] [P.IsPrime], P.IsMaximal
参数：P : Ideal B；p : Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap`：isMaximal_of_isIntegra
l_of_isMaximal_comap [Algebra R S] [Algebra.IsIntegral R S] (I : Ideal S) [I.IsP
rime] (hI : IsMaximal (I.comap (algebr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
-/
theorem IsMaximal.of_liesOver_isMaximal [hpm : p.IsMaximal] [P.IsPrime] : P.IsMaximal := by
  rw [P.over_def p] at hpm
  exact isMaximal_of_isIntegral_of_isMaximal_comap P hpm
/-
**Ideal.IsMaximal.of_isMaximal_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaxim
al`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {B : Type u_2} [inst_1 : CommRing B] 
[inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : Ideal B) (p : Ideal A) [P
.LiesOver p] [P.IsMaximal], p.IsMaximal
参数：P : Ideal B；p : Ideal A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`：isMaximal_comap_of_isI
ntegral_of_isMaximal [Algebra.IsIntegral R S] (I : Ideal S) [hI : I.IsMaximal] :
 IsMaximal (I.comap (algebraMap R S))
-/
theorem IsMaximal.of_isMaximal_liesOver [P.IsMaximal] : p.IsMaximal := by
  rw [P.over_def p]
  exact isMaximal_comap_of_isIntegral_of_isMaximal P

variable (A) in
/-
**Ideal.eq_bot_of_liesOver_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_bot_of_liesOver_bot [Nontrivial A] [IsDomain B] [h : P.LiesOver (⊥ : Id
eal A)] : P = ⊥
参数：⊥ : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.eq_bot_of_comap_eq_bot`：eq_bot_of_comap_eq_bot [Nontrivial R] [IsD
omain S] [Algebra.IsIntegral R S] (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
-/
theorem eq_bot_of_liesOver_bot [Nontrivial A] [IsDomain B] [h : P.LiesOver (⊥ : Ideal A)] :
    P = ⊥ :=
  eq_bot_of_comap_eq_bot <| ((liesOver_iff _ _).mp h).symm

variable (A) {P} in
/-
**Ideal.under_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：under_ne_bot [Nontrivial A] [IsDomain B] (hP : P != ⊥) : under A P != ⊥
参数：hP : P != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.eq_bot_of_comap_eq_bot`：eq_bot_of_comap_eq_bot [Nontrivial R] [IsD
omain S] [Algebra.IsIntegral R S] (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥
-/
theorem under_ne_bot [Nontrivial A] [IsDomain B] (hP : P ≠ ⊥) : under A P ≠ ⊥ :=
  fun h ↦ hP <| eq_bot_of_comap_eq_bot h

/-- `B ⧸ P` is an integral `A ⧸ p`-algebra if `B` is an integral `A`-algebra. -/
/-
**Ideal.Quotient.algebra_isIntegral_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
.Quotient`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {B : Type u_2} [inst_1 : CommRing B] 
[inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : Ideal B) (p : Ideal A) [i
nst_4 : P.LiesOver p], Algebra.IsIntegral (A ⧸ p) (B ⧸ P)
参数：P : Ideal B；p : Ideal A；A ⧸ p；B ⧸ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.tower_top`：Algebra.IsIntegral.tower_top [Algebra R S]
 [Algebra R T] [Algebra S T] [IsScalarTower R S T] [h : Algebra.IsIntegral R T] 
: Algebra.IsIntegr…
· 使用定理 `instIsIntegralQuotientIdeal`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] {I : Ideal A}   [Algebra.I
sIntegral R A], A…

--- 原说明 ---
`B ⧸ P` is an integral `A ⧸ p`-algebra if `B` is an integral `A`-algebra.
-/
instance Quotient.algebra_isIntegral_of_liesOver : Algebra.IsIntegral (A ⧸ p) (B ⧸ P) :=
  Algebra.IsIntegral.tower_top A

end IsIntegral

section IsIntegral

variable {A : Type*} [CommRing A] {p : Ideal A} [p.IsMaximal] {B : Type*} [CommRing B]
  [Algebra A B] [Algebra.IsIntegral A B] (Q : primesOver p B)

/-
**Ideal.primesOver.isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.primesOver`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {p : Ideal A} [p.IsMaximal] {B : Type
 u_2} [inst_2 : CommRing B]   [inst_3 : Algebra A B] [Algebra.IsIntegral A B] (Q
 : ↑(p.primesOver B)), (↑Q).IsMaximal
参数：Q : ↑(p.primesOver B)；↑Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.of_liesOver_isMaximal`：∀ {A : Type u_1} [inst : CommRing
 A] {B : Type u_2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsInt
egral A B] (P : Ideal B) (p…
· 使用定理 `Ideal.primesOver.liesOver`：∀ {A : Type u_2} [inst : CommSemiring A] (p :
 Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p
.primesOver B))…
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
-/
instance primesOver.isMaximal : Q.1.IsMaximal :=
  Ideal.IsMaximal.of_liesOver_isMaximal Q.1 p
/-
**Ideal.isMaximal_of_mem_primesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isMaximal_of_mem_primesOver {P : Ideal B} (hP : P in primesOver p B) : P.I
sMaximal
参数：hP : P in primesOver p B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.primesOver.isMaximal`：∀ {A : Type u_1} [inst : CommRing A] {p : Id
eal A} [p.IsMaximal] {B : Type u_2} [inst_2 : CommRing B]   [inst_3 : Algebra A 
B] [Algebra.IsIn…
-/
theorem isMaximal_of_mem_primesOver {P : Ideal B} (hP : P ∈ primesOver p B) : P.IsMaximal :=
  primesOver.isMaximal ⟨P, hP⟩

variable (A B) in
/-
**Ideal.primesOver_bot** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：primesOver_bot [Module.IsTorsionFree A B] [IsDomain A] [IsDomain B] : prim
esOver (⊥ : Ideal A) B = {⊥}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Ideal.eq_bot_of_comap_eq_bot`：eq_bot_of_comap_eq_bot [Nontrivial R] [IsD
omain S] [Algebra.IsIntegral R S] (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
lemma primesOver_bot [Module.IsTorsionFree A B] [IsDomain A] [IsDomain B] :
    primesOver (⊥ : Ideal A) B = {⊥} := by
  ext p
  refine ⟨fun ⟨_, ⟨h⟩⟩ ↦ p.eq_bot_of_comap_eq_bot h.symm, ?_⟩
  rintro rfl
  exact ⟨Ideal.isPrime_bot, Ideal.bot_liesOver_bot A B⟩

end IsIntegral

end Ideal

