/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

import Mathlib.RingTheory.Polynomial.Subring

/-!
# # Integral closure as a characteristic predicate

We prove basic properties of `IsIntegralClosure`.

-/

@[expose] public section

open Module Polynomial Submodule

section inv

open Algebra

variable {R S : Type*}

/-- A nonzero element in a domain integral over a field is a unit. -/
/-
**IsIntegral.isUnit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.isUnit [Field R] [Ring S] [IsDomain S] [Algebra R S] {x : S} (i
nt : IsIntegral R x) (h0 : x != 0) : IsUnit x
参数：int : IsIntegral R x；h0 : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
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
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用引理 `FiniteDimensional.isUnit`：FiniteDimensional.isUnit (F : Type*) {K : Type
*} [Field F] [Ring K] [IsDomain K] [Algebra F K] [FiniteDimensional F K] {x : K}
 (H : x != 0) …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2

--- 原说明 ---
A nonzero element in a domain integral over a field is a unit.
-/
theorem IsIntegral.isUnit [Field R] [Ring S] [IsDomain S] [Algebra R S] {x : S}
    (int : IsIntegral R x) (h0 : x ≠ 0) : IsUnit x :=
  have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  (FiniteDimensional.isUnit R (K := R[x])
    (x := ⟨x, subset_adjoin rfl⟩) <| mt Subtype.ext_iff.mp h0).map (R[x]).val

/-- A commutative domain that is an integral algebra over a field is a field. -/
/-
**isField_of_isIntegral_of_isField'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isField_of_isIntegral_of_isField' [CommRing R] [CommRing S] [IsDomain S] [
Algebra R S] [Algebra.IsIntegral R S] (hR : IsField R) : IsField S where exists_
pair_ne
参数：hR : IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsIntegral.isUnit`：IsIntegral.isUnit [Field R] [Ring S] [IsDomain S] [Al
gebra R S] {x : S} (int : IsIntegral R x) (h0 : x != 0) : IsUnit x
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Units.val_inv`：∀ {α : Type u} [inst : Monoid α] (self : αˣ), ↑self * sel
f.inv = 1

--- 原说明 ---
A commutative domain that is an integral algebra over a field is a field.
-/
theorem isField_of_isIntegral_of_isField' [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hR : IsField R) : IsField S where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    let := hR.toField
    obtain ⟨y, rfl⟩ := (Algebra.IsIntegral.isIntegral (R := R) x).isUnit hx
    exact ⟨y.inv, y.val_inv⟩

variable [Field R] [DivisionRing S] [Algebra R S] {x : S} {A : Subalgebra R S}
/-
**IsIntegral.inv_mem_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.inv_mem_adjoin (int : IsIntegral R x) : x⁻¹ in R[x]
参数：int : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Subalgebra.zero_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   0 ∈ S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用引理 `FiniteDimensional.exists_mul_eq_one`：FiniteDimensional.exists_mul_eq_one
 (F : Type*) {K : Type*} [Field F] [Ring K] [IsDomain K] [Algebra F K] [FiniteDi
mensional F K] {x : K} (H…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
-/
theorem IsIntegral.inv_mem_adjoin (int : IsIntegral R x) : x⁻¹ ∈ R[x] := by
  obtain rfl | h0 := eq_or_ne x 0
  · rw [inv_zero]; exact Subalgebra.zero_mem _
  have : FiniteDimensional R (R[x]) := .of_fg int.fg_adjoin_singleton
  obtain ⟨⟨y, hy⟩, h1⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := R[x]) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp h0)
  rwa [← mul_left_cancel₀ h0 ((Subtype.ext_iff.mp h1).trans (mul_inv_cancel₀ h0).symm)]

/-- The inverse of an integral element in a subalgebra of a division ring over a field
  also lies in that subalgebra. -/
/-
**IsIntegral.inv_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.inv_mem (int : IsIntegral R x) (hx : x in A) : x⁻¹ in A
参数：int : IsIntegral R x；hx : x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `IsIntegral.inv_mem_adjoin`：IsIntegral.inv_mem_adjoin (int : IsIntegral R
 x) : x⁻¹ in R[x]

--- 原说明 ---
The inverse of an integral element in a subalgebra of a division ring over a fie
ld
  also lies in that subalgebra.
-/
theorem IsIntegral.inv_mem (int : IsIntegral R x) (hx : x ∈ A) : x⁻¹ ∈ A :=
  adjoin_le (Set.singleton_subset_iff.mpr hx) int.inv_mem_adjoin

/-- An integral subalgebra of a division ring over a field is closed under inverses. -/
/-
**Algebra.IsIntegral.inv_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.inv_mem [Algebra.IsIntegral R A] (hx : x in A) : x⁻¹ in
 A
参数：hx : x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.inv_mem`：IsIntegral.inv_mem (int : IsIntegral R x) (hx : x in
 A) : x⁻¹ in A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
An integral subalgebra of a division ring over a field is closed under inverses.
-/
theorem Algebra.IsIntegral.inv_mem [Algebra.IsIntegral R A] (hx : x ∈ A) : x⁻¹ ∈ A :=
  ((isIntegral_algHom_iff A.val Subtype.val_injective).mpr <|
    Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : A)).inv_mem hx

/-- The inverse of an integral element in a division ring over a field is also integral. -/
/-
**IsIntegral.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹
参数：int : IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `IsIntegral.inv_mem_adjoin`：IsIntegral.inv_mem_adjoin (int : IsIntegral R
 x) : x⁻¹ in R[x]

--- 原说明 ---
The inverse of an integral element in a division ring over a field is also integ
ral.
-/
theorem IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹ :=
  .of_mem_of_fg _ int.fg_adjoin_singleton _ int.inv_mem_adjoin
/-
**IsIntegral.mem_of_inv_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.mem_of_inv_mem (int : IsIntegral R x) (inv_mem : x⁻¹ in A) : x 
in A
参数：int : IsIntegral R x；inv_mem : x⁻¹ in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `IsIntegral.inv_mem`：IsIntegral.inv_mem (int : IsIntegral R x) (hx : x in
 A) : x⁻¹ in A
· 使用定理 `IsIntegral.inv`：IsIntegral.inv (int : IsIntegral R x) : IsIntegral R x⁻¹
-/
theorem IsIntegral.mem_of_inv_mem (int : IsIntegral R x) (inv_mem : x⁻¹ ∈ A) : x ∈ A := by
  rw [← inv_inv x]; exact int.inv.inv_mem inv_mem

end inv

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] {f : R →+* S}

/-- The [Kurosh problem](https://en.wikipedia.org/wiki/Kurosh_problem) asks to show that
  this is still true when `A` is not necessarily commutative and `R` is a field, but it has
  been solved in the negative. See https://arxiv.org/pdf/1706.02383.pdf for criteria for a
  finitely generated algebraic (= integral) algebra over a field to be finite dimensional.

This could be an `instance`, but we tend to go from `Module.Finite` to `IsIntegral`/`IsAlgebraic`,
and making it an instance will cause the search to be complicated a lot.
-/
/-
**Algebra.IsIntegral.finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.finite [Algebra.IsIntegral R A] [h' : Algebra.FiniteTyp
e R A] : Module.Finite R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fg_adjoin_of_finite`：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (h
is : forall x in s, IsIntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
The [Kurosh problem](https://en.wikipedia.org/wiki/Kurosh_problem) asks to show 
that
  this is still true when `A` is not necessarily commutative and `R` is a field,
 but it has
  been solved in the negative. See https://arxiv.org/pdf/1706.02383.pdf for crit
eria for a
  finitely generated algebraic (= integral) algebra over a field to be finite di
mensional.

This could be an `instance`, but we tend to go from `Module.Finite` to `IsIntegr
al`/`IsAlgebraic`,
and making it an instance will cause the search to be complicated a lot.
-/
theorem Algebra.IsIntegral.finite [Algebra.IsIntegral R A] [h' : Algebra.FiniteType R A] :
    Module.Finite R A :=
  have ⟨s, hs⟩ := h'
  ⟨by apply hs ▸ fg_adjoin_of_finite s.finite_toSet fun x _ ↦ Algebra.IsIntegral.isIntegral x⟩

/-- finite = integral + finite type -/
/-
**Algebra.finite_iff_isIntegral_and_finiteType** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.finite_iff_isIntegral_and_finiteType : Module.Finite R A ↔ Algebra
.IsIntegral R A ∧ Algebra.FiniteType R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_finite`：IsIntegral.of_finite [Module.Finite R B] (x : B) :
 IsIntegral R x
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用定理 `Algebra.IsIntegral.finite`：Algebra.IsIntegral.finite [Algebra.IsIntegral
 R A] [h' : Algebra.FiniteType R A] : Module.Finite R A

--- 原说明 ---
finite = integral + finite type
-/
theorem Algebra.finite_iff_isIntegral_and_finiteType :
    Module.Finite R A ↔ Algebra.IsIntegral R A ∧ Algebra.FiniteType R A :=
  ⟨fun _ ↦ ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ ↦ h.finite⟩
/-
**RingHom.IsIntegral.to_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegral.to_finite (h : f.IsIntegral) (h' : f.FiniteType) : f.Fi
nite
参数：h : f.IsIntegral；h' : f.FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.finite`：Algebra.IsIntegral.finite [Algebra.IsIntegral
 R A] [h' : Algebra.FiniteType R A] : Module.Finite R A
-/
theorem RingHom.IsIntegral.to_finite (h : f.IsIntegral) (h' : f.FiniteType) : f.Finite :=
  let _ := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨h⟩
  Algebra.IsIntegral.finite (h' := h')

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite

/-- finite = integral + finite type -/
/-
**RingHom.finite_iff_isIntegral_and_finiteType** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.finite_iff_isIntegral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f
.FiniteType
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Finite.to_isIntegral`：RingHom.Finite.to_isIntegral (h : f.Finite
) : f.IsIntegral
· 使用定理 `RingHom.Finite.to_finiteType`：∀ {A : Type u_1} {B : Type u_2} [inst : Co
mmRing A] [inst_1 : CommRing B] {f : A →+* B}, f.Finite → f.FiniteType
· 使用定理 `RingHom.IsIntegral.to_finite`：RingHom.IsIntegral.to_finite (h : f.IsInte
gral) (h' : f.FiniteType) : f.Finite

--- 原说明 ---
finite = integral + finite type
-/
theorem RingHom.finite_iff_isIntegral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f.FiniteType :=
  ⟨fun h ↦ ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ ↦ h.to_finite h'⟩

variable (f : R →+* S) (R A)
/-
**mem_integralClosure_iff_mem_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_integralClosure_iff_mem_fg {r : A} : r in integralClosure R A ↔ exists
 M : Subalgebra R A, M.toSubmodule.FG ∧ r in M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
-/
theorem mem_integralClosure_iff_mem_fg {r : A} :
    r ∈ integralClosure R A ↔ ∃ M : Subalgebra R A, M.toSubmodule.FG ∧ r ∈ M :=
  ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, hr.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => .of_mem_of_fg M Hf _ hrM⟩

variable {R A}
/-
**adjoin_le_integralClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：adjoin_le_integralClosure {x : A} (hx : IsIntegral R x) : Algebra.adjoin R
 {x} <= integralClosure R A
参数：hx : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem adjoin_le_integralClosure {x : A} (hx : IsIntegral R x) :
    Algebra.adjoin R {x} ≤ integralClosure R A := by
  rw [Algebra.adjoin_le_iff]
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  exact hx
/-
**le_integralClosure_iff_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_integralClosure_iff_isIntegral {S : Subalgebra R A} : S <= integralClos
ure R A ↔ Algebra.IsIntegral R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.forall`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p : A
} {q : ↥p → Prop},   (∀ (x : ↥p), q x) ↔ ∀ (x : B) (h : x ∈ p), q ⟨x, h⟩
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用引理 `Algebra.isIntegral_def`：Algebra.isIntegral_def : Algebra.IsIntegral R A 
↔ forall x : A, IsIntegral R x
-/
theorem le_integralClosure_iff_isIntegral {S : Subalgebra R A} :
    S ≤ integralClosure R A ↔ Algebra.IsIntegral R S :=
  SetLike.forall.symm.trans <|
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective).trans
      Algebra.isIntegral_def.symm
/-
**Algebra.IsIntegral.adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.adjoin {S : Set A} (hS : forall x in S, IsIntegral R x)
 : Algebra.IsIntegral R (adjoin R S)
参数：hS : forall x in S, IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_integralClosure_iff_isIntegral`：le_integralClosure_iff_isIntegral {S 
: Subalgebra R A} : S <= integralClosure R A ↔ Algebra.IsIntegral R S
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
-/
theorem Algebra.IsIntegral.adjoin {S : Set A} (hS : ∀ x ∈ S, IsIntegral R x) :
    Algebra.IsIntegral R (adjoin R S) :=
  le_integralClosure_iff_isIntegral.mp <| adjoin_le hS
/-
**integralClosure_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure_eq_top_iff : integralClosure R A = ⊤ ↔ Algebra.IsIntegral 
R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `le_integralClosure_iff_isIntegral`：le_integralClosure_iff_isIntegral {S 
: Subalgebra R A} : S <= integralClosure R A ↔ Algebra.IsIntegral R S
· 使用定理 `AlgEquiv.isIntegral_iff`：AlgEquiv.isIntegral_iff (e : A ≃ₐ[R] B) : Algeb
ra.IsIntegral R A ↔ Algebra.IsIntegral R B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem integralClosure_eq_top_iff : integralClosure R A = ⊤ ↔ Algebra.IsIntegral R A := by
  rw [← top_le_iff, le_integralClosure_iff_isIntegral,
      (Subalgebra.topEquiv (R := R) (A := A)).isIntegral_iff] -- explicit arguments for speedup
/-
**Algebra.isIntegral_sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isIntegral_sup {S T : Subalgebra R A} : Algebra.IsIntegral R (S ⊔ 
T : Subalgebra R A) ↔ Algebra.IsIntegral R S ∧ Algebra.IsIntegral R T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Algebra.isIntegral_sup {S T : Subalgebra R A} :
    Algebra.IsIntegral R (S ⊔ T : Subalgebra R A) ↔
      Algebra.IsIntegral R S ∧ Algebra.IsIntegral R T := by
  simp_rw [← le_integralClosure_iff_isIntegral, sup_le_iff]
/-
**Algebra.isIntegral_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.isIntegral_iSup {ι} (S : ι -> Subalgebra R A) : Algebra.IsIntegral
 R ↑(iSup S) ↔ forall i, Algebra.IsIntegral R (S i)
参数：S : ι -> Subalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Algebra.isIntegral_iSup {ι} (S : ι → Subalgebra R A) :
    Algebra.IsIntegral R ↑(iSup S) ↔ ∀ i, Algebra.IsIntegral R (S i) := by
  simp_rw [← le_integralClosure_iff_isIntegral, iSup_le_iff]

/-- Mapping an integral closure along an `AlgEquiv` gives the integral closure. -/
/-
**integralClosure_map_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure_map_algEquiv [Algebra R S] (f : A ≃ₐ[R] S) : (integralClos
ure R A).map (f : A ->ₐ[R] S) = integralClosure R S
参数：f : A ≃ₐ[R] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.mem_map`：mem_map {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B
} : y in map f S ↔ exists x in S, f x = y
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping an integral closure along an `AlgEquiv` gives the integral closure.
-/
theorem integralClosure_map_algEquiv [Algebra R S] (f : A ≃ₐ[R] S) :
    (integralClosure R A).map (f : A →ₐ[R] S) = integralClosure R S := by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    use f.symm y, hy.map (f.symm : S →ₐ[R] A)
    simp

/-- An `AlgHom` between two rings restrict to an `AlgHom` between the integral closures inside
them. -/
/-
**AlgHom.mapIntegralClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.mapIntegralClosure [Algebra R S] (f : A ->ₐ[R] S) : integralClosure
 R A ->ₐ[R] integralClosure R S
参数：f : A ->ₐ[R] S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AlgHom` between two rings restrict to an `AlgHom` between the integral closu
res inside
them.
-/
def AlgHom.mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S) :
    integralClosure R A →ₐ[R] integralClosure R S :=
  (f.domRestrict (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]
/-
**AlgHom.coe_mapIntegralClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.coe_mapIntegralClosure [Algebra R S] (f : A ->ₐ[R] S) (x : integral
Closure R A) : (f.mapIntegralClosure x : S) = f (x : A)
参数：f : A ->ₐ[R] S；x : integralClosure R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AlgHom.coe_mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

/-- An `AlgEquiv` between two rings restrict to an `AlgEquiv` between the integral closures inside
them. -/
/-
**AlgEquiv.mapIntegralClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S) : integralClosur
e R A ≃ₐ[R] integralClosure R S
参数：f : A ≃ₐ[R] S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AlgEquiv` between two rings restrict to an `AlgEquiv` between the integral c
losures inside
them.
-/
def AlgEquiv.mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S) :
    integralClosure R A ≃ₐ[R] integralClosure R S :=
  AlgEquiv.ofAlgHom (f : A →ₐ[R] S).mapIntegralClosure (f.symm : S →ₐ[R] A).mapIntegralClosure
    (AlgHom.ext fun _ ↦ Subtype.ext (f.right_inv _))
    (AlgHom.ext fun _ ↦ Subtype.ext (f.left_inv _))

@[simp]
/-
**AlgEquiv.coe_mapIntegralClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.coe_mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S) (x : integra
lClosure R A) : (f.mapIntegralClosure x : S) = f (x : A)
参数：f : A ≃ₐ[R] S；x : integralClosure R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AlgEquiv.coe_mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl
/-
**integralClosure.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure.isIntegral (x : integralClosure R A) : IsIntegral R x
参数：x : integralClosure R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_algHom_apply`：aeval_algHom_apply {F : Type*} [FunLike F
 A B] [AlgHomClass F R A B] (f : F) (x : A) (p : R[X]) : aeval (f x) p = f (aeva
l x p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.val_apply`：val_apply (x : S) : S.val x = (x : A)
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
-/
theorem integralClosure.isIntegral (x : integralClosure R A) : IsIntegral R x :=
  let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
    Subtype.ext <| by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩
/-
**integralClosure.AlgebraIsIntegral** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：integralClosure.AlgebraIsIntegral : Algebra.IsIntegral R (integralClosure 
R A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `integralClosure.isIntegral`：integralClosure.isIntegral (x : integralClos
ure R A) : IsIntegral R x
-/
instance integralClosure.AlgebraIsIntegral : Algebra.IsIntegral R (integralClosure R A) :=
  ⟨integralClosure.isIntegral⟩
/-
**IsIntegral.of_mul_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_mul_unit {x y : B} {r : R} (hr : algebraMap R B r * y = 1) (
hx : IsIntegral R (x * y)) : IsIntegral R x
参数：hr : algebraMap R B r * y = 1；hx : IsIntegral R (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.monic_scaleRoots_iff`：monic_scaleRoots_iff {p : R[X]} (s : R)
 : Monic (scaleRoots p s) ↔ Monic p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.scaleRoots_aeval_eq_zero`：scaleRoots_aeval_eq_zero [Algebra R
 A] {p : R[X]} {a : A} {r : R} (ha : aeval a p = 0) : aeval (algebraMap R A r * 
a) (scaleRoots p r) = 0
-/
theorem IsIntegral.of_mul_unit {x y : B} {r : R} (hr : algebraMap R B r * y = 1)
    (hx : IsIntegral R (x * y)) : IsIntegral R x := by
  obtain ⟨p, p_monic, hp⟩ := hx
  refine ⟨scaleRoots p r, (monic_scaleRoots_iff r).2 p_monic, ?_⟩
  convert! scaleRoots_aeval_eq_zero hp
  rw [Algebra.commutes] at hr ⊢
  rw [mul_assoc, hr, mul_one]; rfl
/-
**RingHom.IsIntegralElem.of_mul_unit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegralElem.of_mul_unit (x y : S) (r : R) (hr : f r * y = 1) (h
x : f.IsIntegralElem (x * y)) : f.IsIntegralElem x
参数：x y : S；r : R；hr : f r * y = 1；hx : f.IsIntegralElem (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mul_unit`：IsIntegral.of_mul_unit {x y : B} {r : R} (hr : a
lgebraMap R B r * y = 1) (hx : IsIntegral R (x * y)) : IsIntegral R x
-/
theorem RingHom.IsIntegralElem.of_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
    (hx : f.IsIntegralElem (x * y)) : f.IsIntegralElem x :=
  letI : Algebra R S := f.toAlgebra
  IsIntegral.of_mul_unit hr hx

/-- Generalization of `IsIntegral.of_mem_closure` bootstrapped up from that lemma -/
/-
**IsIntegral.of_mem_closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_mem_closure' (G : Set A) (hG : forall x in G, IsIntegral R x
) : forall x in Subring.closure G, IsIntegral R x
参数：G : Set A；hG : forall x in G, IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.closure_induction`：closure_induction {s : Set R} {p : (x : R) ->
 x in closure s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_closure hx
)) (zero : p 0 …
· 使用定理 `isIntegral_zero`：isIntegral_zero [Algebra R B] : IsIntegral R (0 : B)
· 使用定理 `isIntegral_one`：isIntegral_one [Algebra R B] : IsIntegral R (1 : B)
· 使用定理 `IsIntegral.add`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.neg`：IsIntegral.neg {x : B} (hx : IsIntegral R x) : IsIntegra
l R (-x)
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …

--- 原说明 ---
Generalization of `IsIntegral.of_mem_closure` bootstrapped up from that lemma
-/
theorem IsIntegral.of_mem_closure' (G : Set A) (hG : ∀ x ∈ G, IsIntegral R x) :
    ∀ x ∈ Subring.closure G, IsIntegral R x := fun _ hx ↦
  Subring.closure_induction hG isIntegral_zero isIntegral_one (fun _ _ _ _ ↦ IsIntegral.add)
    (fun _ _ ↦ IsIntegral.neg) (fun _ _ _ _ ↦ IsIntegral.mul) hx
/-
**IsIntegral.of_mem_closure''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.of_mem_closure'' {S : Type*} [CommRing S] {f : R ->+* S} (G : S
et S) (hG : forall x in G, f.IsIntegralElem x) : forall x in Subring.closure G, 
f.IsIntegralElem x
参数：G : Set S；hG : forall x in G, f.IsIntegralElem x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mem_closure'`：IsIntegral.of_mem_closure' (G : Set A) (hG :
 forall x in G, IsIntegral R x) : forall x in Subring.closure G, IsIntegral R x
-/
theorem IsIntegral.of_mem_closure'' {S : Type*} [CommRing S] {f : R →+* S} (G : Set S)
    (hG : ∀ x ∈ G, f.IsIntegralElem x) : ∀ x ∈ Subring.closure G, f.IsIntegralElem x := fun x hx =>
  @IsIntegral.of_mem_closure' R S _ _ f.toAlgebra G hG x hx
/-
**IsIntegral.pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : IsIntegral R (x ^ 
n)
参数：h : IsIntegral R x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `Subalgebra.pow_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈
 S → ∀ (…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem IsIntegral.pow {x : B} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (x ^ n) :=
  .of_mem_of_fg _ h.fg_adjoin_singleton _ <|
    Subalgebra.pow_mem _ (by exact Algebra.subset_adjoin rfl) _
/-
**IsIntegral.nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.nsmul {x : B} (h : IsIntegral R x) (n : Nat) : IsIntegral R (n 
• x)
参数：h : IsIntegral R x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.smul`：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Alg
ebra S B] [Algebra R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S
 x) :…
-/
theorem IsIntegral.nsmul {x : B} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (n • x) :=
  h.smul n
/-
**IsIntegral.zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.zsmul {x : B} (h : IsIntegral R x) (n : Int) : IsIntegral R (n 
• x)
参数：h : IsIntegral R x；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.smul`：IsIntegral.smul {R} [CommSemiring R] [Algebra R B] [Alg
ebra S B] [Algebra R S] [IsScalarTower R S B] {x : B} (r : R) (hx : IsIntegral S
 x) :…
-/
theorem IsIntegral.zsmul {x : B} (h : IsIntegral R x) (n : ℤ) : IsIntegral R (n • x) :=
  h.smul n
/-
**IsIntegral.multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.multiset_prod {s : Multiset A} (h : forall x in s, IsIntegral R
 x) : IsIntegral R s.prod
参数：h : forall x in s, IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.multiset_prod_mem`：∀ {R : Type u} {A : Type v} [inst : CommSe
miring R] [inst_1 : CommSemiring A] [inst_2 : Algebra R A]   (S : Subalgebra R A
) {m : Multiset A}…
-/
theorem IsIntegral.multiset_prod {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.prod :=
  (integralClosure R A).multiset_prod_mem h
/-
**IsIntegral.multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.multiset_sum {s : Multiset A} (h : forall x in s, IsIntegral R 
x) : IsIntegral R s.sum
参数：h : forall x in s, IsIntegral R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.multiset_sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {m 
: Multiset A}, (∀…
-/
theorem IsIntegral.multiset_sum {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.sum :=
  (integralClosure R A).multiset_sum_mem h
/-
**IsIntegral.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.prod {α : Type*} {s : Finset α} (f : α -> A) (h : forall x in s
, IsIntegral R (f x)) : IsIntegral R (∏ x in s, f x)
参数：f : α -> A；h : forall x in s, IsIntegral R (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.prod_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring A] [inst_2 : Algebra R A]   (S : Subalgebra R A) {ι : Ty
pe w} {t …
-/
theorem IsIntegral.prod {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∏ x ∈ s, f x) :=
  (integralClosure R A).prod_mem h
/-
**IsIntegral.sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (h : forall x in s,
 IsIntegral R (f x)) : IsIntegral R (∑ x in s, f x)
参数：f : α -> A；h : forall x in s, IsIntegral R (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w}
 {t : Fi…
-/
theorem IsIntegral.sum {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∑ x ∈ s, f x) :=
  (integralClosure R A).sum_mem h
/-
**IsIntegral.det** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n A} 
(h : forall i j, IsIntegral R (M i j)) : IsIntegral R M.det
参数：h : forall i j, IsIntegral R (M i j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det_apply`：det_apply (M : Matrix n n R) : M.det = ∑ σ : Perm n, E
quiv.Perm.sign σ • ∏ i, M (σ i) i
· 使用定理 `IsIntegral.sum`：IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (
h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∑ x in s, f x)
· 使用定理 `IsIntegral.zsmul`：IsIntegral.zsmul {x : B} (h : IsIntegral R x) (n : Int
) : IsIntegral R (n • x)
· 使用定理 `IsIntegral.prod`：IsIntegral.prod {α : Type*} {s : Finset α} (f : α -> A)
 (h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∏ x in s, f x)
-/
theorem IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n A}
    (h : ∀ i j, IsIntegral R (M i j)) : IsIntegral R M.det := by
  rw [Matrix.det_apply]
  exact IsIntegral.sum _ fun σ _hσ ↦ (IsIntegral.prod _ fun i _hi => h _ _).zsmul _

@[simp]
/-
**IsIntegral.pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.pow_iff {x : A} {n : Nat} (hn : 0 < n) : IsIntegral R (x ^ n) ↔
 IsIntegral R x
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.of_pow`：IsIntegral.of_pow [Algebra R B] {x : B} {n : Nat} (hn
 : 0 < n) (hx : IsIntegral R <| x ^ n) : IsIntegral R x
· 使用定理 `IsIntegral.pow`：IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : 
IsIntegral R (x ^ n)
-/
theorem IsIntegral.pow_iff {x : A} {n : ℕ} (hn : 0 < n) : IsIntegral R (x ^ n) ↔ IsIntegral R x :=
  ⟨IsIntegral.of_pow hn, fun hx ↦ hx.pow n⟩

section Pushout

variable (R S A) [Algebra R S] [int : Algebra.IsIntegral R S]
variable (SA : Type*) [CommRing SA] [Algebra R SA] [Algebra S SA] [Algebra A SA]
  [IsScalarTower R S SA] [IsScalarTower R A SA]

/-
**Algebra.IsPushout.isIntegral'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.isIntegral' [IsPushout R A S SA] : Algebra.IsIntegral A 
SA
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgEquiv.isIntegral_iff`：AlgEquiv.isIntegral_iff (e : A ≃ₐ[R] B) : Algeb
ra.IsIntegral R A ↔ Algebra.IsIntegral R B
-/
theorem Algebra.IsPushout.isIntegral' [IsPushout R A S SA] : Algebra.IsIntegral A SA :=
  (equiv R A S SA).isIntegral_iff.mp inferInstance
/-
**Algebra.IsPushout.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.isIntegral [h : IsPushout R S A SA] : Algebra.IsIntegral
 A SA
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.isIntegral'`：Algebra.IsPushout.isIntegral' [IsPushout 
R A S SA] : Algebra.IsIntegral A SA
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
-/
theorem Algebra.IsPushout.isIntegral [h : IsPushout R S A SA] : Algebra.IsIntegral A SA :=
  h.symm.isIntegral'

attribute [local instance] Polynomial.algebra in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsIntegral R[X] S[X] := Algebra.IsPushout.isIntegral R _ S _

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ} : Algebra.IsIntegral (MvPolynomial σ R) (MvPolynomial σ S) :=
  Algebra.IsPushout.isIntegral R _ S _

end Pushout

section

variable (p : R[X]) (x : S)

/-- Given a `p : R[X]` and a `x : S` such that `p.eval₂ f x = 0`,
`f p.leadingCoeff * x` is integral. -/
/-
**RingHom.isIntegralElem_leadingCoeff_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.isIntegralElem_leadingCoeff_mul (h : p.eval₂ f x = 0) : f.IsIntegr
alElem (f p.leadingCoeff * x)
参数：h : p.eval₂ f x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_succ_le_zero`：∀ (n : ℕ), n.succ ≤ 0 → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Polynomial.monic_integralNormalization`：monic_integralNormalization (hp 
: p != 0) : Monic (integralNormalization p)
· 使用定理 `Polynomial.integralNormalization_eval₂_leadingCoeff_mul`：integralNormali
zation_eval₂_leadingCoeff_mul (h : 1 <= p.natDegree) (f : R ->+* S) (x : S) : (i
ntegralNormalization p).eval₂ f (f p.leadingC…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RingHom.isIntegralElem_zero`：RingHom.isIntegralElem_zero : f.IsIntegralE
lem 0
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0

--- 原说明 ---
Given a `p : R[X]` and a `x : S` such that `p.eval₂ f x = 0`,
`f p.leadingCoeff * x` is integral.
-/
theorem RingHom.isIntegralElem_leadingCoeff_mul (h : p.eval₂ f x = 0) :
    f.IsIntegralElem (f p.leadingCoeff * x) := by
  by_cases h' : 1 ≤ p.natDegree
  · use integralNormalization p
    have : p ≠ 0 := fun h'' => by
      rw [h'', natDegree_zero] at h'
      exact Nat.not_succ_le_zero 0 h'
    use monic_integralNormalization this
    rw [integralNormalization_eval₂_leadingCoeff_mul h' f x, h, mul_zero]
  · by_cases hp : p.map f = 0
    · apply_fun fun q => coeff q p.natDegree at hp
      rw [coeff_map, coeff_zero, coeff_natDegree] at hp
      rw [hp, zero_mul]
      exact f.isIntegralElem_zero
    · rw [Nat.one_le_iff_ne_zero, Classical.not_not] at h'
      rw [eq_C_of_natDegree_eq_zero h', eval₂_C] at h
      suffices p.map f = 0 by exact (hp this).elim
      rw [eq_C_of_natDegree_eq_zero h', map_C, h, C_eq_zero]

/-- Given a `p : R[X]` and a root `x : S`,
then `p.leadingCoeff • x : S` is integral over `R`. -/
/-
**isIntegral_leadingCoeff_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_leadingCoeff_smul [Algebra R S] (h : aeval x p = 0) : IsIntegra
l R (p.leadingCoeff • x)
参数：h : aeval x p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `RingHom.isIntegralElem_leadingCoeff_mul`：RingHom.isIntegralElem_leadingC
oeff_mul (h : p.eval₂ f x = 0) : f.IsIntegralElem (f p.leadingCoeff * x)
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p

--- 原说明 ---
Given a `p : R[X]` and a root `x : S`,
then `p.leadingCoeff • x : S` is integral over `R`.
-/
theorem isIntegral_leadingCoeff_smul [Algebra R S] (h : aeval x p = 0) :
    IsIntegral R (p.leadingCoeff • x) := by
  rw [aeval_def] at h
  rw [Algebra.smul_def]
  exact (algebraMap R S).isIntegralElem_leadingCoeff_mul p x h

end

/-
**Polynomial.Monic.quotient_isIntegralElem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.Monic.quotient_isIntegralElem {g : S[X]} (mon : g.Monic) {I : I
deal S[X]} (h : g in I) : ((Ideal.Quotient.mk I).comp (algebraMap S S[X])).IsInt
egralElem (Ideal.Quotient.mk I X)
参数：mon : g.Monic；h : g in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Polynomial.eval₂_eq_sum_range`：eval₂_eq_sum_range : p.eval₂ f x = ∑ i in
 Finset.range (p.natDegree + 1), f (p.coeff i) * x ^ i
· 使用定理 `Polynomial.as_sum_range_C_mul_X_pow`：as_sum_range_C_mul_X_pow (p : R[X])
 : p = ∑ i in range (p.natDegree + 1), C (coeff p i) * X ^ i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Polynomial.Monic.quotient_isIntegralElem {g : S[X]} (mon : g.Monic) {I : Ideal S[X]}
    (h : g ∈ I) :
    ((Ideal.Quotient.mk I).comp (algebraMap S S[X])).IsIntegralElem (Ideal.Quotient.mk I X) := by
  exact ⟨g, mon, by
  rw [← (Ideal.Quotient.eq_zero_iff_mem.mpr h), eval₂_eq_sum_range]
  nth_rw 3 [(as_sum_range_C_mul_X_pow g)]
  simp only [map_sum, algebraMap_eq, RingHom.coe_comp, Function.comp_apply, map_mul, map_pow]⟩

/- If `I` is an ideal of the polynomial ring `S[X]` and contains a monic polynomial `f`,
then `S[X]/I` is integral over `S`. -/
/-
**Polynomial.Monic.quotient_isIntegral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Polynomial.Monic.quotient_isIntegral {g : S[X]} (mon : g.Monic) {I : Ideal
 S[X]} (h : g in I) : ((Ideal.Quotient.mkₐ S I).comp (Algebra.ofId S S[X])).IsIn
tegral
参数：mon : g.Monic；h : g in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Ideal.Quotient.mkₐ_surjective`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : 
CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst
_3 : I.IsTwoSided],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_eq_sum_range'`：aeval_eq_sum_range' [Algebra R S] {p : R
[X]} {n : Nat} (hn : p.natDegree < n) (x : S) : aeval x p = ∑ i in Finset.range 
n, p.coeff i • x ^ i
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.as_sum_range_C_mul_X_pow`：as_sum_range_C_mul_X_pow (p : R[X])
 : p = ∑ i in range (p.natDegree + 1), C (coeff p i) * X ^ i
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `I` is an ideal of the polynomial ring `S[X]` and contains a monic polynomial
 `f`,
then `S[X]/I` is integral over `S`.
-/
lemma Polynomial.Monic.quotient_isIntegral {g : S[X]} (mon : g.Monic) {I : Ideal S[X]} (h : g ∈ I) :
    ((Ideal.Quotient.mkₐ S I).comp (Algebra.ofId S S[X])).IsIntegral := by
  have eq_top : Algebra.adjoin S {(Ideal.Quotient.mkₐ S I) X} = ⊤ := by
    ext g
    constructor
    · simp only [Algebra.mem_top, implies_true]
    · intro _
      obtain ⟨g', hg⟩ := Ideal.Quotient.mkₐ_surjective S I g
      have : g = (Polynomial.aeval ((Ideal.Quotient.mkₐ S I) X)) g' := by
        nth_rw 1 [← hg, aeval_eq_sum_range' (lt_add_one _),
          as_sum_range_C_mul_X_pow g', map_sum]
        simp only [Polynomial.C_mul', ← map_pow, map_smul]
      exact this ▸ (aeval_mem_adjoin_singleton S ((Ideal.Quotient.mk I) Polynomial.X))
  exact fun a ↦ (eq_top ▸ adjoin_le_integralClosure <| mon.quotient_isIntegralElem h)
    Algebra.mem_top

end

section IsIntegralClosure

/-
**integralClosure.isIntegralClosure** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：integralClosure.isIntegralClosure (R A : Type*) [CommRing R] [CommRing A] 
[Algebra R A] : IsIntegralClosure (integralClosure R A) R A where algebraMap_inj
ective
参数：R A : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
instance integralClosure.isIntegralClosure (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    IsIntegralClosure (integralClosure R A) R A where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨⟨_, h⟩, rfl⟩; exact h⟩

namespace IsIntegralClosure

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R B] [Algebra A B] [IsIntegralClosure A R B]
variable (R B)

/-
**IsIntegralClosure.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} (B : Type u_3) [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R B] [inst_4 : Algebra 
A B] [IsIntegralClosure A R B] [inst_6 : Algebra R A] [IsScalarTower R A B]   (x
 : A), IsIntegral R x
参数：R : Type u_1；B : Type u_3；x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
-/
protected theorem isIntegral [Algebra R A] [IsScalarTower R A B] (x : A) : IsIntegral R x :=
  (isIntegral_algebraMap_iff (algebraMap_injective A R B)).mp <|
    show IsIntegral R (algebraMap A B x) from isIntegral_iff.mpr ⟨x, rfl⟩
/-
**IsIntegralClosure.isIntegral_algebra** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClos
ure`。
形式化陈述：isIntegral_algebra [Algebra R A] [IsScalarTower R A B] : Algebra.IsIntegra
l R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral`：∀ (R : Type u_1) {A : Type u_2} (B : Type 
u_3) [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 :
 Algebra R B] [ins…
-/
theorem isIntegral_algebra [Algebra R A] [IsScalarTower R A B] : Algebra.IsIntegral R A :=
  ⟨fun x => IsIntegralClosure.isIntegral R B x⟩
/-
**IsIntegralClosure.isTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 `IsIntegralClosure`。
形式化陈述：isTorsionFree [Module R A] [IsScalarTower R A B] [IsTorsionFree R B] : IsT
orsionFree R A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `IsScalarTower.smul_assoc`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_1
1} {inst : SMul M N} {inst_1 : SMul N α} {inst_2 : SMul M α}   [self : IsScalarT
ower M N α] (x…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isTorsionFree [Module R A] [IsScalarTower R A B] [IsTorsionFree R B] : IsTorsionFree R A := by
  refine
    Function.Injective.moduleIsTorsionFree _ (IsIntegralClosure.algebraMap_injective A R B)
      fun _ _ => ?_
  simp only [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc]

variable {R} (A) {B}

/-- If `x : B` is integral over `R`, then it is an element of the integral closure of `R` in `B`. -/
/-
**IsIntegralClosure.mk'** 是 Mathlib 中的一个定义，位于命名空间 `IsIntegralClosure`。
形式化陈述：mk' (x : B) (hx : IsIntegral R x) : A
参数：x : B；hx : IsIntegral R x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x : B` is integral over `R`, then it is an element of the integral closure o
f `R` in `B`.
-/
noncomputable def mk' (x : B) (hx : IsIntegral R x) : A :=
  Classical.choose (isIntegral_iff.mp hx)

@[simp]
/-
**IsIntegralClosure.algebraMap_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`
。
形式化陈述：algebraMap_mk' (x : B) (hx : IsIntegral R x) : algebraMap A B (mk' A x hx)
 = x
参数：x : B；hx : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
-/
theorem algebraMap_mk' (x : B) (hx : IsIntegral R x) : algebraMap A B (mk' A x hx) = x :=
  Classical.choose_spec (isIntegral_iff.mp hx)

@[simp]
/-
**IsIntegralClosure.mk'_one** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R B] [inst_4 : Algebra 
A B] [inst_5 : IsIntegralClosure A R B] (h : optParam (IsIntegral R 1) ⋯),   IsI
ntegralClosure.mk' A 1 h = 1
参数：A : Type u_2；h : optParam (IsIntegral R 1) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
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
-/
theorem mk'_one (h : IsIntegral R (1 : B) := isIntegral_one) : mk' A 1 h = 1 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', map_one]

@[simp]
/-
**IsIntegralClosure.mk'_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R B] [inst_4 : Algebra 
A B] [inst_5 : IsIntegralClosure A R B] (h : optParam (IsIntegral R 0) ⋯),   IsI
ntegralClosure.mk' A 0 h = 0
参数：A : Type u_2；h : optParam (IsIntegral R 0) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem mk'_zero (h : IsIntegral R (0 : B) := isIntegral_zero) : mk' A 0 h = 0 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', map_zero]

@[simp]
/-
**IsIntegralClosure.mk'_add** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R B] [inst_4 : Algebra 
A B] [inst_5 : IsIntegralClosure A R B] (x y : B) (hx : IsIntegral R x)   (hy : 
IsIntegral R y), IsIntegralClosure.mk' A (x + y) ⋯ = IsIntegralClosure.mk' A x h
x + IsIntegralClosure.mk' A y hy
参数：A : Type u_2；x y : B；hx : IsIntegral R x；hy : IsIntegral R y；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsIntegral.add`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk'_add (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x + y) (hx.add hy) = mk' A x hx + mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', map_add]

@[simp]
/-
**IsIntegralClosure.mk'_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R B] [inst_4 : Algebra 
A B] [inst_5 : IsIntegralClosure A R B] (x y : B) (hx : IsIntegral R x)   (hy : 
IsIntegral R y), IsIntegralClosure.mk' A (x * y) ⋯ = IsIntegralClosure.mk' A x h
x * IsIntegralClosure.mk' A y hy
参数：A : Type u_2；x y : B；hx : IsIntegral R x；hy : IsIntegral R y；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk'_mul (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x * y) (hx.mul hy) = mk' A x hx * mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', map_mul]

@[simp]
/-
**IsIntegralClosure.mk'_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`
。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algebra R B] [inst_4 : Algebra 
A B] [inst_5 : IsIntegralClosure A R B] [inst_6 : Algebra R A]   [IsScalarTower 
R A B] (x : R) (h : optParam (IsIntegral R ((algebraMap R B) x)) ⋯),   IsIntegra
lClosure.mk' A ((algebraMap R B) x) h = (algebraMap R A) x
参数：A : Type u_2；x : R；h : optParam (IsIntegral R ((algebraMap R B) x)) ⋯；(algebr
aMap R B) x；algebraMap R A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
-/
theorem mk'_algebraMap [Algebra R A] [IsScalarTower R A B] (x : R)
    (h : IsIntegral R (algebraMap R B x) := isIntegral_algebraMap) :
    IsIntegralClosure.mk' A (algebraMap R B x) h = algebraMap R A x :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply]

/-- The integral closure of a field in a commutative domain is always a field. -/
/-
**IsIntegralClosure.isField** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`。
形式化陈述：isField [Algebra R A] [IsScalarTower R A B] [IsDomain A] (hR : IsField R) 
: IsField A
参数：hR : IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `isField_of_isIntegral_of_isField'`：isField_of_isIntegral_of_isField' [Co
mmRing R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] (hR :
 IsField R) : IsField S…

--- 原说明 ---
The integral closure of a field in a commutative domain is always a field.
-/
theorem isField [Algebra R A] [IsScalarTower R A B] [IsDomain A] (hR : IsField R) :
    IsField A :=
  have := IsIntegralClosure.isIntegral_algebra R (A := A) B
  isField_of_isIntegral_of_isField' hR
/-
**IsIntegralClosure.of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure`。
形式化陈述：of_algEquiv {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] (f : B ≃ₐ
[R] S) (h : forall x, algebraMap A S x = f (algebraMap A B x)) : IsIntegralClosu
re A R S where algebraMap_injective
参数：f : B ≃ₐ[R] S；h : forall x, algebraMap A S x = f (algebraMap A B x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isIntegral_algEquiv`：isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B]
 [Algebra R A] [Algebra R B] (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIn
tegral R …
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem of_algEquiv {S : Type*} [CommRing S] [Algebra A S] [Algebra R S]
    (f : B ≃ₐ[R] S) (h : ∀ x, algebraMap A S x = f (algebraMap A B x)) :
    IsIntegralClosure A R S where
  algebraMap_injective :=
    funext_iff.2 h ▸ f.injective.comp (IsIntegralClosure.algebraMap_injective A R B)
  isIntegral_iff {x} := by simp [← isIntegral_algEquiv f.symm,
    IsIntegralClosure.isIntegral_iff (A := A), h, ← f.symm.injective.eq_iff]

section lift

variable (B) {S : Type*} [CommRing S] [Algebra R S]
-- split from above, since otherwise it does not synthesize `Semiring S`
variable [Algebra S B] [IsScalarTower R S B]
variable [Algebra R A] [IsScalarTower R A B] [isIntegral : Algebra.IsIntegral R S]
variable (R)

/-- If `B / S / R` is a tower of ring extensions where `S` is integral over `R`,
then `S` maps (uniquely) into an integral closure `B / A / R`. -/
/-
**IsIntegralClosure.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsIntegralClosure`。
形式化陈述：lift : S ->ₐ[R] A where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `B / S / R` is a tower of ring extensions where `S` is integral over `R`,
then `S` maps (uniquely) into an integral closure `B / A / R`.
-/
noncomputable def lift : S →ₐ[R] A where
  toFun x := mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))
  map_one' := by simp only [map_one, mk'_one]
  map_zero' := by simp only [map_zero, mk'_zero]
  map_add' x y := by simp_rw [← mk'_add, map_add]
  map_mul' x y := by simp_rw [← mk'_mul, map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]

@[simp]
/-
**IsIntegralClosure.algebraMap_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosure
`。
形式化陈述：algebraMap_lift (x : S) : algebraMap A B (lift R A B x) = algebraMap S B x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_mk'`：algebraMap_mk' (x : B) (hx : IsIntegra
l R x) : algebraMap A B (mk' A x hx) = x
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
theorem algebraMap_lift (x : S) : algebraMap A B (lift R A B x) = algebraMap S B x :=
  algebraMap_mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))

end lift

section Equiv

variable (R B) (A' : Type*) [CommRing A']
variable [Algebra A' B] [IsIntegralClosure A' R B]
variable [Algebra R A] [Algebra R A'] [IsScalarTower R A B] [IsScalarTower R A' B]

/-- Integral closures are all isomorphic to each other. -/
/-
**IsIntegralClosure.equiv** 是 Mathlib 中的一个定义，位于命名空间 `IsIntegralClosure`。
形式化陈述：equiv : A ≃ₐ[R] A'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A

--- 原说明 ---
Integral closures are all isomorphic to each other.
-/
noncomputable def equiv : A ≃ₐ[R] A' :=
  AlgEquiv.ofAlgHom
    (lift R A' B (isIntegral := isIntegral_algebra R B))
    (lift R A B (isIntegral := isIntegral_algebra R B))
    (by ext x; apply algebraMap_injective A' R B; simp)
    (by ext x; apply algebraMap_injective A R B; simp)

@[simp]
/-
**IsIntegralClosure.algebraMap_equiv** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegralClosur
e`。
形式化陈述：algebraMap_equiv (x : A) : algebraMap A' B (equiv R A B A' x) = algebraMap
 A B x
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_lift`：algebraMap_lift (x : S) : algebraMap 
A B (lift R A B x) = algebraMap S B x
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
-/
theorem algebraMap_equiv (x : A) : algebraMap A' B (equiv R A B A' x) = algebraMap A B x :=
  algebraMap_lift R A' B (isIntegral := isIntegral_algebra R B) x

end Equiv

end IsIntegralClosure

end IsIntegralClosure

section Algebra

open Algebra

variable {R A B S T : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S] [CommRing T]
variable [Algebra A B] [Algebra R B] (f : R →+* S) (g : S →+* T)
variable [Algebra R A] [IsScalarTower R A B]

set_option backward.isDefEq.respectTransparency false in
/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R. -/
/-
**isIntegral_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx : IsIntegral A x) : 
IsIntegral R x
参数：x : B；hx : IsIntegral A x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…
· 使用定理 `fg_adjoin_of_finite`：fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (h
is : forall x in s, IsIntegral R x) : (Algebra.adjoin R s).toSubmodule.FG
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Polynomial.monic_toSubring`：monic_toSubring : Monic (toSubring p T hp) ↔
 Monic p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.map_toSubring`：map_toSubring : (p.toSubring T hp).map (Subrin
g.subtype T) = p
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `IsIntegral.fg_adjoin_singleton`：IsIntegral.fg_adjoin_singleton [Algebra 
R B] {x : B} (hx : IsIntegral R x) : (Algebra.adjoin R {x}).toSubmodule.FG
· 使用定理 `IsIntegral.of_mem_of_fg`：IsIntegral.of_mem_of_fg (S : Subalgebra R B) (H
S : S.toSubmodule.FG) (x : B) (hx : x in S) : IsIntegral R x
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `Subalgebra.mem_restrictScalars`：mem_restrictScalars {U : Subalgebra S A}
 {x : A} : x in restrictScalars R U ↔ x in U

--- 原说明 ---
If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral 
over R.
-/
theorem isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx : IsIntegral A x) :
    IsIntegral R x := by
  rcases hx with ⟨p, pmonic, hp⟩
  let S := adjoin R (p.coeffs : Set A)
  have : Module.Finite R S := ⟨(Subalgebra.toSubmodule S).fg_top.mpr <|
    fg_adjoin_of_finite p.coeffs.finite_toSet fun a _ ↦ Algebra.IsIntegral.isIntegral a⟩
  let p' : S[X] := p.toSubring S.toSubring subset_adjoin
  have hSx : IsIntegral S x := ⟨p', (p.monic_toSubring _ _).mpr pmonic, by
    rw [IsScalarTower.algebraMap_eq S A B, ← eval₂_map]
    convert! hp; apply p.map_toSubring S.toSubring⟩
  let Sx := Subalgebra.toSubmodule (S[x])
  let MSx : Module S Sx := SMulMemClass.toModule _ -- the next line times out without this
  have : Module.Finite S Sx := .of_fg hSx.fg_adjoin_singleton
  refine .of_mem_of_fg ((S[x]).restrictScalars R) ?_ _
    ((Subalgebra.mem_restrictScalars R).mpr <| subset_adjoin rfl)
  rw [← Module.Finite.iff_fg]
  let : SMul S Sx := { MSx with } -- need this even though MSx is there
  have : IsScalarTower R S Sx :=
    Submodule.isScalarTower Sx -- Lean looks for `Module A Sx` without this
  exact Module.Finite.trans S Sx

variable (A) in
/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R. -/
/-
**Algebra.IsIntegral.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsIntegral`。
形式化陈述：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3} [inst : CommRing R] [inst_1
 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra A B] [inst_4 : Algebra R B]
 [inst_5 : Algebra R A] [IsScalarTower R A B] [Algebra.IsIntegral R A]   [Algebr
a.IsIntegral A B], Algebra.IsIntegral R B
参数：A : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.
-/
protected theorem Algebra.IsIntegral.trans
    [Algebra.IsIntegral R A] [Algebra.IsIntegral A B] : Algebra.IsIntegral R B :=
  ⟨fun x ↦ isIntegral_trans x (Algebra.IsIntegral.isIntegral (R := A) x)⟩
/-
**RingHom.IsIntegral.trans** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.IsIntegral`。
形式化陈述：∀ {R : Type u_1} {S : Type u_4} {T : Type u_5} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   (f : R →+* S) (g : S →+* T), f.IsIntegral
 → g.IsIntegral → (g.comp f).IsIntegral
参数：f : R →+* S；g : S →+* T；g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Algebra.IsIntegral.trans`：∀ {R : Type u_1} (A : Type u_2) {B : Type u_3}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra
 A B] [inst_4 …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
protected theorem RingHom.IsIntegral.trans
    (hf : f.IsIntegral) (hg : g.IsIntegral) : (g.comp f).IsIntegral :=
  let _ := f.toAlgebra; let _ := g.toAlgebra; let _ := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : Algebra.IsIntegral S T := ⟨hg⟩
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.trans S
  Algebra.IsIntegral.isIntegral

/-- If `R → A → B` is an algebra tower, `C` is the integral closure of `R` in `B`
and `A` is integral over `R`, then `C` is the integral closure of `A` in `B`. -/
/-
**IsIntegralClosure.tower_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegralClosure.tower_top {B C : Type*} [CommSemiring C] [CommRing B] [A
lgebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B] [IsIntegralClosure
 C R B] [Algebra.IsIntegral R A] : IsIntegralClosure C A B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegralClosure.algebraMap_injective`：∀ (A : Type u_1) (R : Type u_2) 
(B : Type u_3) {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing 
B}   {inst_3 : Algebra R B} …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
If `R → A → B` is an algebra tower, `C` is the integral closure of `R` in `B`
and `A` is integral over `R`, then `C` is the integral closure of `A` in `B`.
-/
lemma IsIntegralClosure.tower_top {B C : Type*} [CommSemiring C] [CommRing B]
    [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C R B] [Algebra.IsIntegral R A] :
    IsIntegralClosure C A B :=
  ⟨IsIntegralClosure.algebraMap_injective _ R _,
   fun hx => (IsIntegralClosure.isIntegral_iff).mp (isIntegral_trans (R := R) _ hx),
   fun hx => ((IsIntegralClosure.isIntegral_iff (R := R)).mpr hx).tower_top⟩
/-
**RingHom.isIntegral_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.isIntegral_of_surjective (hf : Function.Surjective f) : f.IsIntegr
al
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem_map`：RingHom.isIntegralElem_map {x : R} : f.IsInt
egralElem (f x)
-/
theorem RingHom.isIntegral_of_surjective (hf : Function.Surjective f) : f.IsIntegral :=
  fun x ↦ (hf x).recOn fun _y hy ↦ hy ▸ f.isIntegralElem_map

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
/-
**IsIntegral.tower_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.tower_bot (H : Function.Injective (algebraMap A B)) {x : A} (h 
: IsIntegral R (algebraMap A B x)) : IsIntegral R x
参数：H : Function.Injective (algebraMap A B)；h : IsIntegral R (algebraMap A B x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x

--- 原说明 ---
If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A`
-/
theorem IsIntegral.tower_bot (H : Function.Injective (algebraMap A B)) {x : A}
    (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) H).mp h

nonrec theorem RingHom.IsIntegral.tower_bot (hg : Function.Injective g)
    (hfg : (g.comp f).IsIntegral) : f.IsIntegral :=
  letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  fun x ↦ IsIntegral.tower_bot hg (hfg (g x))

variable (T) in
/-- Let `T / S / R` be a tower of algebras, `T` is non-trivial and is a torsion free `S`-module,
  then if `T` is an integral `R`-algebra, then `S` is an integral `R`-algebra. -/
/-
**Algebra.IsIntegral.tower_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.tower_bot [IsDomain S] [Algebra R S] [Algebra R T] [Alg
ebra S T] [IsTorsionFree S T] [Nontrivial T] [IsScalarTower R S T] [h : Algebra.
IsIntegral R T] : Algebra.IsIntegral R S where isIntegral
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegral.tower_bot`：∀ {R : Type u_1} {S : Type u_4} {T : Type 
u_5} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   (f : R →+
* S) (g : S →+* T)…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
Let `T / S / R` be a tower of algebras, `T` is non-trivial and is a torsion free
 `S`-module,
  then if `T` is an integral `R`-algebra, then `S` is an integral `R`-algebra.
-/
theorem Algebra.IsIntegral.tower_bot [IsDomain S] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsTorsionFree S T] [Nontrivial T] [IsScalarTower R S T]
    [h : Algebra.IsIntegral R T] : Algebra.IsIntegral R S where
  isIntegral := by
    apply RingHom.IsIntegral.tower_bot (algebraMap R S) (algebraMap S T)
      (FaithfulSMul.algebraMap_injective S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral
/-
**IsIntegral.tower_bot_of_field** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegral.tower_bot_of_field {R A B : Type*} [CommRing R] [Field A] [Ring
 B] [Nontrivial B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A 
B] {x : A} (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x
参数：h : IsIntegral R (algebraMap A B x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.tower_bot`：IsIntegral.tower_bot (H : Function.Injective (alge
braMap A B)) {x : A} (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
-/
theorem IsIntegral.tower_bot_of_field {R A B : Type*} [CommRing R] [Field A]
    [Ring B] [Nontrivial B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    {x : A} (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  h.tower_bot (algebraMap A B).injective
/-
**RingHom.isIntegralElem.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.isIntegralElem.of_comp {x : T} (h : (g.comp f).IsIntegralElem x) :
 g.IsIntegralElem x
参数：h : (g.comp f).IsIntegralElem x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
-/
theorem RingHom.isIntegralElem.of_comp {x : T} (h : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x :=
  let ⟨p, hp, hp'⟩ := h
  ⟨p.map f, hp.map f, by rwa [← eval₂_map] at hp'⟩
/-
**RingHom.IsIntegral.tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegral.tower_top (h : (g.comp f).IsIntegral) : g.IsIntegral
参数：h : (g.comp f).IsIntegral。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.isIntegralElem.of_comp`：RingHom.isIntegralElem.of_comp {x : T} (
h : (g.comp f).IsIntegralElem x) : g.IsIntegralElem x
-/
theorem RingHom.IsIntegral.tower_top (h : (g.comp f).IsIntegral) : g.IsIntegral :=
  fun x ↦ RingHom.isIntegralElem.of_comp f g (h x)

variable (R) in
/-- Let `T / S / R` be a tower of algebras, `T` is an integral `R`-algebra, then it is integral
  as an `S`-algebra. -/
/-
**Algebra.IsIntegral.tower_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.tower_top [Algebra R S] [Algebra R T] [Algebra S T] [Is
ScalarTower R S T] [h : Algebra.IsIntegral R T] : Algebra.IsIntegral S T where i
sIntegral
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegral.tower_top`：RingHom.IsIntegral.tower_top (h : (g.comp 
f).IsIntegral) : g.IsIntegral
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…

--- 原说明 ---
Let `T / S / R` be a tower of algebras, `T` is an integral `R`-algebra, then it 
is integral
  as an `S`-algebra.
-/
theorem Algebra.IsIntegral.tower_top [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [h : Algebra.IsIntegral R T] : Algebra.IsIntegral S T where
  isIntegral := by
    apply RingHom.IsIntegral.tower_top (algebraMap R S) (algebraMap S T)
    rw [← IsScalarTower.algebraMap_eq R S T]
    exact h.isIntegral

set_option backward.isDefEq.respectTransparency.types false in
/-
**RingHom.IsIntegral.quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegral.quotient {I : Ideal S} (hf : f.IsIntegral) : (Ideal.quo
tientMap I f le_rfl).IsIntegral
参数：hf : f.IsIntegral。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval₂_map`：eval₂_map [Semiring T] (g : S ->+* T) (x : T) : (p
.map f).eval₂ g x = p.eval₂ (g.comp f) x
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem RingHom.IsIntegral.quotient {I : Ideal S} (hf : f.IsIntegral) :
    (Ideal.quotientMap I f le_rfl).IsIntegral := by
  rintro ⟨x⟩
  obtain ⟨p, p_monic, hpx⟩ := hf x
  refine ⟨p.map (Ideal.Quotient.mk _), p_monic.map _, ?_⟩
  simpa only [hom_eval₂, eval₂_map] using! congr_arg (Ideal.Quotient.mk I) hpx
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I : Ideal A} [Algebra.IsIntegral R A] : Algebra.IsIntegral R (A ⧸ I) :=
  Algebra.IsIntegral.trans A
/-
**Algebra.IsIntegral.quotient** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.quotient {I : Ideal A} [Algebra.IsIntegral R A] : Algeb
ra.IsIntegral (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegral.quotient`：RingHom.IsIntegral.quotient {I : Ideal S} (
hf : f.IsIntegral) : (Ideal.quotientMap I f le_rfl).IsIntegral
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
-/
instance Algebra.IsIntegral.quotient {I : Ideal A} [Algebra.IsIntegral R A] :
    Algebra.IsIntegral (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  ⟨RingHom.IsIntegral.quotient (algebraMap R A) Algebra.IsIntegral.isIntegral⟩
/-
**isIntegral_quotientMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_quotientMap_iff {I : Ideal S} : (Ideal.quotientMap I f le_rfl).
IsIntegral ↔ ((Ideal.Quotient.mk I).comp f : R ->+* S ⧸ I).IsIntegral
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Ideal.quotientMap_comp_mk`：quotientMap_comp_mk {J : Ideal R} {I : Ideal 
S} [I.IsTwoSided] [J.IsTwoSided] {f : R ->+* S} (H : J <= I.comap f) : (quotient
Map I f H).comp…
· 使用定理 `RingHom.IsIntegral.trans`：∀ {R : Type u_1} {S : Type u_4} {T : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing T]   (f : R →+* S)
 (g : S →+* T)…
· 使用定理 `RingHom.isIntegral_of_surjective`：RingHom.isIntegral_of_surjective (hf :
 Function.Surjective f) : f.IsIntegral
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `RingHom.IsIntegral.tower_top`：RingHom.IsIntegral.tower_top (h : (g.comp 
f).IsIntegral) : g.IsIntegral
-/
theorem isIntegral_quotientMap_iff {I : Ideal S} :
    (Ideal.quotientMap I f le_rfl).IsIntegral ↔
      ((Ideal.Quotient.mk I).comp f : R →+* S ⧸ I).IsIntegral := by
  let g := Ideal.Quotient.mk (I.comap f)
  -- Porting note: added type ascription
  have : (Ideal.quotientMap I f le_rfl).comp g = (Ideal.Quotient.mk I).comp f :=
    Ideal.quotientMap_comp_mk le_rfl
  refine ⟨fun h => ?_, fun h => RingHom.IsIntegral.tower_top g _ (this ▸ h)⟩
  refine this ▸ RingHom.IsIntegral.trans g (Ideal.quotientMap I f le_rfl) ?_ h
  exact g.isIntegral_of_surjective Ideal.Quotient.mk_surjective
/-
**RingHom.IsIntegral.kerLift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegral.kerLift {f : S ->+* T} (hf : f.IsIntegral) : f.kerLift.
IsIntegral
参数：hf : f.IsIntegral。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegral.tower_top`：RingHom.IsIntegral.tower_top (h : (g.comp 
f).IsIntegral) : g.IsIntegral
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem RingHom.IsIntegral.kerLift {f : S →+* T} (hf : f.IsIntegral) : f.kerLift.IsIntegral :=
  RingHom.IsIntegral.tower_top (Ideal.Quotient.mk (RingHom.ker f)) f.kerLift hf
/-
**RingHom.IsIntegral.isLocalHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RingHom.IsIntegral.isLocalHom {f : R ->+* S} (hf : f.IsIntegral) (inj : Fu
nction.Injective f) : IsLocalHom f where map_nonunit a ha
参数：hf : f.IsIntegral；inj : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.coeff_zero_reverse`：coeff_zero_reverse (f : R[X]) : coeff (re
verse f) 0 = leadingCoeff f
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.X_mul_divX_add`：X_mul_divX_add (p : R[X]) : X * divX p + C (p
.coeff 0) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero'`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_
9} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [Add
MonoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.eval₂_hom`：eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x)
· 使用定理 `Polynomial.eval₂_reverse_eq_zero_iff`：eval₂_reverse_eq_zero_iff (i : R -
>+* S) (x : S) [Invertible x] (f : R[X]) : eval₂ i (⅟x) (reverse f) = 0 ↔ eval₂ 
i x f = 0
-/
theorem RingHom.IsIntegral.isLocalHom {f : R →+* S} (hf : f.IsIntegral)
    (inj : Function.Injective f) : IsLocalHom f where
  map_nonunit a ha := by
    -- `f a` is invertible in `S`, and we need to show that `(f a)⁻¹` is of the form `f b`.
    -- Let `p : R[X]` be monic with root `(f a)⁻¹`,
    obtain ⟨p, p_monic, hp⟩ := hf (ha.unit⁻¹ : _)
    -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
    -- We have `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
    refine .of_mul_eq_one (-p.reverse.divX.eval a) ?_
    nth_rewrite 1 [mul_neg, ← eval_X (x := a), ← eval_mul, ← p_monic, ← coeff_zero_reverse,
      ← add_eq_zero_iff_neg_eq, ← eval_C (a := p.reverse.coeff 0), ← eval_add, X_mul_divX_add,
      ← (injective_iff_map_eq_zero' _).mp inj, ← eval₂_hom]
    rwa [← eval₂_reverse_eq_zero_iff] at hp

variable [Algebra R S] [Algebra.IsIntegral R S]

variable (R S) in
/-
**Algebra.IsIntegral.isLocalHom** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.isLocalHom [FaithfulSMul R S] : IsLocalHom (algebraMap 
R S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegral.isLocalHom`：RingHom.IsIntegral.isLocalHom {f : R ->+*
 S} (hf : f.IsIntegral) (inj : Function.Injective f) : IsLocalHom f where map_no
nunit a ha
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `algebraMap_isIntegral_iff`：algebraMap_isIntegral_iff : (algebraMap R A).
IsIntegral ↔ Algebra.IsIntegral R A
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
-/
instance Algebra.IsIntegral.isLocalHom [FaithfulSMul R S] : IsLocalHom (algebraMap R S) :=
  (algebraMap_isIntegral_iff.mpr ‹_›).isLocalHom (FaithfulSMul.algebraMap_injective R S)

/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
/-
**isField_of_isIntegral_of_isField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isField_of_isIntegral_of_isField (hRS : Function.Injective (algebraMap R S
)) (hS : IsField S) : IsField R
参数：hRS : Function.Injective (algebraMap R S)；hS : IsField S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `faithfulSMul_iff_algebraMap_injective`：faithfulSMul_iff_algebraMap_injec
tive : FaithfulSMul R A ↔ Injective (algebraMap R A)
· 使用定理 `IsLocalHom.isField`：∀ {A : Type u_1} {B : Type u_2} {F : Type u_3} [inst
 : Semiring A] [inst_1 : Semiring B] [inst_2 : FunLike F A B]   [MonoidWithZeroH
omClass …
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
If the integral extension `R → S` is injective, and `S` is a field, then `R` is 
also a field.
-/
theorem isField_of_isIntegral_of_isField (hRS : Function.Injective (algebraMap R S))
    (hS : IsField S) : IsField R :=
  have := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  IsLocalHom.isField hRS hS
/-
**Algebra.IsIntegral.isField_iff_isField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.isField_iff_isField [IsDomain S] (hRS : Function.Inject
ive (algebraMap R S)) : IsField R ↔ IsField S
参数：hRS : Function.Injective (algebraMap R S)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isField_of_isIntegral_of_isField'`：isField_of_isIntegral_of_isField' [Co
mmRing R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] (hR :
 IsField R) : IsField S…
· 使用定理 `isField_of_isIntegral_of_isField`：isField_of_isIntegral_of_isField (hRS 
: Function.Injective (algebraMap R S)) (hS : IsField S) : IsField R
-/
theorem Algebra.IsIntegral.isField_iff_isField [IsDomain S]
    (hRS : Function.Injective (algebraMap R S)) : IsField R ↔ IsField S :=
  ⟨isField_of_isIntegral_of_isField', isField_of_isIntegral_of_isField hRS⟩
/-
**Ideal.IsMaximal.ne_bot_of_isIntegral_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsMaximal.ne_bot_of_isIntegral_int [CharZero R] [Algebra.IsIntegral 
Int R] (I : Ideal R) [I.IsMaximal] : I != ⊥
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Int.not_isField`：¬IsField ℤ
· 使用定理 `isField_of_isIntegral_of_isField`：isField_of_isIntegral_of_isField (hRS 
: Function.Injective (algebraMap R S)) (hS : IsField S) : IsField R
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
-/
theorem Ideal.IsMaximal.ne_bot_of_isIntegral_int
    [CharZero R] [Algebra.IsIntegral ℤ R] (I : Ideal R) [I.IsMaximal] : I ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField ‹_› fun h ↦ Int.not_isField
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective ℤ R) h)

variable (R) in
/-
**Algebra.ker_algebraMap_isMaximal_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.ker_algebraMap_isMaximal_of_isIntegral (k : Type*) [Field k] [Alge
bra R k] [Algebra.IsIntegral R k] : (RingHom.ker (algebraMap R k)).IsMaximal
参数：k : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.bot_isMaximal`：bot_isMaximal : IsMaximal (⊥ : Ideal K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Sem
iring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F 
R S] (…
· 使用定理 `Ideal.Quotient.maximal_ideal_iff_isField_quotient`：maximal_ideal_iff_isF
ield_quotient {R} [CommRing R] (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I)
· 使用定理 `isField_of_isIntegral_of_isField`：isField_of_isIntegral_of_isField (hRS 
: Function.Injective (algebraMap R S)) (hS : IsField S) : IsField R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.algebraMap_quotient_injective`：algebraMap_quotient_injective {R} [
CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] : Function.Injective (alg
ebraMap (R ⧸ I.comap (alg…
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
-/
theorem Algebra.ker_algebraMap_isMaximal_of_isIntegral (k : Type*) [Field k] [Algebra R k]
    [Algebra.IsIntegral R k] : (RingHom.ker (algebraMap R k)).IsMaximal := by
  have := Ideal.bot_isMaximal (K := k)
  rw [RingHom.ker, Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.field _).toIsField

end Algebra

/-
**integralClosure_idem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integralClosure_idem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
 : integralClosure (integralClosure R A) A = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem integralClosure_idem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    integralClosure (integralClosure R A) A = ⊥ :=
  letI := (integralClosure R A).algebra
  eq_bot_iff.2 fun x hx ↦ Algebra.mem_bot.2
    ⟨⟨x, isIntegral_trans (A := integralClosure R A) x hx⟩, rfl⟩

section IsDomain

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain (integralClosure R S) :=
  inferInstance
/-
**roots_mem_integralClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：roots_mem_integralClosure {f : R[X]} (hf : f.Monic) {a : S} (ha : a in f.a
roots S) : a in integralClosure R S
参数：hf : f.Monic；ha : a in f.aroots S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval₂_eq_eval_map`：eval₂_eq_eval_map {x : S} : p.eval₂ f x = 
(p.map f).eval x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
-/
theorem roots_mem_integralClosure {f : R[X]} (hf : f.Monic) {a : S}
    (ha : a ∈ f.aroots S) : a ∈ integralClosure R S :=
  ⟨f, hf, (eval₂_eq_eval_map _).trans <| (mem_roots <| (hf.map _).ne_zero).1 ha⟩

end IsDomain

