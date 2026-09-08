/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Junyan Xu
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!

# Localizations of domains as subalgebras of the fraction field.

Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
does not contain zero, this file constructs the localization of `A` at `S`
as a subalgebra of the field `K` over `A`.

-/

@[expose] public section


namespace Localization

open nonZeroDivisors

variable {A : Type*} (K : Type*) [CommRing A] (S : Submonoid A) (hS : S ≤ A⁰)

section CommRing

variable [CommRing K] [Algebra A K] [IsFractionRing A K]

/-
**Localization.map_isUnit_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：map_isUnit_of_le (hS : S <= A⁰) (s : S) : IsUnit (algebraMap A K s)
参数：hS : S <= A⁰；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_isUnit_of_le (hS : S ≤ A⁰) (s : S) : IsUnit (algebraMap A K s) := by
  apply IsLocalization.map_units K (⟨s.1, hS s.2⟩ : A⁰)

/-- The canonical map from a localization of `A` at `S` to the fraction ring
  of `A`, given that `S ≤ A⁰`. -/
/-
**Localization.mapToFractionRing** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：mapToFractionRing (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S
 B] (hS : S <= A⁰) : B ->ₐ[A] K
参数：B : Type*；hS : S <= A⁰。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.map_isUnit_of_le`：map_isUnit_of_le (hS : S <= A⁰) (s : S) :
 IsUnit (algebraMap A K s)

--- 原说明 ---
The canonical map from a localization of `A` at `S` to the fraction ring
  of `A`, given that `S ≤ A⁰`.
-/
noncomputable def mapToFractionRing (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) : B →ₐ[A] K :=
  { IsLocalization.lift (map_isUnit_of_le K S hS) with commutes' := fun a => by simp }

@[simp]
/-
**Localization.mapToFractionRing_apply** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mapToFractionRing_apply {B : Type*} [CommRing B] [Algebra A B] [IsLocaliza
tion S B] (hS : S <= A⁰) (b : B) : mapToFractionRing K S B hS b = IsLocalization
.lift (map_isUnit_of_le K S hS) b
参数：hS : S <= A⁰；b : B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapToFractionRing_apply {B : Type*} [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) (b : B) :
    mapToFractionRing K S B hS b = IsLocalization.lift (map_isUnit_of_le K S hS) b :=
  rfl
/-
**Localization.mem_range_mapToFractionRing_iff** 是 Mathlib 中的一个定理，位于命名空间 `Locali
zation`。
形式化陈述：mem_range_mapToFractionRing_iff (B : Type*) [CommRing B] [Algebra A B] [Is
Localization S B] (hS : S <= A⁰) (x : K) : x in (mapToFractionRing K S B hS).ran
ge ↔ exists (a s : A) (hs : s in S), x = IsLocalization.mk' K a ⟨s, hS hs⟩
参数：B : Type*；hS : S <= A⁰；x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalization.lift_mk'`：lift_mk' (x y) : lift hg (mk' S x y) = g x * ↑(
IsUnit.liftRight (g.toMonoidHom.domRestrict M) hg y)⁻¹
· 使用定理 `Localization.map_isUnit_of_le`：map_isUnit_of_le (hS : S <= A⁰) (s : S) :
 IsUnit (algebraMap A K s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_range_mapToFractionRing_iff (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    (hS : S ≤ A⁰) (x : K) :
    x ∈ (mapToFractionRing K S B hS).range ↔
      ∃ (a s : A) (hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ :=
  ⟨by
    rintro ⟨x, rfl⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
    use a, s, s.2
    apply IsLocalization.lift_mk', by
    rintro ⟨a, s, hs, rfl⟩
    use IsLocalization.mk' _ a ⟨s, hs⟩
    apply IsLocalization.lift_mk'⟩
/-
**Localization.isLocalization_range_mapToFractionRing** 是 Mathlib 中的一个实例，位于命名空间 
`Localization`。
形式化陈述：isLocalization_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A
 B] [IsLocalization S B] (hS : S <= A⁰) : IsLocalization S (mapToFractionRing K 
S B hS).range
参数：B : Type*；hS : S <= A⁰。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Localization.map_isUnit_of_le`：map_isUnit_of_le (hS : S <= A⁰) (s : S) :
 IsUnit (algebraMap A K s)
· 使用定理 `IsLocalization.lift_injective_iff`：lift_injective_iff : Injective (lift 
hg : S -> P) ↔ forall x y, algebraMap R S x = algebraMap R S y ↔ g x = g y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)
-/
instance isLocalization_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S ≤ A⁰) : IsLocalization S (mapToFractionRing K S B hS).range :=
  IsLocalization.isLocalization_of_algEquiv S <|
    show B ≃ₐ[A] _ from AlgEquiv.ofBijective (mapToFractionRing K S B hS).rangeRestrict (by
      refine ⟨fun a b h => ?_, Set.rangeFactorization_surjective⟩
      refine (IsLocalization.lift_injective_iff _).2 (fun a b => ?_) (Subtype.ext_iff.1 h)
      exact ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h),
        fun h => congr_arg _ (IsFractionRing.injective A K h)⟩)
/-
**Localization.isFractionRing_range_mapToFractionRing** 是 Mathlib 中的一个实例，位于命名空间 
`Localization`。
形式化陈述：isFractionRing_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A
 B] [IsLocalization S B] (hS : S <= A⁰) : IsFractionRing (mapToFractionRing K S 
B hS).range K
参数：B : Type*；hS : S <= A⁰。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.isFractionRing_of_isLocalization`：isFractionRing_of_isLoc
alization (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [A
lgebra S T] [IsScalarTower R S T] [Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance isFractionRing_range_mapToFractionRing (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (hS : S ≤ A⁰) : IsFractionRing (mapToFractionRing K S B hS).range K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

/-- Given a commutative ring `A` with fraction ring `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`IsLocalization.mk' K a ⟨s, _⟩`, where `s ∈ S`.
-/
/-
**Localization.subalgebra** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：subalgebra (hS : S <= A⁰) : Subalgebra A K
参数：hS : S <= A⁰。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…

--- 原说明 ---
Given a commutative ring `A` with fraction ring `K`, and a submonoid `S` of `A` 
which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`IsLocalization.mk' K a ⟨s, _⟩`, where `s ∈ S`.
-/
noncomputable def subalgebra (hS : S ≤ A⁰) : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A) (hs : s ∈ S), x = IsLocalization.mk' K a ⟨s, hS hs⟩ } <| by
    ext
    symm
    apply mem_range_mapToFractionRing_iff

namespace subalgebra

/-
**Localization.subalgebra.isLocalization_subalgebra** 是 Mathlib 中的一个实例，位于命名空间 `L
ocalization.subalgebra`。
形式化陈述：isLocalization_subalgebra : IsLocalization S (subalgebra K S hS)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.copy_eq`：copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑
S) : S.copy s hs = S
-/
instance isLocalization_subalgebra : IsLocalization S (subalgebra K S hS) := by
  dsimp +instances only [Localization.subalgebra]
  rw [Subalgebra.copy_eq]
  infer_instance
/-
**Localization.subalgebra.isFractionRing** 是 Mathlib 中的一个实例，位于命名空间 `Localization
.subalgebra`。
形式化陈述：isFractionRing : IsFractionRing (subalgebra K S hS) K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.isFractionRing_of_isLocalization`：isFractionRing_of_isLoc
alization (S T : Type*) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [A
lgebra S T] [IsScalarTower R S T] [Is…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance isFractionRing : IsFractionRing (subalgebra K S hS) K :=
  IsFractionRing.isFractionRing_of_isLocalization S _ _ hS

end subalgebra

end CommRing

section Field

variable [Field K] [Algebra A K] [IsFractionRing A K]

namespace subalgebra

/-
**Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField** 是 Mathlib 中的
一个定理，位于命名空间 `Localization.subalgebra`。
形式化陈述：mem_range_mapToFractionRing_iff_ofField (B : Type*) [CommRing B] [Algebra 
A B] [IsLocalization S B] (x : K) : x in (mapToFractionRing K S B hS).range ↔ ex
ists (a s : A) (_ : s in S), x = algebraMap A K a * (algebraMap A K s)⁻¹
参数：B : Type*；x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mem_range_mapToFractionRing_iff`：mem_range_mapToFractionRin
g_iff (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B] (hS : S <= A⁰)
 (x : K) : x in (mapToFractionRing…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range_mapToFractionRing_iff_ofField (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization S B] (x : K) :
    x ∈ (mapToFractionRing K S B hS).range ↔
      ∃ (a s : A) (_ : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ := by
  rw [mem_range_mapToFractionRing_iff]
  convert! Iff.rfl
  congr
  rw [Units.val_inv_eq_inv_val]
  rfl

/-- Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`algebraMap A K a * (algebraMap A K s)⁻¹` where `a s : A` and `s ∈ S`.
-/
/-
**Localization.subalgebra.ofField** 是 Mathlib 中的一个定义，位于命名空间 `Localization.subalg
ebra`。
形式化陈述：ofField : Subalgebra A K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a domain `A` with fraction field `K`, and a submonoid `S` of `A` which
contains no zero divisor, this is the localization of `A` at `S`, considered as
a subalgebra of `K` over `A`.

The carrier of this subalgebra is defined as the set of all `x : K` of the form
`algebraMap A K a * (algebraMap A K s)⁻¹` where `a s : A` and `s ∈ S`.
-/
noncomputable def ofField : Subalgebra A K :=
  (mapToFractionRing K S (Localization S) hS).range.copy
      { x | ∃ (a s : A) (_ : s ∈ S), x = algebraMap A K a * (algebraMap A K s)⁻¹ } <| by
    ext
    symm
    apply mem_range_mapToFractionRing_iff_ofField
/-
**Localization.subalgebra.ofField_eq** 是 Mathlib 中的一个定理，位于命名空间 `Localization.sub
algebra`。
形式化陈述：ofField_eq : ofField K S hS = subalgebra K S hS
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.copy_eq`：copy_eq (S : Subalgebra R A) (s : Set A) (hs : s = ↑
S) : S.copy s hs = S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofField_eq : ofField K S hS = subalgebra K S hS := by
  simp_rw [ofField, subalgebra, Subalgebra.copy_eq]
/-
**Localization.subalgebra.isLocalization_ofField** 是 Mathlib 中的一个实例，位于命名空间 `Loca
lization.subalgebra`。
形式化陈述：isLocalization_ofField : IsLocalization S (ofField K S hS)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.subalgebra.ofField_eq`：ofField_eq : ofField K S hS = subalg
ebra K S hS
-/
instance isLocalization_ofField : IsLocalization S (ofField K S hS) := by
  rw [ofField_eq]
  exact isLocalization_subalgebra K S hS
/-
**Localization.subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Localization.subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Subalgebra A K) : IsFractionRing S K := by
  refine IsFractionRing.of_field S K fun z ↦ ?_
  rcases IsFractionRing.div_surjective A z with ⟨x, y, _, eq⟩
  exact ⟨algebraMap A S x, algebraMap A S y, eq.symm⟩
/-
**Localization.subalgebra.isFractionRing_ofField** 是 Mathlib 中的一个实例，位于命名空间 `Loca
lization.subalgebra`。
形式化陈述：isFractionRing_ofField : IsFractionRing (ofField K S hS) K
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra`：∀ {A : T
ype u_1} (K : Type u_2) [inst : CommRing A] [inst_1 : Field K] [inst_2 : Algebra
 A K] [IsFractionRing A K]   (S : Subalgebra A K), I…
-/
instance isFractionRing_ofField : IsFractionRing (ofField K S hS) K :=
  inferInstance

end subalgebra

end Field

end Localization

