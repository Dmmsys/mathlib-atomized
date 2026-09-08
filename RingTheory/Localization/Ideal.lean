/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs

import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Ideals in localizations of commutative rings

## Implementation notes
See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions

-/

@[expose] public section


namespace IsLocalization

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]
variable [Algebra R S] [IsLocalization M S]

variable {M S} in
/-
**IsLocalization.mk'_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submonoid R} {S : Type u_2} 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 {x : R} {y : ↥M} {I : Ideal S},   IsLocalization.mk' S x y ∈ I ↔ (algebraMap R 
S) x ∈ I
参数：algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem mk'_mem_iff {x} {y : M} {I : Ideal S} : mk' S x y ∈ I ↔ algebraMap R S x ∈ I := by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this

/-- Explicit characterization of the ideal given by `Ideal.map (algebraMap R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_algebraMap_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
/-
**IsLocalization.map_ideal** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit characterization of the ideal given by `Ideal.map (algebraMap R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicit
ly.
This definition is only meant to be used in proving `mem_map_algebraMap_iff`,
and any proof that needs to refer to the explicit carrier set should use that th
eorem.
-/
private def map_ideal (I : Ideal R) : Ideal S :=
  Submodule.localized' S M (Algebra.linearMap R S) I
/-
**IsLocalization.mem_map_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizatio
n`。
形式化陈述：mem_map_algebraMap_iff {I : Ideal R} {z} : z in Ideal.map (algebraMap R S)
 I ↔ exists x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `_private.Mathlib.RingTheory.Localization.Ideal.0.IsLocalization.map_idea
l.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) (S : Type u_2
) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLoc…
· 使用定理 `Ideal.map.eq_1`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   (I : Ideal R), I
deal…
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Submodule.localized'_eq_span`：∀ {R : Type u_1} (S : Type u_2) {M : Type 
u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 
: AddCommMonoid M]…
· 使用定理 `Algebra.coe_linearMap`：coe_linearMap : ⇑(Algebra.linearMap R A) = algebr
aMap R A
· 使用引理 `Submodule.mem_localized'`：mem_localized' (x : N) : x in localized' S p f
 M' ↔ exists m in M', exists s : p, IsLocalizedModule.mk' f m s = x
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_eq_mk'`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [inst_2 : Algebra R A] 
[inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
-/
theorem mem_map_algebraMap_iff {I : Ideal R} {z} : z ∈ Ideal.map (algebraMap R S) I ↔
    ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 := by
  rw [← show map_ideal M S I = Ideal.map (algebraMap R S) I by
    rw [map_ideal, Ideal.map, Ideal.span, Submodule.localized'_eq_span, Algebra.coe_linearMap],
    map_ideal, Submodule.mem_localized']
  constructor
  · rintro ⟨x, hx, s, rfl⟩
    exact ⟨⟨⟨x, hx⟩, s⟩, by rw [← IsLocalization.mk'_eq_mk', IsLocalization.mk'_spec]⟩
  · rintro ⟨⟨⟨x, hx⟩, s⟩, h⟩
    refine ⟨x, hx, s, ?_⟩
    rw [← IsLocalization.mk'_eq_mk', eq_comm, IsLocalization.eq_mk'_iff_mul_eq]
    exact h
/-
**IsLocalization.mk'_mem_map_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
ation`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 : IsLocalization M S]
 (I : Ideal R) (x : R) (s : ↥M),   IsLocalization.mk' S x s ∈ Ideal.map (algebra
Map R S) I ↔ ∃ s ∈ M, s * x ∈ I
参数：M : Submonoid R；S : Type u_2；I : Ideal R；x : R；s : ↥M；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.unit_mul_mem_iff_mem`：unit_mul_mem_iff_mem {x y : α} (hy : IsUnit 
y) : y * x in I ↔ x in I
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mk'_mem_map_algebraMap_iff (I : Ideal R) (x : R) (s : M) :
    IsLocalization.mk' S x s ∈ I.map (algebraMap R S) ↔ ∃ s ∈ M, s * x ∈ I := by
  rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S s), IsLocalization.mk'_spec',
    IsLocalization.mem_map_algebraMap_iff M]
  simp_rw [← map_mul, IsLocalization.eq_iff_exists M, mul_comm x, ← mul_assoc, ← Submonoid.coe_mul]
  exact ⟨fun ⟨⟨y, t⟩, c, h⟩ ↦ ⟨_, (c * t).2, h ▸ I.mul_mem_left c.1 y.2⟩, fun ⟨s, hs, h⟩ ↦
    ⟨⟨⟨_, h⟩, ⟨s, hs⟩⟩, 1, by simp⟩⟩
/-
**IsLocalization.algebraMap_mem_map_algebraMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Is
Localization`。
形式化陈述：algebraMap_mem_map_algebraMap_iff (I : Ideal R) (x : R) : algebraMap R S x
 in I.map (algebraMap R S) ↔ exists m in M, m * x in I
参数：I : Ideal R；x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_mem_map_algebraMap_iff`：∀ {R : Type u_1} [inst : Comm
Semiring R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] [inst_3 : IsLoc…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma algebraMap_mem_map_algebraMap_iff (I : Ideal R) (x : R) :
    algebraMap R S x ∈ I.map (algebraMap R S) ↔
      ∃ m ∈ M, m * x ∈ I := by
  rw [← IsLocalization.mk'_one (M := M), mk'_mem_map_algebraMap_iff]
/-
**IsLocalization.map_algebraMap_ne_top_iff_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `I
sLocalization`。
形式化陈述：map_algebraMap_ne_top_iff_disjoint (I : Ideal R) : I.map (algebraMap R S) 
!= ⊤ ↔ Disjoint (M : Set R) (I : Set R)
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用引理 `IsLocalization.algebraMap_mem_map_algebraMap_iff`：algebraMap_mem_map_alg
ebraMap_iff (I : Ideal R) (x : R) : algebraMap R S x in I.map (algebraMap R S) ↔
 exists m in M, m * x in I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_algebraMap_ne_top_iff_disjoint (I : Ideal R) :
    I.map (algebraMap R S) ≠ ⊤ ↔ Disjoint (M : Set R) (I : Set R) := by
  simp only [ne_eq, Ideal.eq_top_iff_one, ← map_one (algebraMap R S), not_iff_comm,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  simp [Set.disjoint_left]

set_option backward.isDefEq.respectTransparency false in
include M in
/-
**IsLocalization.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Submonoid R) (S : Type u_2) 
[inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [IsLocalization M S] (I J : I
deal R),   Ideal.map (algebraMap R S) (I ⊓ J) = Ideal.map (algebraMap R S) I ⊓ I
deal.map (algebraMap R S) J
参数：M : Submonoid R；S : Type u_2；I J : Ideal R；algebraMap R S；I ⊓ J；algebraMap R 
S；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.map_inf_le`：map_inf_le : map f (I ⊓ J) <= map f I ⊓ map f J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.eq`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submono
id R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 
: IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `IsLocalization.mk'_cancel`：∀ {R : Type u_1} [inst : CommSemiring R] {M :
 Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] 
[inst_3 : IsLoc…
-/
protected theorem map_inf (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (Ideal.map_inf_le (algebraMap R S)) fun x hx ↦ ?_
  simp only [Ideal.mem_inf, IsLocalization.mem_map_algebraMap_iff M, Prod.exists] at hx ⊢
  obtain ⟨⟨⟨i, hi⟩, mi, hi'⟩, ⟨j, hj⟩, mj, hj'⟩ := hx
  simp only [← IsLocalization.eq_mk'_iff_mul_eq] at hi' hj'
  obtain ⟨m, hm⟩ := IsLocalization.eq.mp (hi'.symm.trans hj')
  rw [← mul_assoc, ← mul_assoc, mul_comm, ← mul_comm (j : R)] at hm
  refine ⟨⟨i * (m * mj : M), I.mul_mem_right _ hi, hm ▸ J.mul_mem_right _ hj⟩, mi * (m * mj), ?_⟩
  rwa [← IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, IsLocalization.mk'_cancel]

/-- `IsLocalization.map_inf` as an `FrameHom`. -/
/-
**IsLocalization.mapFrameHom** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：mapFrameHom : FrameHom (Ideal R) (Ideal S) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_inf`：∀ {R : Type u_1} [inst : CommSemiring R] (M : Su
bmonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [Is
Localization…

--- 原说明 ---
`IsLocalization.map_inf` as an `FrameHom`.
-/
def mapFrameHom : FrameHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := IsLocalization.map_inf M S
  map_top' := Ideal.map_top (algebraMap R S)
  map_sSup' _ := (Ideal.gc_map_comap (algebraMap R S)).l_sSup.trans sSup_image.symm

@[simp]
/-
**IsLocalization.mapFrameHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization`。
形式化陈述：mapFrameHom_apply (I : Ideal R) : IsLocalization.mapFrameHom M S I = I.map
 (algebraMap R S)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapFrameHom_apply (I : Ideal R) :
    IsLocalization.mapFrameHom M S I = I.map (algebraMap R S) :=
  rfl

include M in
/-
**IsLocalization.map_under** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：map_under (J : Ideal S) : Ideal.map (algebraMap R S) (J.under R) = J
参数：J : Ideal S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
theorem map_under (J : Ideal S) :
    Ideal.map (algebraMap R S) (J.under R) = J :=
  le_antisymm (Ideal.map_le_iff_le_comap.2 le_rfl) fun x hJ => by
    obtain ⟨r, s, hx⟩ := exists_mk'_eq M x
    rw [← hx] at hJ ⊢
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r ∈ J from
            mk'_spec S r s ▸ J.mul_mem_right ((algebraMap R S) s) hJ))

@[deprecated (since := "2026-04-09")] alias map_comap := map_under
/-
**IsLocalization.under_map_of_isPrimary_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsLo
calization`。
形式化陈述：under_map_of_isPrimary_disjoint {I : Ideal R} (hI : I.IsPrimary) (hM : Dis
joint (M : Set R) I) : (Ideal.map (algebraMap R S) I).under R = I
参数：hI : I.IsPrimary；hM : Disjoint (M : Set R) I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Ideal.isPrimary_iff`：isPrimary_iff {I : Ideal R} : I.IsPrimary ↔ I != ⊤ 
∧ forall {x y : R}, x * y in I -> x in I ∨ y in radical I
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
-/
theorem under_map_of_isPrimary_disjoint
    {I : Ideal R} (hI : I.IsPrimary) (hM : Disjoint (M : Set R) I) :
    (Ideal.map (algebraMap R S) I).under R = I := by
  have key : Disjoint (M : Set R) I.radical := by
    contrapose hM
    rw [Set.not_disjoint_iff] at hM ⊢
    obtain ⟨a, ha, k, hk⟩ := hM
    exact ⟨a ^ k, pow_mem ha k, hk⟩
  refine le_antisymm (fun a ha ↦ ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, IsLocalization.mem_map_algebraMap_iff M S] at ha
  obtain ⟨⟨b, s⟩, h⟩ := ha
  replace h : algebraMap R S (s * a) = algebraMap R S b := by
    simpa only [← map_mul, mul_comm] using h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 h
  have : a * (c * s : M) ∈ I := by
    rw [mul_comm, Submonoid.coe_mul, mul_assoc, hc]
    exact I.mul_mem_left c b.2
  exact ((Ideal.isPrimary_iff.mp hI).2 this).resolve_right (Set.disjoint_left.mp key (c * s).2)

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrimary_disjoint :=
  under_map_of_isPrimary_disjoint
/-
**IsLocalization.under_map_of_isPrime_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lization`。
形式化陈述：under_map_of_isPrime_disjoint {I : Ideal R} (hI : I.IsPrime) (hM : Disjoin
t (M : Set R) I) : (Ideal.map (algebraMap R S) I).under R = I
参数：hI : I.IsPrime；hM : Disjoint (M : Set R) I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.under_map_of_isPrimary_disjoint`：under_map_of_isPrimary_d
isjoint {I : Ideal R} (hI : I.IsPrimary) (hM : Disjoint (M : Set R) I) : (Ideal.
map (algebraMap R S) I).under R = I
· 使用定理 `Ideal.IsPrime.isPrimary`：∀ {R : Type u_1} [inst : CommSemiring R] {I : I
deal R}, I.IsPrime → I.IsPrimary
-/
theorem under_map_of_isPrime_disjoint {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) :
    (Ideal.map (algebraMap R S) I).under R = I :=
  under_map_of_isPrimary_disjoint M S hI.isPrimary hM

@[deprecated (since := "2026-04-09")] alias comap_map_of_isPrime_disjoint :=
  under_map_of_isPrime_disjoint
/-
**IsLocalization.liesOver_map_of_isPrime_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsL
ocalization`。
形式化陈述：liesOver_map_of_isPrime_disjoint {I : Ideal R} [I.IsPrime] (hM : Disjoint 
(M : Set R) I) : (I.map (algebraMap R S)).LiesOver I
参数：hM : Disjoint (M : Set R) I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
-/
theorem liesOver_map_of_isPrime_disjoint {I : Ideal R} [I.IsPrime] (hM : Disjoint (M : Set R) I) :
    (I.map (algebraMap R S)).LiesOver I :=
  ⟨(under_map_of_isPrime_disjoint M S ‹_› hM).symm⟩

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
/-
**IsLocalization.orderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：orderEmbedding : Ideal S ↪o Ideal R where toFun J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` 
is
embedded in the ordering of ideals of `R`.
-/
def orderEmbedding : Ideal S ↪o Ideal R where
  toFun J := J.under R
  inj' := Function.LeftInverse.injective (map_under M S)
  map_rel_iff' := by
    rintro J₁ J₂
    constructor
    · exact fun hJ => (map_under M S) J₁ ▸ (map_under M S) J₂ ▸ Ideal.map_mono hJ
    · exact fun hJ => Ideal.comap_mono hJ

include M in
/-
**IsLocalization.under_le_under_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：under_le_under_iff {I J : Ideal S} : I.under R <= J.under R ↔ I <= J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
theorem under_le_under_iff {I J : Ideal S} :
    I.under R ≤ J.under R ↔ I ≤ J := by
  exact (IsLocalization.orderEmbedding M S).le_iff_le

@[deprecated (since := "2026-04-09")] alias comap_le_comap_iff := under_le_under_iff

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
/-
**IsLocalization.isPrime_iff_isPrime_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
ization`。
形式化陈述：isPrime_iff_isPrime_disjoint (J : Ideal S) : J.IsPrime ↔ (J.under R).IsPri
me ∧ Disjoint (M : Set R) (J.under R)
参数：J : Ideal S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.IsPrime.mul_mem_iff_mem_or_mem`：∀ {α : Type u} [inst : Semiring α]
 {I : Ideal α} [I.IsTwoSided], I.IsPrime → ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ 
I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsLocalization.mk'_mem_iff`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S]
 [inst_3 : IsLoc…

--- 原说明 ---
If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism
-/
theorem isPrime_iff_isPrime_disjoint (J : Ideal S) :
    J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.under R) := by
  constructor
  · refine fun h =>
      ⟨⟨?_, ?_⟩,
        Set.disjoint_left.mpr fun m hm1 hm2 =>
          h.ne_top (Ideal.eq_top_of_isUnit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩
    · refine fun hJ => h.ne_top ?_
      rw [eq_top_iff, ← (orderEmbedding M S).le_iff_le]
      exact le_of_eq hJ.symm
    · intro x y hxy
      rw [Ideal.mem_comap, map_mul] at hxy
      exact h.mem_or_mem hxy
  · refine fun h => ⟨fun hJ => h.left.ne_top (eq_top_iff.2 ?_), ?_⟩
    · rwa [eq_top_iff, ← (orderEmbedding M S).le_iff_le] at hJ
    · intro x y hxy
      obtain ⟨a, s, ha⟩ := exists_mk'_eq M x
      obtain ⟨b, t, hb⟩ := exists_mk'_eq M y
      have : mk' S (a * b) (s * t) ∈ J := by rwa [mk'_mul, ha, hb]
      rw [mk'_mem_iff, ← Ideal.mem_comap] at this
      have this₂ := (h.1).mul_mem_iff_mem_or_mem.1 this
      rw [Ideal.mem_comap, Ideal.mem_comap] at this₂
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff]

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
/-
**IsLocalization.isPrime_of_isPrime_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zation`。
形式化陈述：isPrime_of_isPrime_disjoint (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint 
(M : Set R) ↑I) : (Ideal.map (algebraMap R S) I).IsPrime
参数：I : Ideal R；hp : I.IsPrime；hd : Disjoint (M : Set R) ↑I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.isPrime_iff_isPrime_disjoint`：isPrime_iff_isPrime_disjoin
t (J : Ideal S) : J.IsPrime ↔ (J.under R).IsPrime ∧ Disjoint (M : Set R) (J.unde
r R)
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I

--- 原说明 ---
If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the rev
erse implication
-/
theorem isPrime_of_isPrime_disjoint (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) :
    (Ideal.map (algebraMap R S) I).IsPrime := by
  rw [isPrime_iff_isPrime_disjoint M S, under_map_of_isPrime_disjoint M S hp hd]
  exact ⟨hp, hd⟩
/-
**IsLocalization.disjoint_under_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：disjoint_under_iff (J : Ideal S) : Disjoint (M : Set R) (J.under R) ↔ J !=
 ⊤
参数：J : Ideal S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
-/
theorem disjoint_under_iff (J : Ideal S) :
    Disjoint (M : Set R) (J.under R) ↔ J ≠ ⊤ := by
  rw [← iff_not_comm, Set.not_disjoint_iff]
  constructor
  · rintro rfl
    exact ⟨1, M.one_mem, ⟨⟩⟩
  · rintro ⟨x, hxM, hxJ⟩
    exact J.eq_top_of_isUnit_mem hxJ (IsLocalization.map_units S ⟨x, hxM⟩)

@[deprecated (since := "2026-04-09")] alias disjoint_comap_iff := disjoint_under_iff

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
/-
**IsLocalization.orderIsoOfPrime** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     (M : Submonoid R) →      
 (S : Type u_2) →         [inst_1 : CommSemiring S] →           [inst_2 : Algebr
a R S] → [IsLocalization M S] → { p // p.IsPrime } ≃o { p // p.IsPrime ∧ Disjoin
t ↑M ↑p }
参数：M : Submonoid R；S : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`
-/
@[simps] def orderIsoOfPrime :
    { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) ↑p } where
  toFun p := ⟨p.1.under R, (isPrime_iff_isPrime_disjoint M S p.1).1 p.2⟩
  invFun p := ⟨Ideal.map (algebraMap R S) p.1, isPrime_of_isPrime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv J := Subtype.ext (map_under M S J)
  right_inv I := Subtype.ext (under_map_of_isPrime_disjoint M S I.2.1 I.2.2)
  map_rel_iff' {I I'} := by
    constructor
    · exact fun h => show I.val ≤ I'.val from map_under M S I.val ▸
        map_under M S I'.val ▸ Ideal.map_mono h
    exact fun h x hx => h hx

/-- The prime spectrum of the localization of a ring at a submonoid `M` are in
order-preserving bijection with subset of the prime spectrum of the ring consisting of
prime ideals disjoint from `M`. -/
/-
**IsLocalization.primeSpectrumOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization
`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     (M : Submonoid R) →      
 (S : Type u_2) →         [inst_1 : CommSemiring S] →           [inst_2 : Algebr
a R S] → [IsLocalization M S] → PrimeSpectrum S ≃o { p // Disjoint ↑M ↑p.asIdeal
 }
参数：M : Submonoid R；S : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime spectrum of the localization of a ring at a submonoid `M` are in
order-preserving bijection with subset of the prime spectrum of the ring consist
ing of
prime ideals disjoint from `M`.
-/
@[simps!] def primeSpectrumOrderIso :
    PrimeSpectrum S ≃o {p : PrimeSpectrum R // Disjoint (M : Set R) p.asIdeal} :=
  (PrimeSpectrum.equivSubtype S).trans <| (orderIsoOfPrime M S).trans
    ⟨⟨fun p ↦ ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p ↦ ⟨p.1.1, p.1.2, p.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩

include M in
/-
**IsLocalization.map_radical** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization`。
形式化陈述：map_radical (I : Ideal R) : I.radical.map (algebraMap R S) = (I.map (algeb
raMap R S)).radical
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ideal.map_radical_le`：map_radical_le : map f (radical I) <= radical (map
 f I)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_mem_map_algebraMap_iff`：∀ {R : Type u_1} [inst : Comm
Semiring R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] [inst_3 : IsLoc…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a
（共 35 条，此处仅展示前 30 条）
-/
lemma map_radical (I : Ideal R) :
    I.radical.map (algebraMap R S) = (I.map (algebraMap R S)).radical := by
  refine (I.map_radical_le (algebraMap R S)).antisymm ?_
  rintro x ⟨n, hn⟩
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [← IsLocalization.mk'_pow, IsLocalization.mk'_mem_map_algebraMap_iff M] at hn ⊢
  obtain ⟨s, hs, h⟩ := hn
  refine ⟨s, hs, n + 1, by convert! I.mul_mem_left (s ^ n * x) h; ring⟩
/-
**IsLocalization.ideal_eq_iInf_under_map_away** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
ization`。
形式化陈述：ideal_eq_iInf_under_map_away {S : Finset R} (hS : Ideal.span (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Submodule.mem_of_span_eq_top_of_smul_pow_mem`：mem_of_span_eq_top_of_smul
_pow_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M) (H : f
orall r : s, exists n : Nat, ((r :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem ideal_eq_iInf_under_map_away {S : Finset R} (hS : Ideal.span (α := R) S = ⊤) (I : Ideal R) :
    I = ⨅ f ∈ S, (I.map (algebraMap R (Localization.Away f))).under R := by
  apply le_antisymm
  · simp only [le_iInf₂_iff, ← Ideal.map_le_iff_le_comap, le_refl, implies_true]
  · intro x hx
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hS
    rintro ⟨s, hs⟩
    simp only [Ideal.mem_iInf, Ideal.mem_comap] at hx
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, e⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers s) _).mp (hx s hs)
    dsimp only at e
    rw [← map_mul, IsLocalization.eq_iff_exists (.powers s)] at e
    obtain ⟨⟨_, m, rfl⟩, e⟩ := e
    use m + n
    dsimp at e ⊢
    rw [pow_add, mul_assoc, ← mul_comm x, e]
    exact I.mul_mem_left _ y.2

@[deprecated (since := "2026-04-09")] alias ideal_eq_iInf_comap_map_away :=
  ideal_eq_iInf_under_map_away
/-
**IsLocalization.map_eq_top_of_not_subset** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizat
ion`。
形式化陈述：map_eq_top_of_not_subset {I : Ideal R} (hle : ¬ (I : Set R) subseteq Mᶜ) :
 Ideal.map (algebraMap R S) I = ⊤
参数：hle : ¬ (I : Set R) subseteq Mᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
-/
lemma map_eq_top_of_not_subset {I : Ideal R} (hle : ¬ (I : Set R) ⊆ Mᶜ) :
    Ideal.map (algebraMap R S) I = ⊤ := by
  simp only [Set.not_subset_iff_exists_mem_notMem, Set.mem_compl_iff, not_not] at hle
  obtain ⟨y, hy, hny⟩ := hle
  apply Ideal.eq_top_of_isUnit_mem
  · exact Ideal.mem_map_of_mem (algebraMap R _) hy
  · exact IsLocalization.map_units _ (⟨y, hny⟩ : M)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S] [IsLocalization M S]

include M in
/-- `quotientMap` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already exist,
  and the localization necessarily maps the equivalence class of the inverse in the localization -/
/-
**IsLocalization.surjective_quotientMap_of_maximal_of_localization** 是 Mathlib 中
的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：surjective_quotientMap_of_maximal_of_localization {I : Ideal S} [I.IsPrime
] {J : Ideal R} {H : J <= I.under R} (hI : (I.under R).IsMaximal) : Function.Sur
jective (Ideal.quotientMap I (algebraMap R S) H)
参数：hI : (I.under R).IsMaximal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
· 使用定理 `Ideal.Quotient.maximal_ideal_iff_isField_quotient`：maximal_ideal_iff_isF
ield_quotient {R} [CommRing R] (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Ideal.quotientMap_mk`：quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTw
oSided] [J.IsTwoSided] {f : R ->+* S} {H : J <= I.comap f} {x : R} : quotientMap
 I f H (Qu…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
`quotientMap` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already ex
ist,
  and the localization necessarily maps the equivalence class of the inverse in 
the localization
-/
theorem surjective_quotientMap_of_maximal_of_localization {I : Ideal S} [I.IsPrime] {J : Ideal R}
    {H : J ≤ I.under R} (hI : (I.under R).IsMaximal) :
    Function.Surjective (Ideal.quotientMap I (algebraMap R S) H) := by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := exists_mk'_eq M s
  by_cases hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap] at hM
      convert! I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM
      rw [← mk'_eq_mul_mk'_one, mk'_self]
    exact ⟨0, eq_comm.1 (by simp [Ideal.Quotient.eq_zero_iff_mem, this])⟩
  · rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient] at hI
    obtain ⟨n, hn⟩ := hI.3 hM
    obtain ⟨rn, rfl⟩ := Ideal.Quotient.mk_surjective n
    refine ⟨(Ideal.Quotient.mk J) (r * rn), ?_⟩
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    replace hn := congr_arg (Ideal.quotientMap I (algebraMap R S) le_rfl) hn
    rw [map_one, map_mul] at hn
    rw [Ideal.quotientMap_mk, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ←
      Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, mk'_eq_mul_mk'_one]
    simp only [mul_eq_mul_left_iff, map_mul]
    refine
      Or.inl
        (mul_left_cancel₀ (M₀ := S ⧸ I)
          (fun hn =>
            hM
              (Ideal.Quotient.eq_zero_iff_mem.2
                (Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 hn))))
          (_root_.trans hn ?_))
    rw [← map_mul, ← mk'_eq_mul_mk'_one, mk'_self, map_one]

open nonZeroDivisors
/-
**IsLocalization.bot_lt_under_prime** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：bot_lt_under_prime [IsDomain R] (hM : M <= R⁰) (p : Ideal S) [hpp : p.IsPr
ime] (hp0 : p != ⊥) : ⊥ < p.under R
参数：hM : M <= R⁰；p : Ideal S；hp0 : p != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isDomain_of_le_nonZeroDivisors`：isDomain_of_le_nonZeroDiv
isors (hM : M <= nonZeroDivisors R) : IsDomain S where __ : IsCancelMulZero S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_bot_of_injective`：comap_bot_of_injective (hf : Function.Inje
ctive f) : Ideal.comap f ⊥ = ⊥
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem bot_lt_under_prime [IsDomain R] (hM : M ≤ R⁰) (p : Ideal S) [hpp : p.IsPrime]
    (hp0 : p ≠ ⊥) : ⊥ < p.under R := by
  have : IsDomain S := isDomain_of_le_nonZeroDivisors _ hM
  rw [← Ideal.comap_bot_of_injective (algebraMap R S) (IsLocalization.injective _ hM)]
  convert!
    (orderIsoOfPrime M S).lt_iff_lt.mpr
      (show (⟨⊥, Ideal.isPrime_bot⟩ : { p : Ideal S // p.IsPrime }) < ⟨p, hpp⟩ from hp0.bot_lt)

@[deprecated (since := "2026-04-09")] alias bot_lt_comap_prime := bot_lt_under_prime

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-
**IsLocalization._root_.Module.IsTorsionFree.of_isLocalization** 是 Mathlib 中的一个引
理，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.IsTorsionFree.of_isLocalization [IsDomain R] [IsDomain S] {Rₚ Sₚ : Type*}
    [CommRing Rₚ] [IsDomain Rₚ] [CommRing Sₚ] [Algebra R Rₚ] [Algebra R Sₚ] [Algebra S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] {M : Submonoid R} (hM : M ≤ R⁰)
    [IsLocalization M Rₚ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₚ]
    [Module.IsTorsionFree R S] : Module.IsTorsionFree Rₚ Sₚ := by
  have e : Algebra.algebraMapSubmonoid S M ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : algebraMap Rₚ Sₚ = IsLocalization.map (T := Algebra.algebraMapSubmonoid S M) Sₚ
    (algebraMap R S) (Submonoid.le_comap_map M) := by
    apply IsLocalization.ringHom_ext M
    simp only [IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq]
  rw [Module.isTorsionFree_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot,
    RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp only [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    Subtype.exists, exists_prop, this] at hx ⊢
  obtain ⟨_, ⟨a, ha, rfl⟩, H⟩ := hx
  simp only [← map_mul,
    (injective_iff_map_eq_zero' _).mp (FaithfulSMul.algebraMap_injective R S)] at H
  exact ⟨a, ha, H⟩
/-
**IsLocalization.of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalization`。
形式化陈述：of_surjective {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S'] 
(f : R ->+* R') (hf : Function.Surjective f) (g : S ->+* S') (hg : Function.Surj
ective g) (H : g.comp (algebraMap R S) = (algebraMap _ _).comp f) (H' : RingHom.
ker g <= (RingHom.ker f).map (algebraMap R S)) : IsLocalization (M.map f) S' whe
re map_units
参数：f : R ->+* R'；hf : Function.Surjective f；g : S ->+* S'；hg : Function.Surjecti
ve g；H : g.comp (algebraMap R S) = (algebraMap _ _).comp f；H' : RingHom.ker g <=
 (RingHom.ker f).map (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `IsLocalization.surj`：surj : forall z : S, exists x : R × M, z * algebraM
ap R S x.2 = algebraMap R S x.1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_mem_map_algebraMap_iff`：∀ {R : Type u_1} [inst : Comm
Semiring R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2
 : Algebra R S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
-/
lemma of_surjective {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R' S']
    (f : R →+* R') (hf : Function.Surjective f) (g : S →+* S') (hg : Function.Surjective g)
    (H : g.comp (algebraMap R S) = (algebraMap _ _).comp f)
    (H' : RingHom.ker g ≤ (RingHom.ker f).map (algebraMap R S)) : IsLocalization (M.map f) S' where
  map_units := by
    rintro ⟨_, y, hy, rfl⟩
    simpa only [← RingHom.comp_apply, H] using (IsLocalization.map_units S ⟨y, hy⟩).map g
  surj := by
    intro z
    obtain ⟨z, rfl⟩ := hg z
    obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj M z
    refine ⟨⟨f r, _, s.1, s.2, rfl⟩, ?_⟩
    simpa only [map_mul, ← RingHom.comp_apply, H] using DFunLike.congr_arg g e
  exists_of_eq := by
    intro x y e
    obtain ⟨x, rfl⟩ := hf x
    obtain ⟨y, rfl⟩ := hf y
    rw [← sub_eq_zero, ← map_sub, ← map_sub, ← RingHom.comp_apply, ← H, RingHom.comp_apply,
      ← IsLocalization.mk'_one (M := M)] at e
    obtain ⟨r, hr, hr'⟩ := (IsLocalization.mk'_mem_map_algebraMap_iff M _ _ _ _).mp (H' e)
    exact ⟨⟨_, r, hr, rfl⟩, by simpa [sub_eq_zero, mul_sub] using hr'⟩
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Ideal R) :
    IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map (algebraMap R S)) :=
  of_surjective M S (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (I.map (algebraMap R S))) Ideal.Quotient.mk_surjective rfl (by simp)

open Algebra in
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Ideal R} [P.IsPrime] [IsDomain R] [IsDomain S] [FaithfulSMul R S] :
    IsDomain (Localization (algebraMapSubmonoid S P.primeCompl)) :=
  isDomain_localization (map_le_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective R S) P.primeCompl_le_nonZeroDivisors)

end CommRing

end IsLocalization

