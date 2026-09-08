/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Class group map induced by an extension of domains

For an injective extension `A → B` of commutative domains (equivalently `Module.IsTorsionFree A B`),
we construct the group homomorphism `ClassGroup.extendedHom : ClassGroup A →* ClassGroup B` given by
pushing fractional ideals forward along the algebra map.

## Main definitions

- `ClassGroup.extendedHom A B`: the induced map between the class groups.
- `ClassGroup.extendedIdeal A B`: the extension of a nonzero integral ideal.

## Main results

- `ClassGroup.extendedHom_mk`: compatibility with representatives as fractional ideals.
- `ClassGroup.extendedHom_mk0`: compatibility with representatives as nonzero integral ideals.
- `ClassGroup.extendedHom_comp`: compatibility of extension in a tower `A → B → C`.
- `ClassGroup.extendedHom_eq_one_of_forall_isPrincipal`: if the extension of every ideal is
  principal, then `ClassGroup.extendedHom A B` is trivial.
-/

public section

open scoped nonZeroDivisors

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.IsTorsionFree A B]

namespace ClassGroup

section CommRing

variable [IsDomain A] [IsDomain B]

/-- The monoid homomorphism `ClassGroup A → ClassGroup B` induced by an
injective extension of domains `A → B`. -/
/-
**ClassGroup.extendedHom** 是 Mathlib 中的一个定义，位于命名空间 `ClassGroup`。
形式化陈述：extendedHom : ClassGroup A ->* ClassGroup B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid homomorphism `ClassGroup A → ClassGroup B` induced by an
injective extension of domains `A → B`.
-/
noncomputable def extendedHom : ClassGroup A →* ClassGroup B :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map (j := algebraMap A B)
        (FaithfulSMul.algebraMap_injective _ _) (α : FractionRing A))
        (by simp [α.ne_zero]), ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0] using!
        (FractionalIdeal.extendedHom_spanSingleton (FractionRing B) B _).symm)

@[simp]
/-
**ClassGroup.extendedHom_quotientMk** 是 Mathlib 中的一个引理，位于命名空间 `ClassGroup`。
形式化陈述：extendedHom_quotientMk (α : (FractionalIdeal A⁰ (FractionRing A))ˣ) : exte
ndedHom A B (QuotientGroup.mk α) = QuotientGroup.mk (Units.map (FractionalIdeal.
extendedHom (FractionRing B) B).toMonoidHom α)
参数：α : (FractionalIdeal A⁰ (FractionRing A))ˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendedHom_quotientMk (α : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (QuotientGroup.mk α) = QuotientGroup.mk
      (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom α) := by
  rfl

@[simp]
/-
**ClassGroup.extendedHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：extendedHom_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) : extendedHom 
A B (ClassGroup.mk _ I) = ClassGroup.mk _ (Units.map (FractionalIdeal.extendedHo
m (FractionRing B) B).toMonoidHom I)
参数：I : (FractionalIdeal A⁰ (FractionRing A))ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ClassGroup.Quot_mk_eq_mk`：ClassGroup.Quot_mk_eq_mk (I : (FractionalIdeal
 R⁰ (FractionRing R))ˣ) : Quot.mk _ I = ClassGroup.mk (FractionRing R) I
· 使用引理 `ClassGroup.extendedHom_quotientMk`：extendedHom_quotientMk (α : (Fraction
alIdeal A⁰ (FractionRing A))ˣ) : extendedHom A B (QuotientGroup.mk α) = Quotient
Group.mk (Units.map (Fr…
-/
theorem extendedHom_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (ClassGroup.mk _ I) = ClassGroup.mk _
        (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom I) := by
  rw [← ClassGroup.Quot_mk_eq_mk, ← ClassGroup.Quot_mk_eq_mk]
  exact extendedHom_quotientMk A B I

/-- The extension of a nonzero integral ideal along an injective extension of domains. -/
/-
**ClassGroup.extendedIdeal** 是 Mathlib 中的一个缩写定义，位于命名空间 `ClassGroup`。
形式化陈述：extendedIdeal (I : (Ideal A)⁰) : (Ideal B)⁰
参数：I : (Ideal A)⁰。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of a nonzero integral ideal along an injective extension of domain
s.
-/
abbrev extendedIdeal (I : (Ideal A)⁰) : (Ideal B)⁰ :=
  ⟨I.1.map (algebraMap A B), mem_nonZeroDivisors_iff_ne_zero.mpr <|
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩

@[simp]
/-
**ClassGroup.extendedIdeal_extendedIdeal** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：extendedIdeal_extendedIdeal (C : Type*) [CommRing C] [IsDomain C] [Algebra
 B C] [Algebra A C] [IsScalarTower A B C] [Module.IsTorsionFree B C] [Module.IsT
orsionFree A C] (I : (Ideal A)⁰) : extendedIdeal B C (extendedIdeal A B I) = ext
endedIdeal A C I
参数：C : Type*；I : (Ideal A)⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extendedIdeal_extendedIdeal (C : Type*) [CommRing C] [IsDomain C] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Module.IsTorsionFree B C]
    [Module.IsTorsionFree A C] (I : (Ideal A)⁰) :
    extendedIdeal B C (extendedIdeal A B I) = extendedIdeal A C I := by
  simp [Ideal.map_map, IsScalarTower.algebraMap_eq A B C]

end CommRing

section DedekindDomain

variable [IsDedekindDomain A] (C : Type*) [CommRing C] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
  [IsDedekindDomain C]

/-
**ClassGroup.extendedHom_mk0'** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：extendedHom_mk0' [IsDomain B] (I : (Ideal A)⁰) : extendedHom A B (ClassGro
up.mk0 I) = ClassGroup.mk _ (Units.map (FractionalIdeal.extendedHom (FractionRin
g B) B).toMonoidHom (FractionalIdeal.mk0 (FractionRing A) I))
参数：I : (Ideal A)⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ClassGroup.mk_mk0`：ClassGroup.mk_mk0 [IsDedekindDomain R] (I : (Ideal R)
⁰) : ClassGroup.mk K (FractionalIdeal.mk0 K I) = ClassGroup.mk0 I
· 使用定理 `ClassGroup.extendedHom_mk`：extendedHom_mk (I : (FractionalIdeal A⁰ (Frac
tionRing A))ˣ) : extendedHom A B (ClassGroup.mk _ I) = ClassGroup.mk _ (Units.ma
p (FractionalId…
-/
theorem extendedHom_mk0' [IsDomain B] (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) =
      ClassGroup.mk _ (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom
      (FractionalIdeal.mk0 (FractionRing A) I)) := by
  rw [← ClassGroup.mk_mk0 (FractionRing A), extendedHom_mk]

variable [IsDedekindDomain B]
/-
**ClassGroup.extendedHom_mk0** 是 Mathlib 中的一个引理，位于命名空间 `ClassGroup`。
形式化陈述：extendedHom_mk0 (I : (Ideal A)⁰) : extendedHom A B (ClassGroup.mk0 I) = Cl
assGroup.mk0 (extendedIdeal A B I)
参数：I : (Ideal A)⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClassGroup.mk0_eq_quotientMk`：ClassGroup.mk0_eq_quotientMk [IsDedekindDo
main R] (I : (Ideal R)⁰) : (ClassGroup.mk0 I : ClassGroup R) = QuotientGroup.mk 
(FractionalIdeal.m…
· 使用引理 `ClassGroup.extendedHom_quotientMk`：extendedHom_quotientMk (α : (Fraction
alIdeal A⁰ (FractionRing A))ˣ) : extendedHom A B (QuotientGroup.mk α) = Quotient
Group.mk (Units.map (Fr…
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `FractionalIdeal.extendedHom_coeIdeal_eq_map`：extendedHom_coeIdeal_eq_map
 (I : Ideal A) : (I : FractionalIdeal A⁰ K).extendedHom L B = (I.map (algebraMap
 A B) : FractionalIdeal B⁰ L)
-/
lemma extendedHom_mk0 (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) = ClassGroup.mk0 (extendedIdeal A B I) := by
  rw [mk0_eq_quotientMk, mk0_eq_quotientMk, extendedHom_quotientMk]
  congr; ext : 1
  exact FractionalIdeal.extendedHom_coeIdeal_eq_map (L := FractionRing B) (B := B) _


@[simp]
/-
**ClassGroup.extendedHom_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：extendedHom_comp_apply (x : ClassGroup A) : extendedHom B C (extendedHom A
 B x) = extendedHom A C x
参数：x : ClassGroup A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `ClassGroup.mk0_surjective`：ClassGroup.mk0_surjective [IsDedekindDomain R
] : Function.Surjective (ClassGroup.mk0 : (Ideal R)⁰ -> ClassGroup R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ClassGroup.extendedHom_mk0`：extendedHom_mk0 (I : (Ideal A)⁰) : extendedH
om A B (ClassGroup.mk0 I) = ClassGroup.mk0 (extendedIdeal A B I)
· 使用定理 `ClassGroup.extendedIdeal_extendedIdeal`：extendedIdeal_extendedIdeal (C :
 Type*) [CommRing C] [IsDomain C] [Algebra B C] [Algebra A C] [IsScalarTower A B
 C] [Module.IsTorsionFree B …
-/
theorem extendedHom_comp_apply (x : ClassGroup A) :
      extendedHom B C (extendedHom A B x) = extendedHom A C x := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0 A B I, extendedHom_mk0 B C (extendedIdeal A B I),
    extendedHom_mk0 A C I, extendedIdeal_extendedIdeal]
/-
**ClassGroup.extendedHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `ClassGroup`。
形式化陈述：extendedHom_comp : (extendedHom B C).comp (extendedHom A B) = extendedHom 
A C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `ClassGroup.extendedHom_comp_apply`：extendedHom_comp_apply (x : ClassGrou
p A) : extendedHom B C (extendedHom A B x) = extendedHom A C x
-/
theorem extendedHom_comp : (extendedHom B C).comp (extendedHom A B) = extendedHom A C := by
  ext x
  exact extendedHom_comp_apply A B C x
/-
**ClassGroup.extendedHom_eq_one_of_forall_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 
`ClassGroup`。
形式化陈述：extendedHom_eq_one_of_forall_isPrincipal (h : forall I : (Ideal A), (I.map
 (algebraMap A B)).IsPrincipal) : extendedHom A B = 1
参数：h : forall I : (Ideal A), (I.map (algebraMap A B)).IsPrincipal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `ClassGroup.mk0_surjective`：ClassGroup.mk0_surjective [IsDedekindDomain R
] : Function.Surjective (ClassGroup.mk0 : (Ideal R)⁰ -> ClassGroup R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ClassGroup.extendedHom_mk0`：extendedHom_mk0 (I : (Ideal A)⁰) : extendedH
om A B (ClassGroup.mk0 I) = ClassGroup.mk0 (extendedIdeal A B I)
· 使用定理 `MonoidHom.one_apply`：MonoidHom.one_apply [MulOne M] [MulOneClass N] (x :
 M) : (1 : M ->* N) x = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ClassGroup.mk0_eq_one_iff`：ClassGroup.mk0_eq_one_iff [IsDedekindDomain R
] {I : Ideal R} (hI : I in (Ideal R)⁰) : ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ I.IsPrinci
pal
-/
theorem extendedHom_eq_one_of_forall_isPrincipal
    (h : ∀ I : (Ideal A), (I.map (algebraMap A B)).IsPrincipal) : extendedHom A B = 1 := by
  ext x
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0, MonoidHom.one_apply]
  exact (ClassGroup.mk0_eq_one_iff (extendedIdeal A B I).2).mpr (by simpa using h I)

end DedekindDomain

end ClassGroup

end

