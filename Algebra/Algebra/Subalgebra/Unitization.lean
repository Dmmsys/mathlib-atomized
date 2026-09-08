/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Relating unital and non-unital substructures

This file relates various algebraic structures and provides maps (generally algebra homomorphisms),
from the unitization of a non-unital subobject into the full structure. The range of this map is
the unital closure of the non-unital subobject (e.g., `Algebra.adjoin`, `Subring.closure`,
`Subsemiring.closure` or `StarAlgebra.adjoin`). When the underlying scalar ring is a field, for
this map to be injective it suffices that the range omits `1`. In this setting we provide suitable
`AlgEquiv` (or `StarAlgEquiv`) onto the range.

## Main declarations

* `NonUnitalSubalgebra.unitization s : Unitization R s →ₐ[R] A`:
  where `s` is a non-unital subalgebra of a unital `R`-algebra `A`, this is the natural algebra
  homomorphism sending `(r, a)` to `r • 1 + a`. The range of this map is
  `Algebra.adjoin R (s : Set A)`.
* `NonUnitalSubalgebra.unitizationAlgEquiv s : Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A)`
  when `R` is a field and `1 ∉ s`. This is `NonUnitalSubalgebra.unitization` upgraded to an
  `AlgEquiv` onto its range.
* `NonUnitalSubsemiring.unitization : Unitization ℕ s →ₐ[ℕ] R`: the natural `ℕ`-algebra homomorphism
  from the unitization of a non-unital subsemiring `s` into the ring containing it. The range of
  this map is `subalgebraOfSubsemiring (Subsemiring.closure s)`.
  This is just `NonUnitalSubalgebra.unitization s` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalSubring.unitization : Unitization ℤ s →ₐ[ℤ] R`:
  the natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring `s` into the
  ring containing it. The range of this map is `subalgebraOfSubring (Subring.closure s)`.
  This is just `NonUnitalSubalgebra.unitization s` but we provide a separate declaration because
  there is an instance Lean can't find on its own due to `outParam`.
* `NonUnitalStarSubalgebra s : Unitization R s →⋆ₐ[R] A`: a version of
  `NonUnitalSubalgebra.unitization` for star algebras.
* `NonUnitalStarSubalgebra.unitizationStarAlgEquiv s :`
  `Unitization R s ≃⋆ₐ[R] StarAlgebra.adjoin R (s : Set A)`:
  a version of `NonUnitalSubalgebra.unitizationAlgEquiv` for star algebras.
-/

@[expose] public section

/-! ## Subalgebras -/

namespace Unitization

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [Semiring C] [Algebra R C]

/-
**Unitization.lift_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：lift_range_le {f : A ->ₙₐ[R] C} {S : Subalgebra R C} : (lift f).range <= S
 ↔ NonUnitalAlgHom.range f <= S.toNonUnitalSubalgebra
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Unitization.lift_apply`：∀ {R : Type u_2} {A : Type u_3} [inst : CommSemi
ring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A]   [inst_3 : 
SMulCommClas…
· 使用定理 `NonUnitalAlgHom.toAlgHom_apply`：∀ {R : Type u_2} {A : Type u_3} [inst : 
CommSemiring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A]   [i
nst_3 : SMulCommClas…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Unitization.ind`：ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitiz
ation R A -> Prop} (inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitiz
ation…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
-/
theorem lift_range_le {f : A →ₙₐ[R] C} {S : Subalgebra R C} :
    (lift f).range ≤ S ↔ NonUnitalAlgHom.range f ≤ S.toNonUnitalSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)
/-
**Unitization.lift_range** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：lift_range (f : A ->ₙₐ[R] C) : (lift f).range = Algebra.adjoin R (NonUnita
lAlgHom.range f : Set C)
参数：f : A ->ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.lift_range_le`：lift_range_le {f : A ->ₙₐ[R] C} {S : Subalgeb
ra R C} : (lift f).range <= S ↔ NonUnitalAlgHom.range f <= S.toNonUnitalSubalgeb
ra
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_range (f : A →ₙₐ[R] C) :
    (lift f).range = Algebra.adjoin R (NonUnitalAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c ↦ by rw [lift_range_le, Algebra.adjoin_le_iff]; rfl

end Unitization

namespace NonUnitalSubalgebra

section Semiring

variable {R S A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)

/-- The natural `R`-algebra homomorphism from the unitization of a non-unital subalgebra into
the algebra containing it. -/
/-
**NonUnitalSubalgebra.unitization** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubalgebra
`。
形式化陈述：unitization : Unitization R s ->ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `R`-algebra homomorphism from the unitization of a non-unital subalg
ebra into
the algebra containing it.
-/
def unitization : Unitization R s →ₐ[R] A :=
  Unitization.lift (NonUnitalSubalgebraClass.subtype s)

@[simp]
/-
**NonUnitalSubalgebra.unitization_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSuba
lgebra`。
形式化陈述：unitization_apply (x : Unitization R s) : unitization s x = algebraMap R A
 x.fst + x.snd
参数：x : Unitization R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem unitization_apply (x : Unitization R s) :
    unitization s x = algebraMap R A x.fst + x.snd :=
  rfl
/-
**NonUnitalSubalgebra.unitization_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSuba
lgebra`。
形式化陈述：unitization_range : (unitization s).range = Algebra.adjoin R (s : Set A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubalgebra.unitization.eq_1`：∀ {R : Type u_1} {S : Type u_2} {A
 : Type u_3} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A
]   [inst_3 : SetLike S A]…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `Unitization.lift_range`：lift_range (f : A ->ₙₐ[R] C) : (lift f).range = 
Algebra.adjoin R (NonUnitalAlgHom.range f : Set C)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalAlgHom.coe_range`：coe_range (φ : F) : ((NonUnitalAlgHom.range φ
 : NonUnitalSubalgebra R B) : Set B) = Set.range (φ : A -> B)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unitization_range : (unitization s).range = Algebra.adjoin R (s : Set A) := by
  rw [unitization, Unitization.lift_range]
  simp

end Semiring

/-- A sufficient condition for injectivity of `NonUnitalSubalgebra.unitization` when the scalars
are a commutative ring. When the scalars are a field, one should use the more natural
`NonUnitalStarSubalgebra.unitization_injective` whose hypothesis is easier to verify. -/
/-
**NonUnitalSubalgebra._root_.AlgHomClass.unitization_injective'** 是 Mathlib 中的一个
定理，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sufficient condition for injectivity of `NonUnitalSubalgebra.unitization` when
 the scalars
are a commutative ring. When the scalars are a field, one should use the more na
tural
`NonUnitalStarSubalgebra.unitization_injective` whose hypothesis is easier to ve
rify.
-/
theorem _root_.AlgHomClass.unitization_injective' {F R S A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h : ∀ r, r ≠ 0 → algebraMap R A r ∉ s)
    [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx => ?_
  induction x with
  | inl_add_inr r a =>
    simp_rw [map_add, hf, ← Unitization.algebraMap_eq_inl, AlgHomClass.commutes] at hx
    rw [add_eq_zero_iff_eq_neg] at hx ⊢
    by_cases hr : r = 0
    · ext
      · simp [hr]
      · simpa [hr] using hx
    · exact (h r hr <| hx ▸ (neg_mem a.property)).elim

/-- This is a generic version which allows us to prove both
`NonUnitalSubalgebra.unitization_injective` and `NonUnitalStarSubalgebra.unitization_injective`. -/
/-
**NonUnitalSubalgebra._root_.AlgHomClass.unitization_injective** 是 Mathlib 中的一个定
理，位于命名空间 `NonUnitalSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a generic version which allows us to prove both
`NonUnitalSubalgebra.unitization_injective` and `NonUnitalStarSubalgebra.unitiza
tion_injective`.
-/
theorem _root_.AlgHomClass.unitization_injective {F R S A : Type*} [Field R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h1 : 1 ∉ s) [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : ∀ x : s, f x = x) : Function.Injective f := by
  refine AlgHomClass.unitization_injective' s (fun r hr hr' ↦ ?_) f hf
  rw [Algebra.algebraMap_eq_smul_one] at hr'
  exact h1 <| inv_smul_smul₀ hr (1 : A) ▸ SMulMemClass.smul_mem r⁻¹ hr'

section Field

variable {R S A : Type*} [Field R] [Ring A] [Algebra R A]
  [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A] (s : S)

/-
**NonUnitalSubalgebra.unitization_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
Subalgebra`。
形式化陈述：unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization
 s)
参数：h1 : (1 : A) ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.unitization_injective`：∀ {F : Type u_1} {R : Type u_2} {S : 
Type u_3} {A : Type u_4} [inst : Field R] [inst_1 : Ring A] [inst_2 : Algebra R 
A]   [inst_3 : SetLike …
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization s) :=
  AlgHomClass.unitization_injective s h1 (unitization s) fun _ ↦ by simp

/-- If a `NonUnitalSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `Algebra.adjoin`. -/
@[simps! apply_coe]
/-
**NonUnitalSubalgebra.unitizationAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSu
balgebra`。
形式化陈述：unitizationAlgEquiv (h1 : (1 : A) ∉ s) : Unitization R s ≃ₐ[R] Algebra.adj
oin R (s : Set A)
参数：h1 : (1 : A) ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `NonUnitalSubalgebra` over a field does not contain `1`, then its unitizati
on is
isomorphic to its `Algebra.adjoin`.
-/
noncomputable def unitizationAlgEquiv (h1 : (1 : A) ∉ s) :
    Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A) :=
  let algHom : Unitization R s →ₐ[R] Algebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
      fun x ↦ (unitization_range s).le <| AlgHom.mem_range_self _ x)
  AlgEquiv.ofBijective algHom <| by
    refine ⟨?_, fun x ↦ ?_⟩
    · have := AlgHomClass.unitization_injective s h1
        ((Subalgebra.val _).comp algHom) fun _ ↦ by simp [algHom]
      rw [AlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) ∈ (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Field

end NonUnitalSubalgebra

/-! ## Subsemirings -/

namespace NonUnitalSubsemiring

variable {R S : Type*} [Semiring R] [SetLike S R] [hSR : NonUnitalSubsemiringClass S R] (s : S)

/-- The natural `ℕ`-algebra homomorphism from the unitization of a non-unital subsemiring to
its `Subsemiring.closure`. -/
/-
**NonUnitalSubsemiring.unitization** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubsemiri
ng`。
形式化陈述：unitization : Unitization Nat s ->ₐ[Nat] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `ℕ`-algebra homomorphism from the unitization of a non-unital subsem
iring to
its `Subsemiring.closure`.
-/
def unitization : Unitization ℕ s →ₐ[ℕ] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubmonoidClass.nsmulMemClass) s

@[simp]
/-
**NonUnitalSubsemiring.unitization_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
semiring`。
形式化陈述：unitization_apply (x : Unitization Nat s) : unitization s x = x.fst + x.sn
d
参数：x : Unitization Nat s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitization_apply (x : Unitization ℕ s) : unitization s x = x.fst + x.snd :=
  rfl
/-
**NonUnitalSubsemiring.unitization_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSub
semiring`。
形式化陈述：unitization_range : (unitization s).range = subalgebraOfSubsemiring (.clos
ure s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddSubmonoidClass.nsmulMemClass`：AddSubmonoidClass.nsmulMemClass {S M : 
Type*} [AddMonoid M] [SetLike S M] [AddSubmonoidClass S M] : SMulMemClass S Nat 
M where smul_mem n _x…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubsemiring.unitization.eq_1`：∀ {R : Type u_1} {S : Type u_2} [
inst : Semiring R] [inst_1 : SetLike S R] [hSR : NonUnitalSubsemiringClass S R] 
  (s : S), NonUnitalSubsemi…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalSubalgebra.unitization_range`：unitization_range : (unitization 
s).range = Algebra.adjoin R (s : Set A)
· 使用定理 `Algebra.adjoin_nat`：Algebra.adjoin_nat {R : Type*} [Semiring R] (s : Set
 R) : adjoin Nat s = subalgebraOfSubsemiring (Subsemiring.closure s)
-/
theorem unitization_range :
    (unitization s).range = subalgebraOfSubsemiring (.closure s) := by
  have := AddSubmonoidClass.nsmulMemClass (S := S)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_nat]

end NonUnitalSubsemiring

/-! ## Subrings -/

namespace NonUnitalSubring

variable {R S : Type*} [Ring R] [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

/-- The natural `ℤ`-algebra homomorphism from the unitization of a non-unital subring to
its `Subring.closure`. -/
/-
**NonUnitalSubring.unitization** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalSubring`。
形式化陈述：unitization : Unitization Int s ->ₐ[Int] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `ℤ`-algebra homomorphism from the unitization of a non-unital subrin
g to
its `Subring.closure`.
-/
def unitization : Unitization ℤ s →ₐ[ℤ] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubgroupClass.zsmulMemClass) s

@[simp]
/-
**NonUnitalSubring.unitization_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：unitization_apply (x : Unitization Int s) : unitization s x = x.fst + x.sn
d
参数：x : Unitization Int s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
-/
theorem unitization_apply (x : Unitization ℤ s) : unitization s x = x.fst + x.snd :=
  rfl
/-
**NonUnitalSubring.unitization_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnitalSubring
`。
形式化陈述：unitization_range : (unitization s).range = subalgebraOfSubring (.closure 
s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddSubgroupClass.zsmulMemClass`：AddSubgroupClass.zsmulMemClass {S M : Ty
pe*} [SubNegMonoid M] [SetLike S M] [AddSubgroupClass S M] : SMulMemClass S Int 
M where smul_mem n _…
· 使用定理 `NonUnitalSubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [i
nst : SetLike S R] [inst_1 : NonUnitalNonAssocRing R] [h : NonUnitalSubringClass
 S R],   AddSubgroupClass S …
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalSubring.unitization.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst
 : Ring R] [inst_1 : SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S),   N
onUnitalSubring.unitiza…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalSubalgebra.unitization_range`：unitization_range : (unitization 
s).range = Algebra.adjoin R (s : Set A)
· 使用定理 `Algebra.adjoin_int`：Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) 
: adjoin Int s = subalgebraOfSubring (Subring.closure s)
-/
theorem unitization_range :
    (unitization s).range = subalgebraOfSubring (.closure s) := by
  have := AddSubgroupClass.zsmulMemClass (S := S)
  rw [unitization, NonUnitalSubalgebra.unitization_range (hSRA := this), Algebra.adjoin_int]

end NonUnitalSubring

/-! ## Star subalgebras -/

namespace Unitization

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing R] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]
variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

/-
**Unitization.starLift_range_le** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：starLift_range_le {f : A ->⋆ₙₐ[R] C} {S : StarSubalgebra R C} : (starLift 
f).range <= S ↔ NonUnitalStarAlgHom.range f <= S.toNonUnitalStarSubalgebra
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Unitization.starLift_apply`：∀ {R : Type u_1} {A : Type u_2} {C : Type u_
3} [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : NonUnitalSemiring A
] [inst_3 : Star…
· 使用定理 `NonUnitalAlgHom.toAlgHom_apply`：∀ {R : Type u_2} {A : Type u_3} [inst : 
CommSemiring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A]   [i
nst_3 : SMulCommClas…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Unitization.ind`：ind {R A} [AddZeroClass R] [AddZeroClass A] {P : Unitiz
ation R A -> Prop} (inl_add_inr : forall (r : R) (a : A), P (inl r + (a : Unitiz
ation…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
-/
theorem starLift_range_le
    {f : A →⋆ₙₐ[R] C} {S : StarSubalgebra R C} :
    (starLift f).range ≤ S ↔ NonUnitalStarAlgHom.range f ≤ S.toNonUnitalStarSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)
/-
**Unitization.starLift_range** 是 Mathlib 中的一个定理，位于命名空间 `Unitization`。
形式化陈述：starLift_range (f : A ->⋆ₙₐ[R] C) : (starLift f).range = StarAlgebra.adjoi
n R (NonUnitalStarAlgHom.range f : Set C)
参数：f : A ->⋆ₙₐ[R] C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.starLift_range_le`：starLift_range_le {f : A ->⋆ₙₐ[R] C} {S :
 StarSubalgebra R C} : (starLift f).range <= S ↔ NonUnitalStarAlgHom.range f <= 
S.toNonUnitalStarSu…
· 使用定理 `StarAlgebra.adjoin_le_iff`：adjoin_le_iff {S : StarSubalgebra R A} {s : S
et A} : adjoin R s <= S ↔ s subseteq S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem starLift_range (f : A →⋆ₙₐ[R] C) :
    (starLift f).range = StarAlgebra.adjoin R (NonUnitalStarAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c ↦ by
    rw [starLift_range_le, StarAlgebra.adjoin_le_iff]
    rfl

end Unitization

namespace NonUnitalStarSubalgebra

section Semiring

variable {R S A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)
/-- The natural star `R`-algebra homomorphism from the unitization of a non-unital star subalgebra
to its `StarAlgebra.adjoin`. -/
/-
**NonUnitalStarSubalgebra.unitization** 是 Mathlib 中的一个定义，位于命名空间 `NonUnitalStarSu
balgebra`。
形式化陈述：unitization : Unitization R s ->⋆ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural star `R`-algebra homomorphism from the unitization of a non-unital s
tar subalgebra
to its `StarAlgebra.adjoin`.
-/
def unitization : Unitization R s →⋆ₐ[R] A :=
  Unitization.starLift <| NonUnitalStarSubalgebraClass.subtype s

@[simp]
/-
**NonUnitalStarSubalgebra.unitization_apply** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
StarSubalgebra`。
形式化陈述：unitization_apply (x : Unitization R s) : unitization s x = algebraMap R A
 x.fst + x.snd
参数：x : Unitization R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem unitization_apply (x : Unitization R s) : unitization s x = algebraMap R A x.fst + x.snd :=
  rfl
/-
**NonUnitalStarSubalgebra.unitization_range** 是 Mathlib 中的一个定理，位于命名空间 `NonUnital
StarSubalgebra`。
形式化陈述：unitization_range : (unitization s).range = StarAlgebra.adjoin R s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NonUnitalStarSubalgebra.unitization.eq_1`：∀ {R : Type u_1} {S : Type u_2
} {A : Type u_3} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : Semirin
g A]   [inst_3 : StarRing A] […
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `Unitization.starLift_range`：starLift_range (f : A ->⋆ₙₐ[R] C) : (starLif
t f).range = StarAlgebra.adjoin R (NonUnitalStarAlgHom.range f : Set C)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NonUnitalStarAlgHom.coe_range`：coe_range (φ : F) : ((NonUnitalStarAlgHom
.range φ : NonUnitalStarSubalgebra R B) : Set B) = Set.range (φ : A -> B)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
-/
theorem unitization_range : (unitization s).range = StarAlgebra.adjoin R s := by
  rw [unitization, Unitization.starLift_range]
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coe_subtype,
    Subtype.range_coe_subtype]
  rfl

end Semiring

section Field

variable {R S A : Type*} [Field R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)

/-
**NonUnitalStarSubalgebra.unitization_injective** 是 Mathlib 中的一个定理，位于命名空间 `NonUn
italStarSubalgebra`。
形式化陈述：unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization
 s)
参数：h1 : (1 : A) ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.unitization_injective`：∀ {F : Type u_1} {R : Type u_2} {S : 
Type u_3} {A : Type u_4} [inst : Field R] [inst_1 : Ring A] [inst_2 : Algebra R 
A]   [inst_3 : SetLike …
· 使用定理 `NonUnitalSubringClass.toNonUnitalSubsemiringClass`：∀ {S : Type u_1} {R :
 Type u} {inst : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUn
italSubringClass S R], NonUnitalSubsemi…
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `NonUnitalSubsemiringClass.mulMemClass`：∀ (S : Type u_1) (R : Type u) [in
st : NonUnitalNonAssocSemiring R] [inst_1 : SetLike S R]   [h : NonUnitalSubsemi
ringClass S R], MulMemClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
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
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization s) :=
  AlgHomClass.unitization_injective s h1 (unitization s) fun _ ↦ by simp

/-- If a `NonUnitalStarSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `StarAlgebra.adjoin`. -/
@[simps! apply_coe]
/-
**NonUnitalStarSubalgebra.unitizationStarAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Non
UnitalStarSubalgebra`。
形式化陈述：unitizationStarAlgEquiv (h1 : (1 : A) ∉ s) : Unitization R s ≃⋆ₐ[R] StarAl
gebra.adjoin R (s : Set A)
参数：h1 : (1 : A) ∉ s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `NonUnitalStarSubalgebra` over a field does not contain `1`, then its uniti
zation is
isomorphic to its `StarAlgebra.adjoin`.
-/
noncomputable def unitizationStarAlgEquiv (h1 : (1 : A) ∉ s) :
    Unitization R s ≃⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
  let starAlgHom : Unitization R s →⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
      fun x ↦ (unitization_range s).le <| Set.mem_range_self x)
  StarAlgEquiv.ofBijective starAlgHom <| by
    refine ⟨?_, fun x ↦ ?_⟩
    · have := AlgHomClass.unitization_injective s h1 ((StarSubalgebra.subtype _).comp starAlgHom)
        fun _ ↦ by simp [starAlgHom]
      rw [StarAlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) ∈ (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Field

end NonUnitalStarSubalgebra

