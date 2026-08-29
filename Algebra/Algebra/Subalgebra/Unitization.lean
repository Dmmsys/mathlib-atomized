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

/--
theorem `lift_range_le` / 定理 `lift_range_le`

English:
theorem lift_range_le
  given: {f : A ->ₙₐ[R] C} {S : Subalgebra R C}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

中文:
定理 lift_range_le
  条件: {f : A ->ₙₐ[R] C} {S : 子代数 R C}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

Depends on / 依赖: add_mem, algebraMap_mem
-/
theorem lift_range_le {f : A ->ₙₐ[R] C} {S : Subalgebra R C} :
    (lift f).range <= S ↔ NonUnitalAlgHom.range f <= S.toNonUnitalSubalgebra := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

/--
theorem `lift_range` / 定理 `lift_range`

English:
theorem lift_range
  given: (f : A ->ₙₐ[R] C)
  proof: eq_of_forall_ge_iff fun c => by rw [lift_range_le, Algebra.adjoin_le_iff]; rfl

中文:
定理 lift_range
  条件: (f : A ->ₙₐ[R] C)
  证明: eq_of_forall_ge_iff fun c => by rw [lift_range_le, Algebra.adjoin_le_iff]; rfl

Depends on / 依赖: Algebra, Algebra.adjoin_le_iff, adjoin_le_iff, eq_of_forall_ge_iff, lift_range_le
-/
theorem lift_range (f : A ->ₙₐ[R] C) :
    (lift f).range = Algebra.adjoin R (NonUnitalAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c => by rw [lift_range_le, Algebra.adjoin_le_iff]; rfl

end Unitization

namespace NonUnitalSubalgebra

section Semiring

variable {R S A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [SetLike S A]
  [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A] (s : S)

/--
Definition of `unitization` / `unitization` 的定义

English:
definition unitization
  signature: : Unitization R s ->ₐ[R] A
  body: Unitization.lift (NonUnitalSubalgebraClass.subtype s)

@[simp]

中文:
定义 unitization
  签名: : Unitization R s ->ₐ[R] A
  定义体: Unitization.lift (NonUnitalSubalgebraClass.subtype s)

@[simp]

Depends on / 依赖: NonUnitalSubalgebraClass, NonUnitalSubalgebraClass.subtype, Unitization, Unitization.lift, subtype
-/
def unitization : Unitization R s ->ₐ[R] A :=
  Unitization.lift (NonUnitalSubalgebraClass.subtype s)

@[simp]
/--
theorem `unitization_apply` / 定理 `unitization_apply`

English:
theorem unitization_apply
  given: (x : Unitization R s)
  proof: rfl

中文:
定理 unitization_apply
  条件: (x : Unitization R s)
  证明: rfl
-/
theorem unitization_apply (x : Unitization R s) :
    unitization s x = algebraMap R A x.fst + x.snd :=
  rfl

/--
theorem `unitization_range` / 定理 `unitization_range`

English:
theorem unitization_range
  statement: (unitization s).range = Algebra.adjoin R (s : Set A)
  proof: by
  rw [unitization]; rw [Unitization.lift_range]
  simp

中文:
定理 unitization_range
  结论: (unitization s).range = 代数.adjoin R (s : 集合 A)
  证明: by
  rw [unitization]; rw [Unitization.lift_range]
  simp

Depends on / 依赖: Unitization, Unitization.lift_range, lift_range, unitization
-/
theorem unitization_range : (unitization s).range = Algebra.adjoin R (s : Set A) := by
  rw [unitization]; rw [Unitization.lift_range]
  simp

end Semiring

/--
theorem `_root_.AlgHomClass.unitization_injective'` / 定理 `_root_.AlgHomClass.unitization_injective'`

English:
theorem _root_.AlgHomClass.unitization_injective'
  statement: {F R S A : Type*} [CommRing R] [Ring A]
  proof: by
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

中文:
定理 _root_.代数态射类.unitization_injective'
  结论: {F R S A : 类型} [交换环 R] [环 A]
  证明: by
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

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, Unitization, Unitization.algebraMap_eq_inl, a.property, add_eq_zero_iff_eq_neg, algebraMap_eq_inl, commutes, injective_iff_map_eq_zero, inl_add_inr, map_add, neg_mem, property, simp_rw
-/
theorem _root_.AlgHomClass.unitization_injective' {F R S A : Type*} [CommRing R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h : forall r, r != 0 -> algebraMap R A r ∉ s)
    [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : forall x : s, f x = x) : Function.Injective f := by
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

/--
theorem `_root_.AlgHomClass.unitization_injective` / 定理 `_root_.AlgHomClass.unitization_injective`

English:
theorem _root_.AlgHomClass.unitization_injective
  statement: {F R S A : Type*} [Field R] [Ring A]
  proof: by
  refine AlgHomClass.unitization_injective' s (fun r hr hr' => ?_) f hf
  rw [Algebra.algebraMap_eq_smul_one] at hr'
exact h1 inv_smul_smul₀ hr (1 : A) ▸ SMulMemClass.smul_mem r⁻¹ hr'

中文:
定理 _root_.代数态射类.unitization_injective
  结论: {F R S A : 类型} [域 R] [环 A]
  证明: by
  refine AlgHomClass.unitization_injective' s (fun r hr hr' => ?_) f hf
  rw [Algebra.algebraMap_eq_smul_one] at hr'
exact h1 inv_smul_smul₀ hr (1 : A) ▸ SMulMemClass.smul_mem r⁻¹ hr'

Depends on / 依赖: AlgHomClass, AlgHomClass.unitization_injective, Algebra, Algebra.algebraMap_eq_smul_one, SMulMemClass, SMulMemClass.smul_mem, algebraMap_eq_smul_one, smul_mem, unitization_injective
-/
theorem _root_.AlgHomClass.unitization_injective {F R S A : Type*} [Field R] [Ring A]
    [Algebra R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
    (s : S) (h1 : 1 ∉ s) [FunLike F (Unitization R s) A] [AlgHomClass F R (Unitization R s) A]
    (f : F) (hf : forall x : s, f x = x) : Function.Injective f := by
  refine AlgHomClass.unitization_injective' s (fun r hr hr' => ?_) f hf
  rw [Algebra.algebraMap_eq_smul_one] at hr'
exact h1 inv_smul_smul₀ hr (1 : A) ▸ SMulMemClass.smul_mem r⁻¹ hr'

section Field

variable {R S A : Type*} [Field R] [Ring A] [Algebra R A]
  [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A] (s : S)

/--
theorem `unitization_injective` / 定理 `unitization_injective`

English:
theorem unitization_injective
  given: (h1 : (1 : A) ∉ s)
  statement: Function.Injective (unitization s)
  proof: AlgHomClass.unitization_injective s h1 (unitization s) fun _ => by simp

中文:
定理 unitization_injective
  条件: (h1 : (1 : A) ∉ s)
  结论: 函数.单射 (unitization s)
  证明: AlgHomClass.unitization_injective s h1 (unitization s) fun _ => by simp

Depends on / 依赖: AlgHomClass, AlgHomClass.unitization_injective, unitization, unitization_injective
-/
theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization s) :=
  AlgHomClass.unitization_injective s h1 (unitization s) fun _ => by simp

/-- If a `NonUnitalSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `Algebra.adjoin`. -/
@[simps! apply_coe]
/--
Definition of `unitizationAlgEquiv` / `unitizationAlgEquiv` 的定义

English:
definition unitizationAlgEquiv
  signature: (h1 : (1 : A) ∉ s)
  body: let algHom : Unitization R s ->ₐ[R] Algebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
fun x => (unitization_range s).le AlgHom.mem_range_self _ x)
AlgEquiv.ofBijective algHom by
    refine ⟨?_, fun x => ?_⟩
    · have := AlgHomClass.unitization_injective s h1
        ((Subalgebra.val _).comp algHom) fun _ => by simp [algHom]
      rw [AlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) in (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

中文:
定义 unitizationAlgEquiv
  签名: (h1 : (1 : A) ∉ s)
  定义体: let algHom : Unitization R s ->ₐ[R] Algebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
fun x => (unitization_range s).le AlgHom.mem_range_self _ x)
AlgEquiv.ofBijective algHom by
    refine ⟨?_, fun x => ?_⟩
    · have := AlgHomClass.unitization_injective s h1
        ((Subalgebra.val _).comp algHom) fun _ => by simp [algHom]
      rw [AlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) in (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AlgHom, AlgHom.coe_comp, AlgHom.mem_range_self, AlgHomClass, AlgHomClass.unitization_injective, Algebra, Algebra.adjoin, Subalgebra, Subalgebra.val, Subtype, Subtype.ext, Unitization, adjoin, algHom, codRestrict, coe_comp, mem_range_self, ofBijective
-/
noncomputable def unitizationAlgEquiv (h1 : (1 : A) ∉ s) :
    Unitization R s ≃ₐ[R] Algebra.adjoin R (s : Set A) :=
  let algHom : Unitization R s ->ₐ[R] Algebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
fun x => (unitization_range s).le AlgHom.mem_range_self _ x)
AlgEquiv.ofBijective algHom by
    refine ⟨?_, fun x => ?_⟩
    · have := AlgHomClass.unitization_injective s h1
        ((Subalgebra.val _).comp algHom) fun _ => by simp [algHom]
      rw [AlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) in (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Field

end NonUnitalSubalgebra

/-! ## Subsemirings -/

namespace NonUnitalSubsemiring

variable {R S : Type*} [Semiring R] [SetLike S R] [hSR : NonUnitalSubsemiringClass S R] (s : S)

/--
Definition of `unitization` / `unitization` 的定义

English:
definition unitization
  signature: : Unitization Nat s ->ₐ[Nat] R
  body: NonUnitalSubalgebra.unitization (hSRA := AddSubmonoidClass.nsmulMemClass) s

@[simp]

中文:
定义 unitization
  签名: : Unitization 自然数 s ->ₐ[自然数] R
  定义体: NonUnitalSubalgebra.unitization (hSRA := AddSubmonoidClass.nsmulMemClass) s

@[simp]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.nsmulMemClass, NonUnitalSubalgebra, NonUnitalSubalgebra.unitization, nsmulMemClass, unitization
-/
def unitization : Unitization Nat s ->ₐ[Nat] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubmonoidClass.nsmulMemClass) s

@[simp]
/--
theorem `unitization_apply` / 定理 `unitization_apply`

English:
theorem unitization_apply
  given: (x : Unitization Nat s)
  statement: unitization s x = x.fst + x.snd
  proof: rfl

中文:
定理 unitization_apply
  条件: (x : Unitization 自然数 s)
  结论: unitization s x = x.fst + x.snd
  证明: rfl
-/
theorem unitization_apply (x : Unitization Nat s) : unitization s x = x.fst + x.snd :=
  rfl

/--
theorem `unitization_range` / 定理 `unitization_range`

English:
theorem unitization_range
  proof: by
  have := AddSubmonoidClass.nsmulMemClass (S := S)
  rw [unitization]; rw [NonUnitalSubalgebra.unitization_range (hSRA := this)]; rw [Algebra.adjoin_nat]

中文:
定理 unitization_range
  证明: by
  have := AddSubmonoidClass.nsmulMemClass (S := S)
  rw [unitization]; rw [NonUnitalSubalgebra.unitization_range (hSRA := this)]; rw [Algebra.adjoin_nat]

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.nsmulMemClass, Algebra, Algebra.adjoin_nat, NonUnitalSubalgebra, NonUnitalSubalgebra.unitization_range, adjoin_nat, nsmulMemClass, unitization, unitization_range
-/
theorem unitization_range :
    (unitization s).range = subalgebraOfSubsemiring (.closure s) := by
  have := AddSubmonoidClass.nsmulMemClass (S := S)
  rw [unitization]; rw [NonUnitalSubalgebra.unitization_range (hSRA := this)]; rw [Algebra.adjoin_nat]

end NonUnitalSubsemiring

/-! ## Subrings -/

namespace NonUnitalSubring

variable {R S : Type*} [Ring R] [SetLike S R] [hSR : NonUnitalSubringClass S R] (s : S)

/--
Definition of `unitization` / `unitization` 的定义

English:
definition unitization
  signature: : Unitization Int s ->ₐ[Int] R
  body: NonUnitalSubalgebra.unitization (hSRA := AddSubgroupClass.zsmulMemClass) s

@[simp]

中文:
定义 unitization
  签名: : Unitization 整数 s ->ₐ[整数] R
  定义体: NonUnitalSubalgebra.unitization (hSRA := AddSubgroupClass.zsmulMemClass) s

@[simp]

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.zsmulMemClass, NonUnitalSubalgebra, NonUnitalSubalgebra.unitization, unitization, zsmulMemClass
-/
def unitization : Unitization Int s ->ₐ[Int] R :=
  NonUnitalSubalgebra.unitization (hSRA := AddSubgroupClass.zsmulMemClass) s

@[simp]
/--
theorem `unitization_apply` / 定理 `unitization_apply`

English:
theorem unitization_apply
  given: (x : Unitization Int s)
  statement: unitization s x = x.fst + x.snd
  proof: rfl

中文:
定理 unitization_apply
  条件: (x : Unitization 整数 s)
  结论: unitization s x = x.fst + x.snd
  证明: rfl
-/
theorem unitization_apply (x : Unitization Int s) : unitization s x = x.fst + x.snd :=
  rfl

/--
theorem `unitization_range` / 定理 `unitization_range`

English:
theorem unitization_range
  proof: by
  have := AddSubgroupClass.zsmulMemClass (S := S)
  rw [unitization]; rw [NonUnitalSubalgebra.unitization_range (hSRA := this)]; rw [Algebra.adjoin_int]

中文:
定理 unitization_range
  证明: by
  have := AddSubgroupClass.zsmulMemClass (S := S)
  rw [unitization]; rw [NonUnitalSubalgebra.unitization_range (hSRA := this)]; rw [Algebra.adjoin_int]

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.zsmulMemClass, Algebra, Algebra.adjoin_int, NonUnitalSubalgebra, NonUnitalSubalgebra.unitization_range, adjoin_int, unitization, unitization_range, zsmulMemClass
-/
theorem unitization_range :
    (unitization s).range = subalgebraOfSubring (.closure s) := by
  have := AddSubgroupClass.zsmulMemClass (S := S)
  rw [unitization]; rw [NonUnitalSubalgebra.unitization_range (hSRA := this)]; rw [Algebra.adjoin_int]

end NonUnitalSubring

/-! ## Star subalgebras -/

namespace Unitization

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing R] [StarRing A]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]
variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

/--
theorem `starLift_range_le` / 定理 `starLift_range_le`

English:
theorem starLift_range_le
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

中文:
定理 starLift_range_le
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

Depends on / 依赖: add_mem, algebraMap_mem
-/
theorem starLift_range_le
    {f : A ->⋆ₙₐ[R] C} {S : StarSubalgebra R C} :
    (starLift f).range <= S ↔ NonUnitalStarAlgHom.range f <= S.toNonUnitalStarSubalgebra := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using! add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

/--
theorem `starLift_range` / 定理 `starLift_range`

English:
theorem starLift_range
  given: (f : A ->⋆ₙₐ[R] C)
  proof: eq_of_forall_ge_iff fun c => by
    rw [starLift_range_le]; rw [StarAlgebra.adjoin_le_iff]
    rfl

中文:
定理 starLift_range
  条件: (f : A ->⋆ₙₐ[R] C)
  证明: eq_of_forall_ge_iff fun c => by
    rw [starLift_range_le]; rw [StarAlgebra.adjoin_le_iff]
    rfl

Depends on / 依赖: StarAlgebra, StarAlgebra.adjoin_le_iff, adjoin_le_iff, eq_of_forall_ge_iff, starLift_range_le
-/
theorem starLift_range (f : A ->⋆ₙₐ[R] C) :
    (starLift f).range = StarAlgebra.adjoin R (NonUnitalStarAlgHom.range f : Set C) :=
  eq_of_forall_ge_iff fun c => by
    rw [starLift_range_le]; rw [StarAlgebra.adjoin_le_iff]
    rfl

end Unitization

namespace NonUnitalStarSubalgebra

section Semiring

variable {R S A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)
/--
Definition of `unitization` / `unitization` 的定义

English:
definition unitization
  signature: : Unitization R s ->⋆ₐ[R] A
  body: Unitization.starLift NonUnitalStarSubalgebraClass.subtype s

@[simp]

中文:
定义 unitization
  签名: : Unitization R s ->⋆ₐ[R] A
  定义体: Unitization.starLift NonUnitalStarSubalgebraClass.subtype s

@[simp]

Depends on / 依赖: NonUnitalStarSubalgebraClass, NonUnitalStarSubalgebraClass.subtype, Unitization, Unitization.starLift, starLift, subtype
-/
def unitization : Unitization R s ->⋆ₐ[R] A :=
Unitization.starLift NonUnitalStarSubalgebraClass.subtype s

@[simp]
/--
theorem `unitization_apply` / 定理 `unitization_apply`

English:
theorem unitization_apply
  given: (x : Unitization R s)
  statement: unitization s x = algebraMap R A x.fst + x.snd
  proof: rfl

中文:
定理 unitization_apply
  条件: (x : Unitization R s)
  结论: unitization s x = algebraMap R A x.fst + x.snd
  证明: rfl
-/
theorem unitization_apply (x : Unitization R s) : unitization s x = algebraMap R A x.fst + x.snd :=
  rfl

/--
theorem `unitization_range` / 定理 `unitization_range`

English:
theorem unitization_range
  statement: (unitization s).range = StarAlgebra.adjoin R s
  proof: by
  rw [unitization]; rw [Unitization.starLift_range]
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coe_subtype,
    Subtype.range_coe_subtype]
  rfl

中文:
定理 unitization_range
  结论: (unitization s).range = 对合代数.adjoin R s
  证明: by
  rw [unitization]; rw [Unitization.starLift_range]
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coe_subtype,
    Subtype.range_coe_subtype]
  rfl

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass, NonUnitalStarSubalgebraClass.coe_subtype, Subtype, Subtype.range_coe_subtype, Unitization, Unitization.starLift_range, coe_range, coe_subtype, range_coe_subtype, starLift_range, unitization
-/
theorem unitization_range : (unitization s).range = StarAlgebra.adjoin R s := by
  rw [unitization]; rw [Unitization.starLift_range]
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coe_subtype,
    Subtype.range_coe_subtype]
  rfl

end Semiring

section Field

variable {R S A : Type*} [Field R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)

/--
theorem `unitization_injective` / 定理 `unitization_injective`

English:
theorem unitization_injective
  given: (h1 : (1 : A) ∉ s)
  statement: Function.Injective (unitization s)
  proof: AlgHomClass.unitization_injective s h1 (unitization s) fun _ => by simp

中文:
定理 unitization_injective
  条件: (h1 : (1 : A) ∉ s)
  结论: 函数.单射 (unitization s)
  证明: AlgHomClass.unitization_injective s h1 (unitization s) fun _ => by simp

Depends on / 依赖: AlgHomClass, AlgHomClass.unitization_injective, unitization, unitization_injective
-/
theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (unitization s) :=
  AlgHomClass.unitization_injective s h1 (unitization s) fun _ => by simp

/-- If a `NonUnitalStarSubalgebra` over a field does not contain `1`, then its unitization is
isomorphic to its `StarAlgebra.adjoin`. -/
@[simps! apply_coe]
/--
Definition of `unitizationStarAlgEquiv` / `unitizationStarAlgEquiv` 的定义

English:
definition unitizationStarAlgEquiv
  signature: (h1 : (1 : A) ∉ s)
  body: let starAlgHom : Unitization R s ->⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
fun x => (unitization_range s).le Set.mem_range_self x)
StarAlgEquiv.ofBijective starAlgHom by
    refine ⟨?_, fun x => ?_⟩
    · have := AlgHomClass.unitization_injective s h1 ((StarSubalgebra.subtype _).comp starAlgHom)
        fun _ => by simp [starAlgHom]
      rw [StarAlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) in (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

中文:
定义 unitizationStarAlgEquiv
  签名: (h1 : (1 : A) ∉ s)
  定义体: let starAlgHom : Unitization R s ->⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
fun x => (unitization_range s).le Set.mem_range_self x)
StarAlgEquiv.ofBijective starAlgHom by
    refine ⟨?_, fun x => ?_⟩
    · have := AlgHomClass.unitization_injective s h1 ((StarSubalgebra.subtype _).comp starAlgHom)
        fun _ => by simp [starAlgHom]
      rw [StarAlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) in (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

Depends on / 依赖: AlgHomClass, AlgHomClass.unitization_injective, Set.mem_range_self, StarAlgEquiv, StarAlgEquiv.ofBijective, StarAlgHom, StarAlgHom.coe_comp, StarAlgebra, StarAlgebra.adjoin, StarSubalgebra, StarSubalgebra.subtype, Unitization, adjoin, codRestrict, coe_comp, mem_range_self, ofBijective, of_comp, property, starAlgHom
-/
noncomputable def unitizationStarAlgEquiv (h1 : (1 : A) ∉ s) :
    Unitization R s ≃⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
  let starAlgHom : Unitization R s ->⋆ₐ[R] StarAlgebra.adjoin R (s : Set A) :=
    ((unitization s).codRestrict _
fun x => (unitization_range s).le Set.mem_range_self x)
StarAlgEquiv.ofBijective starAlgHom by
    refine ⟨?_, fun x => ?_⟩
    · have := AlgHomClass.unitization_injective s h1 ((StarSubalgebra.subtype _).comp starAlgHom)
        fun _ => by simp [starAlgHom]
      rw [StarAlgHom.coe_comp] at this
      exact this.of_comp
    · obtain (⟨a, ha⟩ : (x : A) in (unitization s).range) :=
        (unitization_range s).ge x.property
      exact ⟨a, Subtype.ext ha⟩

end Field

end NonUnitalStarSubalgebra
