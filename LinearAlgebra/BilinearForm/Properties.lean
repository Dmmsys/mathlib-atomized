/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Bilinear form

This file defines various properties of bilinear forms, including reflexivity, symmetry,
alternativity, adjoint, and non-degeneracy.
For orthogonality, see `Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean`.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

@[expose] public section


open LinearMap (BilinForm)
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-! ### Reflexivity, symmetry, and alternativity -/


/--
Definition of `IsRefl` / `IsRefl` 的定义

English:
definition IsRefl
  signature: (B : BilinForm R M)
  body: LinearMap.IsRefl B

中文:
定义 IsRefl
  签名: (B : BilinForm R M)
  定义体: LinearMap.IsRefl B

Depends on / 依赖: IsRefl, LinearMap, LinearMap.IsRefl
-/
def IsRefl (B : BilinForm R M) : Prop := LinearMap.IsRefl B

namespace IsRefl

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  given: (H : B.IsRefl)
  statement: forall {x y : M}, B x y = 0 -> B y x = 0
  proof: fun {x y} => H x y

中文:
定理 eq_zero
  条件: (H : B.IsRefl)
  结论: 对任意 {x y : M}, B x y = 0 -> B y x = 0
  证明: fun {x y} => H x y
-/
theorem eq_zero (H : B.IsRefl) : forall {x y : M}, B x y = 0 -> B y x = 0 := fun {x y} => H x y

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: {B : BilinForm R₁ M₁} (hB : B.IsRefl)
  statement: (-B).IsRefl
  proof: fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp

中文:
定理 neg
  条件: {B : BilinForm R₁ M₁} (hB : B.IsRefl)
  结论: (-B).IsRefl
  证明: fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp
-/
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {α : Type*} [Semiring α] [IsDomain α] [Module α R] [SMulCommClass R α R]
  proof: fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)

中文:
定理 smul
  结论: {α : 类型} [Semiring α] [IsDomain α] [Module α R] [SMulCommClass R α R]
  证明: fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)
-/
protected theorem smul {α : Type*} [Semiring α] [IsDomain α] [Module α R] [SMulCommClass R α R]
    [IsTorsionFree α R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) :
    (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)

/--
theorem `groupSMul` / 定理 `groupSMul`

English:
theorem groupSMul
  statement: {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
  proof: fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp

中文:
定理 groupSMul
  结论: {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
  证明: fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp
-/
protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp

end IsRefl

@[simp]
/--
theorem `isRefl_zero` / 定理 `isRefl_zero`

English:
theorem isRefl_zero
  statement: (0 : BilinForm R M).IsRefl
  proof: fun _ _ _ => rfl

@[simp]

中文:
定理 isRefl_zero
  结论: (0 : BilinForm R M).IsRefl
  证明: fun _ _ _ => rfl

@[simp]
-/
theorem isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl

@[simp]
/--
theorem `isRefl_neg` / 定理 `isRefl_neg`

English:
theorem isRefl_neg
  given: {B : BilinForm R₁ M₁}
  statement: (-B).IsRefl ↔ B.IsRefl
  proof: ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩

中文:
定理 isRefl_neg
  条件: {B : BilinForm R₁ M₁}
  结论: (-B).IsRefl ↔ B.IsRefl
  证明: ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩

Depends on / 依赖: IsRefl, IsRefl.neg, h.neg, neg_neg
-/
theorem isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩

/--
Definition of `IsSymm` / `IsSymm` 的定义

English:
structure IsSymm
  parameters: (B : BilinForm R M)
  axioms and operations (1):
    - eq : forall x y, B x y = B y x

中文:
结构 IsSymm
  参数: (B : BilinForm R M)
  公理与运算 (1 个):
    - eq : 对任意 x y, B x y = B y x
-/
structure IsSymm (B : BilinForm R M) : Prop where
  protected eq : forall x y, B x y = B y x

/--
theorem `isSymm_def` / 定理 `isSymm_def`

English:
theorem isSymm_def
  statement: IsSymm B ↔ forall x y, B x y = B y x where
  proof: fun ⟨h⟩ => h
  mpr h := ⟨h⟩

中文:
定理 isSymm_def
  结论: IsSymm B ↔ 对任意 x y, B x y = B y x where
  证明: fun ⟨h⟩ => h
  mpr h := ⟨h⟩
-/
theorem isSymm_def : IsSymm B ↔ forall x y, B x y = B y x where
  mp := fun ⟨h⟩ => h
  mpr h := ⟨h⟩

/--
theorem `isSymm_iff` / 定理 `isSymm_iff`

English:
theorem isSymm_iff
  statement: IsSymm B ↔ LinearMap.IsSymm B
  proof: by
  simp [isSymm_def, LinearMap.isSymm_def]

中文:
定理 isSymm_iff
  结论: IsSymm B ↔ LinearMap.IsSymm B
  证明: by
  simp [isSymm_def, LinearMap.isSymm_def]

Depends on / 依赖: LinearMap, LinearMap.isSymm_def, isSymm_def
-/
theorem isSymm_iff : IsSymm B ↔ LinearMap.IsSymm B := by
  simp [isSymm_def, LinearMap.isSymm_def]

namespace IsSymm

/--
theorem `isRefl` / 定理 `isRefl`

English:
theorem isRefl
  given: (H : B.IsSymm)
  statement: B.IsRefl
  proof: fun x y H1 => H.eq x y ▸ H1

中文:
定理 isRefl
  条件: (H : B.IsSymm)
  结论: B.IsRefl
  证明: fun x y H1 => H.eq x y ▸ H1

Depends on / 依赖: H.eq
-/
theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 => H.eq x y ▸ H1

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm)
  proof: ⟨fun x y => (congr_arg₂ (· + ·) (hB₁.eq x y) (hB₂.eq x y) :)⟩

中文:
定理 add
  条件: {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm)
  证明: ⟨fun x y => (congr_arg₂ (· + ·) (hB₁.eq x y) (hB₂.eq x y) :)⟩
-/
protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ + B₂).IsSymm := ⟨fun x y => (congr_arg₂ (· + ·) (hB₁.eq x y) (hB₂.eq x y) :)⟩

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm)
  proof: ⟨fun x y => (congr_arg₂ Sub.sub (hB₁.eq x y) (hB₂.eq x y) :)⟩

中文:
定理 sub
  条件: {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm)
  证明: ⟨fun x y => (congr_arg₂ Sub.sub (hB₁.eq x y) (hB₂.eq x y) :)⟩
-/
protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ - B₂).IsSymm := ⟨fun x y => (congr_arg₂ Sub.sub (hB₁.eq x y) (hB₂.eq x y) :)⟩

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: {B : BilinForm R₁ M₁} (hB : B.IsSymm)
  statement: (-B).IsSymm
  proof: ⟨fun x y =>
  congr_arg Neg.neg (hB.eq x y)⟩

中文:
定理 neg
  条件: {B : BilinForm R₁ M₁} (hB : B.IsSymm)
  结论: (-B).IsSymm
  证明: ⟨fun x y =>
  congr_arg Neg.neg (hB.eq x y)⟩
-/
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) : (-B).IsSymm := ⟨fun x y =>
  congr_arg Neg.neg (hB.eq x y)⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
  proof: ⟨fun x y =>
  congr_arg (a • ·) (hB.eq x y)⟩

中文:
定理 smul
  结论: {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
  证明: ⟨fun x y =>
  congr_arg (a • ·) (hB.eq x y)⟩
-/
protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := ⟨fun x y =>
  congr_arg (a • ·) (hB.eq x y)⟩

/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M)
  proof: ⟨fun x y => b.eq x y⟩

中文:
定理 restrict
  条件: {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M)
  证明: ⟨fun x y => b.eq x y⟩

Depends on / 依赖: b.eq
-/
theorem restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := ⟨fun x y => b.eq x y⟩

end IsSymm

@[simp]
/--
theorem `isSymm_zero` / 定理 `isSymm_zero`

English:
theorem isSymm_zero
  statement: (0 : BilinForm R M).IsSymm
  proof: ⟨fun _ _ => rfl⟩

@[simp]

中文:
定理 isSymm_zero
  结论: (0 : BilinForm R M).IsSymm
  证明: ⟨fun _ _ => rfl⟩

@[simp]
-/
theorem isSymm_zero : (0 : BilinForm R M).IsSymm := ⟨fun _ _ => rfl⟩

@[simp]
/--
theorem `isSymm_neg` / 定理 `isSymm_neg`

English:
theorem isSymm_neg
  given: {B : BilinForm R₁ M₁}
  statement: (-B).IsSymm ↔ B.IsSymm
  proof: ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩

中文:
定理 isSymm_neg
  条件: {B : BilinForm R₁ M₁}
  结论: (-B).IsSymm ↔ B.IsSymm
  证明: ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩

Depends on / 依赖: IsSymm, IsSymm.neg, h.neg, neg_neg
-/
theorem isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩

/--
theorem `isSymm_iff_flip` / 定理 `isSymm_iff_flip`

English:
theorem isSymm_iff_flip
  statement: B.IsSymm ↔ flipHom B = B where
  proof: fun ⟨h⟩ => by ext; simp [h]
  mpr h := ⟨fun x y => by rw [← flip_apply, h]⟩

中文:
定理 isSymm_iff_flip
  结论: B.IsSymm ↔ flipHom B = B where
  证明: fun ⟨h⟩ => by ext; simp [h]
  mpr h := ⟨fun x y => by rw [← flip_apply, h]⟩
-/
theorem isSymm_iff_flip : B.IsSymm ↔ flipHom B = B where
  mp := fun ⟨h⟩ => by ext; simp [h]
  mpr h := ⟨fun x y => by rw [← flip_apply, h]⟩

section polarization

variable {R : Type*} [Field R] [NeZero (2 : R)] [Module R M] {B C : BilinForm R M}

/--
lemma `IsSymm.polarization` / 引理 `IsSymm.polarization`

English:
lemma IsSymm.polarization
  given: (x y : M) (hB : B.IsSymm)
  proof: by
  simp only [map_add, LinearMap.add_apply]
  rw [hB.eq y x]
  ring_nf
  rw [mul_assoc]; rw [inv_mul_cancel₀ two_ne_zero]; rw [mul_one]

中文:
引理 IsSymm.polarization
  条件: (x y : M) (hB : B.IsSymm)
  证明: by
  simp only [map_add, LinearMap.add_apply]
  rw [hB.eq y x]
  ring_nf
  rw [mul_assoc]; rw [inv_mul_cancel₀ two_ne_zero]; rw [mul_one]

Depends on / 依赖: LinearMap, LinearMap.add_apply, add_apply, hB.eq, map_add, mul_assoc, mul_one, ring_nf, two_ne_zero
-/
lemma IsSymm.polarization (x y : M) (hB : B.IsSymm) :
    B x y = (B (x + y) (x + y) - B x x - B y y) / 2 := by
  simp only [map_add, LinearMap.add_apply]
  rw [hB.eq y x]
  ring_nf
  rw [mul_assoc]; rw [inv_mul_cancel₀ two_ne_zero]; rw [mul_one]

/--
lemma `ext_of_isSymm` / 引理 `ext_of_isSymm`

English:
lemma ext_of_isSymm
  statement: (hB : IsSymm B) (hC : IsSymm C)
  proof: by
  ext x y
  rw [hB.polarization]; rw [hC.polarization]
  simp_rw [h]

中文:
引理 ext_of_isSymm
  结论: (hB : IsSymm B) (hC : IsSymm C)
  证明: by
  ext x y
  rw [hB.polarization]; rw [hC.polarization]
  simp_rw [h]

Depends on / 依赖: hB.polarization, hC.polarization, polarization, simp_rw
-/
lemma ext_of_isSymm (hB : IsSymm B) (hC : IsSymm C)
    (h : forall x, B x x = C x x) : B = C := by
  ext x y
  rw [hB.polarization]; rw [hC.polarization]
  simp_rw [h]

/--
lemma `ext_iff_of_isSymm` / 引理 `ext_iff_of_isSymm`

English:
lemma ext_iff_of_isSymm
  given: (hB : IsSymm B) (hC : IsSymm C)
  proof: by simp [h]
  mpr := ext_of_isSymm hB hC

中文:
引理 ext_iff_of_isSymm
  条件: (hB : IsSymm B) (hC : IsSymm C)
  证明: by simp [h]
  mpr := ext_of_isSymm hB hC

Depends on / 依赖: ext_of_isSymm
-/
lemma ext_iff_of_isSymm (hB : IsSymm B) (hC : IsSymm C) :
    B = C ↔ forall x, B x x = C x x where
  mp h := by simp [h]
  mpr := ext_of_isSymm hB hC

end polarization

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSymm_iff_basis` / 引理 `isSymm_iff_basis`

English:
lemma isSymm_iff_basis
  given: {ι : Type*} (b : Basis ι R M)
  proof: fun ⟨h⟩ i j => h _ _
  mpr := by
    refine fun h => ⟨fun x y => ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x in Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : 

中文:
引理 isSymm_iff_basis
  条件: {ι : 类型} (b : Basis ι R M)
  证明: fun ⟨h⟩ i j => h _ _
  mpr := by
    refine fun h => ⟨fun x y => ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x in Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : 
-/
lemma isSymm_iff_basis {ι : Type*} (b : Basis ι R M) :
    IsSymm B ↔ forall i j, B (b i) (b j) = B (b j) (b i) where
  mp := fun ⟨h⟩ i j => h _ _
  mpr := by
    refine fun h => ⟨fun x y => ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x in Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y in Submodule.span R (Set.range b))
    rw [← hx]; rw [← hy]
    simp only [map_sum, map_smul, coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ => Finset.sum_congr rfl fun b₂ h₂ => ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

/-! ### Positive semidefinite bilinear forms -/

section PositiveSemidefinite

/--
Definition of `IsNonneg` / `IsNonneg` 的定义

English:
structure IsNonneg
  parameters: [LE R] (B : BilinForm R M)
  axioms and operations (1):
    - nonneg : forall x, 0 <= B x x

中文:
结构 IsNonneg
  参数: [LE R] (B : BilinForm R M)
  公理与运算 (1 个):
    - nonneg : 对任意 x, 0 <= B x x
-/
structure IsNonneg [LE R] (B : BilinForm R M) where
  nonneg : forall x, 0 <= B x x

/--
lemma `isNonneg_def` / 引理 `isNonneg_def`

English:
lemma isNonneg_def
  given: [LE R] {B : BilinForm R M}
  statement: B.IsNonneg ↔ forall x, 0 <= B x x
  proof: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

中文:
引理 isNonneg_def
  条件: [LE R] {B : BilinForm R M}
  结论: B.IsNonneg ↔ 对任意 x, 0 <= B x x
  证明: ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩
-/
lemma isNonneg_def [LE R] {B : BilinForm R M} : B.IsNonneg ↔ forall x, 0 <= B x x :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/--
lemma `isNonneg_iff` / 引理 `isNonneg_iff`

English:
lemma isNonneg_iff
  given: [LE R] {B : BilinForm R M}
  statement: B.IsNonneg ↔ LinearMap.IsNonneg B
  proof: isNonneg_def.trans LinearMap.isNonneg_def.symm

@[simp]

中文:
引理 isNonneg_iff
  条件: [LE R] {B : BilinForm R M}
  结论: B.IsNonneg ↔ LinearMap.IsNonneg B
  证明: isNonneg_def.trans LinearMap.isNonneg_def.symm

@[simp]

Depends on / 依赖: LinearMap, LinearMap.isNonneg_def.symm, isNonneg_def, isNonneg_def.trans
-/
lemma isNonneg_iff [LE R] {B : BilinForm R M} : B.IsNonneg ↔ LinearMap.IsNonneg B :=
  isNonneg_def.trans LinearMap.isNonneg_def.symm

@[simp]
/--
lemma `isNonneg_zero` / 引理 `isNonneg_zero`

English:
lemma isNonneg_zero
  given: [Preorder R]
  statement: IsNonneg (0 : BilinForm R M)
  proof: isNonneg_iff.2 LinearMap.isNonneg_zero

中文:
引理 isNonneg_zero
  条件: [Preorder R]
  结论: IsNonneg (0 : BilinForm R M)
  证明: isNonneg_iff.2 LinearMap.isNonneg_zero

Depends on / 依赖: LinearMap, LinearMap.isNonneg_zero, isNonneg_iff, isNonneg_zero
-/
lemma isNonneg_zero [Preorder R] : IsNonneg (0 : BilinForm R M) :=
  isNonneg_iff.2 LinearMap.isNonneg_zero

/--
lemma `IsNonneg.add` / 引理 `IsNonneg.add`

English:
lemma IsNonneg.add
  statement: [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
  proof: add_nonneg (hB.nonneg x) (hC.nonneg x)

中文:
引理 IsNonneg.add
  结论: [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
  证明: add_nonneg (hB.nonneg x) (hC.nonneg x)
-/
protected lemma IsNonneg.add [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
    (hB : B.IsNonneg) (hC : C.IsNonneg) : (B + C).IsNonneg where
  nonneg x := add_nonneg (hB.nonneg x) (hC.nonneg x)

/--
lemma `IsNonneg.smul` / 引理 `IsNonneg.smul`

English:
lemma IsNonneg.smul
  statement: [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
  proof: mul_nonneg hc (hB.nonneg x)

中文:
引理 IsNonneg.smul
  结论: [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
  证明: mul_nonneg hc (hB.nonneg x)
-/
protected lemma IsNonneg.smul [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
    (hB : B.IsNonneg) (hc : 0 <= c) : (c • B).IsNonneg where
  nonneg x := mul_nonneg hc (hB.nonneg x)

/--
Definition of `IsPosSemidef` / `IsPosSemidef` 的定义

English:
structure IsPosSemidef
  parameters: [LE R] (B : BilinForm R M)
  (no additional axioms)

中文:
结构 IsPosSemidef
  参数: [LE R] (B : BilinForm R M)
  (无附加公理)
-/
structure IsPosSemidef [LE R] (B : BilinForm R M) extends
  isSymm : B.IsSymm,
  isNonneg : B.IsNonneg

variable {B : BilinForm R M}

/--
lemma `isPosSemidef_def` / 引理 `isPosSemidef_def`

English:
lemma isPosSemidef_def
  given: [LE R]
  statement: B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg
  proof: ⟨fun h => ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

中文:
引理 isPosSemidef_def
  条件: [LE R]
  结论: B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg
  证明: ⟨fun h => ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

Depends on / 依赖: h.isNonneg, h.isSymm, isNonneg, isSymm
-/
lemma isPosSemidef_def [LE R] : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg :=
  ⟨fun h => ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

/--
lemma `isPosSemidef_iff` / 引理 `isPosSemidef_iff`

English:
lemma isPosSemidef_iff
  given: [LE R] {B : BilinForm R M}
  statement: B.IsPosSemidef ↔ LinearMap.IsPosSemidef B
  proof: isPosSemidef_def.trans (isSymm_iff.and isNonneg_iff).trans LinearMap.isPosSemidef_def.symm

@[simp]

中文:
引理 isPosSemidef_iff
  条件: [LE R] {B : BilinForm R M}
  结论: B.IsPosSemidef ↔ LinearMap.IsPosSemidef B
  证明: isPosSemidef_def.trans (isSymm_iff.and isNonneg_iff).trans LinearMap.isPosSemidef_def.symm

@[simp]

Depends on / 依赖: LinearMap, LinearMap.isPosSemidef_def.symm, isNonneg_iff, isPosSemidef_def, isPosSemidef_def.trans, isSymm_iff, isSymm_iff.and
-/
lemma isPosSemidef_iff [LE R] {B : BilinForm R M} : B.IsPosSemidef ↔ LinearMap.IsPosSemidef B :=
isPosSemidef_def.trans (isSymm_iff.and isNonneg_iff).trans LinearMap.isPosSemidef_def.symm

@[simp]
/--
lemma `isPosSemidef_zero` / 引理 `isPosSemidef_zero`

English:
lemma isPosSemidef_zero
  given: [Preorder R]
  statement: IsPosSemidef (0 : BilinForm R M)
  proof: isPosSemidef_iff.2 LinearMap.isPosSemidef_zero

中文:
引理 isPosSemidef_zero
  条件: [Preorder R]
  结论: IsPosSemidef (0 : BilinForm R M)
  证明: isPosSemidef_iff.2 LinearMap.isPosSemidef_zero

Depends on / 依赖: LinearMap, LinearMap.isPosSemidef_zero, isPosSemidef_iff, isPosSemidef_zero
-/
lemma isPosSemidef_zero [Preorder R] : IsPosSemidef (0 : BilinForm R M) :=
  isPosSemidef_iff.2 LinearMap.isPosSemidef_zero

/--
lemma `IsPosSemidef.add` / 引理 `IsPosSemidef.add`

English:
lemma IsPosSemidef.add
  statement: [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
  proof: isPosSemidef_iff.2 ((isPosSemidef_iff.1 hB).add (isPosSemidef_iff.1 hC))

中文:
引理 IsPosSemidef.add
  结论: [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
  证明: isPosSemidef_iff.2 ((isPosSemidef_iff.1 hB).add (isPosSemidef_iff.1 hC))
-/
protected lemma IsPosSemidef.add [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
    (hB : B.IsPosSemidef) (hC : C.IsPosSemidef) : (B + C).IsPosSemidef :=
  isPosSemidef_iff.2 ((isPosSemidef_iff.1 hB).add (isPosSemidef_iff.1 hC))

/--
lemma `IsPosSemidef.smul` / 引理 `IsPosSemidef.smul`

English:
lemma IsPosSemidef.smul
  statement: [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
  proof: isPosSemidef_def.2 ⟨hB.isSymm.smul c, hB.isNonneg.smul hc⟩

中文:
引理 IsPosSemidef.smul
  结论: [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
  证明: isPosSemidef_def.2 ⟨hB.isSymm.smul c, hB.isNonneg.smul hc⟩
-/
protected lemma IsPosSemidef.smul [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
    (hB : B.IsPosSemidef) (hc : 0 <= c) : (c • B).IsPosSemidef :=
  isPosSemidef_def.2 ⟨hB.isSymm.smul c, hB.isNonneg.smul hc⟩

end PositiveSemidefinite

/--
Definition of `IsAlt` / `IsAlt` 的定义

English:
definition IsAlt
  signature: (B : BilinForm R M)
  body: LinearMap.IsAlt B

中文:
定义 IsAlt
  签名: (B : BilinForm R M)
  定义体: LinearMap.IsAlt B

Depends on / 依赖: LinearMap, LinearMap.IsAlt
-/
def IsAlt (B : BilinForm R M) : Prop := LinearMap.IsAlt B

namespace IsAlt

/--
theorem `self_eq_zero` / 定理 `self_eq_zero`

English:
theorem self_eq_zero
  given: (H : B.IsAlt) (x : M)
  statement: B x x = 0
  proof: LinearMap.IsAlt.self_eq_zero H x

中文:
定理 self_eq_zero
  条件: (H : B.IsAlt) (x : M)
  结论: B x x = 0
  证明: LinearMap.IsAlt.self_eq_zero H x

Depends on / 依赖: LinearMap, LinearMap.IsAlt.self_eq_zero, self_eq_zero
-/
theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 := LinearMap.IsAlt.self_eq_zero H x

/--
theorem `neg_eq` / 定理 `neg_eq`

English:
theorem neg_eq
  given: (H : B₁.IsAlt) (x y : M₁)
  statement: -B₁ x y = B₁ y x
  proof: LinearMap.IsAlt.neg H x y

中文:
定理 neg_eq
  条件: (H : B₁.IsAlt) (x y : M₁)
  结论: -B₁ x y = B₁ y x
  证明: LinearMap.IsAlt.neg H x y

Depends on / 依赖: LinearMap, LinearMap.IsAlt.neg
-/
theorem neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := LinearMap.IsAlt.neg H x y

/--
theorem `isRefl` / 定理 `isRefl`

English:
theorem isRefl
  given: (H : B₁.IsAlt)
  statement: B₁.IsRefl
  proof: LinearMap.IsAlt.isRefl H

中文:
定理 isRefl
  条件: (H : B₁.IsAlt)
  结论: B₁.IsRefl
  证明: LinearMap.IsAlt.isRefl H

Depends on / 依赖: LinearMap, LinearMap.IsAlt.isRefl, isRefl
-/
theorem isRefl (H : B₁.IsAlt) : B₁.IsRefl := LinearMap.IsAlt.isRefl H

/--
theorem `eq_of_add_add_eq_zero` / 定理 `eq_of_add_add_eq_zero`

English:
theorem eq_of_add_add_eq_zero
  given: [IsCancelAdd R] {a b c : M} (H : B.IsAlt) (hAdd : a + b + c = 0)
  proof: LinearMap.IsAlt.eq_of_add_add_eq_zero H hAdd

中文:
定理 eq_of_add_add_eq_zero
  条件: [IsCancelAdd R] {a b c : M} (H : B.IsAlt) (hAdd : a + b + c = 0)
  证明: LinearMap.IsAlt.eq_of_add_add_eq_zero H hAdd

Depends on / 依赖: LinearMap, LinearMap.IsAlt.eq_of_add_add_eq_zero, eq_of_add_add_eq_zero
-/
theorem eq_of_add_add_eq_zero [IsCancelAdd R] {a b c : M} (H : B.IsAlt) (hAdd : a + b + c = 0) :
    B a b = B b c := LinearMap.IsAlt.eq_of_add_add_eq_zero H hAdd

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt)
  statement: (B₁ + B₂).IsAlt
  proof: fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) :).trans add_zero _

中文:
定理 add
  条件: {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt)
  结论: (B₁ + B₂).IsAlt
  证明: fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) :).trans add_zero _
-/
protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) :).trans add_zero _

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt)
  proof: fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans sub_zero _

中文:
定理 sub
  条件: {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt)
  证明: fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans sub_zero _
-/
protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
(B₁ - B₂).IsAlt := fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans sub_zero _

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: {B : BilinForm R₁ M₁} (hB : B.IsAlt)
  statement: (-B).IsAlt
  proof: fun x =>
neg_eq_zero.mpr hB x

中文:
定理 neg
  条件: {B : BilinForm R₁ M₁} (hB : B.IsAlt)
  结论: (-B).IsAlt
  证明: fun x =>
neg_eq_zero.mpr hB x
-/
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt := fun x =>
neg_eq_zero.mpr hB x

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
  proof: fun x =>
(congr_arg (a • ·) (hB x)).trans smul_zero _

中文:
定理 smul
  结论: {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
  证明: fun x =>
(congr_arg (a • ·) (hB x)).trans smul_zero _
-/
protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
(congr_arg (a • ·) (hB x)).trans smul_zero _

end IsAlt

@[simp]
/--
theorem `isAlt_zero` / 定理 `isAlt_zero`

English:
theorem isAlt_zero
  statement: (0 : BilinForm R M).IsAlt
  proof: fun _ => rfl

@[simp]

中文:
定理 isAlt_zero
  结论: (0 : BilinForm R M).IsAlt
  证明: fun _ => rfl

@[simp]
-/
theorem isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl

@[simp]
/--
theorem `isAlt_neg` / 定理 `isAlt_neg`

English:
theorem isAlt_neg
  given: {B : BilinForm R₁ M₁}
  statement: (-B).IsAlt ↔ B.IsAlt
  proof: ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩

中文:
定理 isAlt_neg
  条件: {B : BilinForm R₁ M₁}
  结论: (-B).IsAlt ↔ B.IsAlt
  证明: ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩

Depends on / 依赖: IsAlt.neg, h.neg, neg_neg
-/
theorem isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩

end BilinForm

namespace BilinForm


-- Note: This originally involved only left-separating, and was changed (January 2026, PR #34110)
-- to be symmetric to match `LinearMap.Nondegenerate`. See discussion at this Zulip thread:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Nondegenerate.20bilinear.20.2F.20quadratic.20forms/with/568863325
-- TODO: Should it be removed entirely?
/--
Definition of `Nondegenerate` / `Nondegenerate` 的定义

English:
abbreviation Nondegenerate
  signature: (B : BilinForm R M)
  body: LinearMap.Nondegenerate B

中文:
缩写 Nondegenerate
  签名: (B : BilinForm R M)
  定义体: LinearMap.Nondegenerate B

Depends on / 依赖: LinearMap, LinearMap.Nondegenerate, Nondegenerate
-/
abbrev Nondegenerate (B : BilinForm R M) : Prop :=
  LinearMap.Nondegenerate B

section

variable (R M)

/--
theorem `not_nondegenerate_zero` / 定理 `not_nondegenerate_zero`

English:
theorem not_nondegenerate_zero
  given: [Nontrivial M]
  statement: ¬(0 : BilinForm R M).Nondegenerate
  proof: let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h.1 m fun _ => rfl)

中文:
定理 not_nondegenerate_zero
  条件: [Nontrivial M]
  结论: ¬(0 : BilinForm R M).Nondegenerate
  证明: let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h.1 m fun _ => rfl)

Depends on / 依赖: exists_ne
-/
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h.1 m fun _ => rfl)

end

variable {M' : Type*}
variable [AddCommMonoid M'] [Module R M']

/--
theorem `Nondegenerate.ne_zero` / 定理 `Nondegenerate.ne_zero`

English:
theorem Nondegenerate.ne_zero
  given: [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate)
  statement: B != 0
  proof: fun h0 => not_nondegenerate_zero R M h0 ▸ h

中文:
定理 Nondegenerate.ne_zero
  条件: [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate)
  结论: B != 0
  证明: fun h0 => not_nondegenerate_zero R M h0 ▸ h

Depends on / 依赖: not_nondegenerate_zero
-/
theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B != 0 :=
fun h0 => not_nondegenerate_zero R M h0 ▸ h

/--
theorem `Nondegenerate.congr` / 定理 `Nondegenerate.congr`

English:
theorem Nondegenerate.congr
  given: {B : BilinForm R M} (e : M ≃ₗ[R] M') (h : B.Nondegenerate)
  proof: ⟨h.1.congr e e, show (BilinForm.congr e (flip B)).SeparatingLeft from .congr e e h.2⟩

@[simp]

中文:
定理 Nondegenerate.congr
  条件: {B : BilinForm R M} (e : M ≃ₗ[R] M') (h : B.Nondegenerate)
  证明: ⟨h.1.congr e e, show (BilinForm.congr e (flip B)).SeparatingLeft from .congr e e h.2⟩

@[simp]

Depends on / 依赖: BilinForm, BilinForm.congr, SeparatingLeft
-/
theorem Nondegenerate.congr {B : BilinForm R M} (e : M ≃ₗ[R] M') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate :=
  ⟨h.1.congr e e, show (BilinForm.congr e (flip B)).SeparatingLeft from .congr e e h.2⟩

@[simp]
/--
theorem `nondegenerate_congr_iff` / 定理 `nondegenerate_congr_iff`

English:
theorem nondegenerate_congr_iff
  given: {B : BilinForm R M} (e : M ≃ₗ[R] M')
  proof: ⟨fun h => by
    convert! h.congr e.symm
    rw [congr_congr]; rw [e.self_trans_symm]; rw [congr_refl]; rw [LinearEquiv.refl_apply], Nondegenerate.congr e⟩

中文:
定理 nondegenerate_congr_iff
  条件: {B : BilinForm R M} (e : M ≃ₗ[R] M')
  证明: ⟨fun h => by
    convert! h.congr e.symm
    rw [congr_congr]; rw [e.self_trans_symm]; rw [congr_refl]; rw [LinearEquiv.refl_apply], Nondegenerate.congr e⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.refl_apply, Nondegenerate, Nondegenerate.congr, congr_congr, congr_refl, convert, e.self_trans_symm, e.symm, h.congr, refl_apply, self_trans_symm
-/
theorem nondegenerate_congr_iff {B : BilinForm R M} (e : M ≃ₗ[R] M') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert! h.congr e.symm
    rw [congr_congr]; rw [e.self_trans_symm]; rw [congr_refl]; rw [LinearEquiv.refl_apply], Nondegenerate.congr e⟩

/--
theorem `Nondegenerate.ker_eq_bot` / 定理 `Nondegenerate.ker_eq_bot`

English:
theorem Nondegenerate.ker_eq_bot
  given: {B : BilinForm R M} (h : B.Nondegenerate)
  proof: LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1

中文:
定理 Nondegenerate.ker_eq_bot
  条件: {B : BilinForm R M} (h : B.Nondegenerate)
  证明: LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1

Depends on / 依赖: LinearMap, LinearMap.separatingLeft_iff_ker_eq_bot.mp, separatingLeft_iff_ker_eq_bot
-/
theorem Nondegenerate.ker_eq_bot {B : BilinForm R M} (h : B.Nondegenerate) :
    LinearMap.ker B = ⊥ := LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1

/--
theorem `compLeft_injective` / 定理 `compLeft_injective`

English:
theorem compLeft_injective
  given: (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
  proof: fun φ ψ h => by
  ext w
  refine eq_of_sub_eq_zero (b.1 _ ?_)
  intro v
  rw [sub_left]; rw [← compLeft_apply]; rw [← compLeft_apply]; rw [← h]; rw [sub_self]

中文:
定理 compLeft_injective
  条件: (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
  证明: fun φ ψ h => by
  ext w
  refine eq_of_sub_eq_zero (b.1 _ ?_)
  intro v
  rw [sub_left]; rw [← compLeft_apply]; rw [← compLeft_apply]; rw [← h]; rw [sub_self]

Depends on / 依赖: compLeft_apply, eq_of_sub_eq_zero, sub_left, sub_self
-/
theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h => by
  ext w
  refine eq_of_sub_eq_zero (b.1 _ ?_)
  intro v
  rw [sub_left]; rw [← compLeft_apply]; rw [← compLeft_apply]; rw [← h]; rw [sub_self]

/--
theorem `isAdjointPair_unique_of_nondegenerate` / 定理 `isAdjointPair_unique_of_nondegenerate`

English:
theorem isAdjointPair_unique_of_nondegenerate
  statement: (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
  proof: B.compLeft_injective b ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]

中文:
定理 isAdjointPair_unique_of_nondegenerate
  结论: (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
  证明: B.compLeft_injective b ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]

Depends on / 依赖: B.compLeft_injective, compLeft_apply, compLeft_injective
-/
theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ ->ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
B.compLeft_injective b ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]

/--
lemma `Nondegenerate.flip` / 引理 `Nondegenerate.flip`

English:
lemma Nondegenerate.flip
  given: {B : BilinForm R M} (hB : B.Nondegenerate)
  proof: ⟨hB.2, hB.1⟩

中文:
引理 Nondegenerate.flip
  条件: {B : BilinForm R M} (hB : B.Nondegenerate)
  证明: ⟨hB.2, hB.1⟩
-/
lemma Nondegenerate.flip {B : BilinForm R M} (hB : B.Nondegenerate) :
    B.flip.Nondegenerate :=
  ⟨hB.2, hB.1⟩

/--
lemma `nondegenerate_flip_iff` / 引理 `nondegenerate_flip_iff`

English:
lemma nondegenerate_flip_iff
  given: {B : BilinForm R M}
  proof: ⟨Nondegenerate.flip, Nondegenerate.flip⟩

中文:
引理 nondegenerate_flip_iff
  条件: {B : BilinForm R M}
  证明: ⟨Nondegenerate.flip, Nondegenerate.flip⟩

Depends on / 依赖: Nondegenerate, Nondegenerate.flip
-/
lemma nondegenerate_flip_iff {B : BilinForm R M} :
    B.flip.Nondegenerate ↔ B.Nondegenerate := ⟨Nondegenerate.flip, Nondegenerate.flip⟩

section FiniteDimensional

variable [FiniteDimensional K V]

/--
Definition of `toDual` / `toDual` 的定义

English:
definition toDual
  signature: (B : BilinForm K V) (b : B.Nondegenerate)
  body: B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm

中文:
定义 toDual
  签名: (B : BilinForm K V) (b : B.Nondegenerate)
  定义体: B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm

Depends on / 依赖: B.linearEquivOfInjective, LinearMap, LinearMap.ker_eq_bot.mp, Subspace, Subspace.dual_finrank_eq.symm, b.ker_eq_bot, dual_finrank_eq, ker_eq_bot, linearEquivOfInjective
-/
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm

/--
theorem `toDual_def` / 定理 `toDual_def`

English:
theorem toDual_def
  given: {B : BilinForm K V} (b : B.Nondegenerate) {m n : V}
  statement: B.toDual b m n = B m n
  proof: rfl

@[simp]

中文:
定理 toDual_def
  条件: {B : BilinForm K V} (b : B.Nondegenerate) {m n : V}
  结论: B.toDual b m n = B m n
  证明: rfl

@[simp]
-/
theorem toDual_def {B : BilinForm K V} (b : B.Nondegenerate) {m n : V} : B.toDual b m n = B m n :=
  rfl

@[simp]
/--
lemma `apply_toDual_symm_apply` / 引理 `apply_toDual_symm_apply`

English:
lemma apply_toDual_symm_apply
  statement: {B : BilinForm K V} {hB : B.Nondegenerate}
  proof: by
  change B.toDual hB ((B.toDual hB).symm f) v = f v
  simp only [LinearEquiv.apply_symm_apply]

@[deprecated (since := "2026-01-17")] alias nonDegenerateFlip_iff := nondegenerate_flip_iff

中文:
引理 apply_toDual_symm_apply
  结论: {B : BilinForm K V} {hB : B.Nondegenerate}
  证明: by
  change B.toDual hB ((B.toDual hB).symm f) v = f v
  simp only [LinearEquiv.apply_symm_apply]

@[deprecated (since := "2026-01-17")] alias nonDegenerateFlip_iff := nondegenerate_flip_iff

Depends on / 依赖: B.toDual, LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, toDual
-/
lemma apply_toDual_symm_apply {B : BilinForm K V} {hB : B.Nondegenerate}
    (f : Module.Dual K V) (v : V) :
    B ((B.toDual hB).symm f) v = f v := by
  change B.toDual hB ((B.toDual hB).symm f) v = f v
  simp only [LinearEquiv.apply_symm_apply]

@[deprecated (since := "2026-01-17")] alias nonDegenerateFlip_iff := nondegenerate_flip_iff

end FiniteDimensional

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Finite ι]

/--
Definition of `dualBasis` / `dualBasis` 的定义

English:
definition dualBasis
  signature: (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V)
  body: haveI := b.finiteDimensional_of_finite
  b.dualBasis.map (B.toDual hB).symm

中文:
定义 dualBasis
  签名: (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V)
  定义体: haveI := b.finiteDimensional_of_finite
  b.dualBasis.map (B.toDual hB).symm

Depends on / 依赖: B.toDual, b.dualBasis.map, b.finiteDimensional_of_finite, dualBasis, finiteDimensional_of_finite, toDual
-/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    Basis ι K V :=
  haveI := b.finiteDimensional_of_finite
  b.dualBasis.map (B.toDual hB).symm

variable {B : BilinForm K V}

@[simp]
/--
theorem `dualBasis_repr_apply` / 定理 `dualBasis_repr_apply`

English:
theorem dualBasis_repr_apply
  given: (hB : B.Nondegenerate) (b : Basis ι K V) (x i)
  proof: by
  have := b.finiteDimensional_of_finite
  rw [dualBasis]; rw [Basis.map_repr]; rw [LinearEquiv.symm_symm]; rw [LinearEquiv.trans_apply]; rw [Basis.dualBasis_repr]; rw [toDual_def]

中文:
定理 dualBasis_repr_apply
  条件: (hB : B.Nondegenerate) (b : Basis ι K V) (x i)
  证明: by
  have := b.finiteDimensional_of_finite
  rw [dualBasis]; rw [Basis.map_repr]; rw [LinearEquiv.symm_symm]; rw [LinearEquiv.trans_apply]; rw [Basis.dualBasis_repr]; rw [toDual_def]

Depends on / 依赖: Basis.dualBasis_repr, Basis.map_repr, LinearEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply, b.finiteDimensional_of_finite, dualBasis, dualBasis_repr, finiteDimensional_of_finite, map_repr, symm_symm, toDual_def, trans_apply
-/
theorem dualBasis_repr_apply (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  have := b.finiteDimensional_of_finite
  rw [dualBasis]; rw [Basis.map_repr]; rw [LinearEquiv.symm_symm]; rw [LinearEquiv.trans_apply]; rw [Basis.dualBasis_repr]; rw [toDual_def]

/--
theorem `apply_dualBasis_left` / 定理 `apply_dualBasis_left`

English:
theorem apply_dualBasis_left
  given: (hB : B.Nondegenerate) (b : Basis ι K V) (i j)
  proof: by
  have := b.finiteDimensional_of_finite
  rw [dualBasis]; rw [Basis.map_apply]; rw [Basis.coe_dualBasis]; rw [← toDual_def hB]; rw [LinearEquiv.apply_symm_apply]; rw [Basis.coord_apply]; rw [Basis.repr_self]; rw [Finsupp.single_apply]

中文:
定理 apply_dualBasis_left
  条件: (hB : B.Nondegenerate) (b : Basis ι K V) (i j)
  证明: by
  have := b.finiteDimensional_of_finite
  rw [dualBasis]; rw [Basis.map_apply]; rw [Basis.coe_dualBasis]; rw [← toDual_def hB]; rw [LinearEquiv.apply_symm_apply]; rw [Basis.coord_apply]; rw [Basis.repr_self]; rw [Finsupp.single_apply]

Depends on / 依赖: Basis.coe_dualBasis, Basis.coord_apply, Basis.map_apply, Basis.repr_self, Finsupp, Finsupp.single_apply, LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, b.finiteDimensional_of_finite, coe_dualBasis, coord_apply, dualBasis, finiteDimensional_of_finite, map_apply, repr_self, single_apply, toDual_def
-/
theorem apply_dualBasis_left (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  have := b.finiteDimensional_of_finite
  rw [dualBasis]; rw [Basis.map_apply]; rw [Basis.coe_dualBasis]; rw [← toDual_def hB]; rw [LinearEquiv.apply_symm_apply]; rw [Basis.coord_apply]; rw [Basis.repr_self]; rw [Finsupp.single_apply]

/--
theorem `apply_dualBasis_right` / 定理 `apply_dualBasis_right`

English:
theorem apply_dualBasis_right
  statement: (hB : B.Nondegenerate) (sym : B.IsSymm)
  proof: by
  rw [sym.eq]; rw [apply_dualBasis_left]

@[simp]

中文:
定理 apply_dualBasis_right
  结论: (hB : B.Nondegenerate) (sym : B.IsSymm)
  证明: by
  rw [sym.eq]; rw [apply_dualBasis_left]

@[simp]

Depends on / 依赖: apply_dualBasis_left, sym.eq
-/
theorem apply_dualBasis_right (hB : B.Nondegenerate) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [sym.eq]; rw [apply_dualBasis_left]

@[simp]
/--
lemma `dualBasis_dualBasis_flip` / 引理 `dualBasis_dualBasis_flip`

English:
lemma dualBasis_dualBasis_flip
  given: (hB : B.Nondegenerate) (b : Basis ι K V)
  proof: by
  ext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((B.flip.dualBasis hB.flip b).ext (fun j => ?_))
  simp_rw [apply_dualBasis_left, ← B.flip_apply, apply_dualBasis_left, @eq_comm _ i j]

@[simp]

中文:
引理 dualBasis_dualBasis_flip
  条件: (hB : B.Nondegenerate) (b : Basis ι K V)
  证明: by
  ext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((B.flip.dualBasis hB.flip b).ext (fun j => ?_))
  simp_rw [apply_dualBasis_left, ← B.flip_apply, apply_dualBasis_left, @eq_comm _ i j]

@[simp]

Depends on / 依赖: B.flip.dualBasis, B.flip_apply, LinearMap, LinearMap.ker_eq_bot.mp, apply_dualBasis_left, dualBasis, eq_comm, flip_apply, hB.flip, hB.ker_eq_bot, ker_eq_bot, simp_rw
-/
lemma dualBasis_dualBasis_flip (hB : B.Nondegenerate) (b : Basis ι K V) :
    B.dualBasis hB (B.flip.dualBasis hB.flip b) = b := by
  ext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((B.flip.dualBasis hB.flip b).ext (fun j => ?_))
  simp_rw [apply_dualBasis_left, ← B.flip_apply, apply_dualBasis_left, @eq_comm _ i j]

@[simp]
/--
lemma `dualBasis_flip_dualBasis` / 引理 `dualBasis_flip_dualBasis`

English:
lemma dualBasis_flip_dualBasis
  given: (hB : B.Nondegenerate) (b : Basis ι K V)
  proof: dualBasis_dualBasis_flip hB.flip b

@[simp]

中文:
引理 dualBasis_flip_dualBasis
  条件: (hB : B.Nondegenerate) (b : Basis ι K V)
  证明: dualBasis_dualBasis_flip hB.flip b

@[simp]

Depends on / 依赖: dualBasis_dualBasis_flip, hB.flip
-/
lemma dualBasis_flip_dualBasis (hB : B.Nondegenerate) (b : Basis ι K V) :
    B.flip.dualBasis hB.flip (B.dualBasis hB b) = b :=
  dualBasis_dualBasis_flip hB.flip b

@[simp]
/--
lemma `dualBasis_dualBasis` / 引理 `dualBasis_dualBasis`

English:
lemma dualBasis_dualBasis
  statement: (hB : B.Nondegenerate) (hB' : B.IsSymm)
  proof: by
  convert! dualBasis_dualBasis_flip hB.flip b
  rwa [eq_comm, ← isSymm_iff_flip]

中文:
引理 dualBasis_dualBasis
  结论: (hB : B.Nondegenerate) (hB' : B.IsSymm)
  证明: by
  convert! dualBasis_dualBasis_flip hB.flip b
  rwa [eq_comm, ← isSymm_iff_flip]

Depends on / 依赖: convert, dualBasis_dualBasis_flip, eq_comm, hB.flip, isSymm_iff_flip
-/
lemma dualBasis_dualBasis (hB : B.Nondegenerate) (hB' : B.IsSymm)
    (b : Basis ι K V) :
    B.dualBasis hB (B.dualBasis hB b) = b := by
  convert! dualBasis_dualBasis_flip hB.flip b
  rwa [eq_comm, ← isSymm_iff_flip]

/--
lemma `dualBasis_involutive` / 引理 `dualBasis_involutive`

English:
lemma dualBasis_involutive
  given: (hB : B.Nondegenerate) (hB' : B.IsSymm)
  proof: fun b => dualBasis_dualBasis hB hB' b

中文:
引理 dualBasis_involutive
  条件: (hB : B.Nondegenerate) (hB' : B.IsSymm)
  证明: fun b => dualBasis_dualBasis hB hB' b

Depends on / 依赖: dualBasis_dualBasis
-/
lemma dualBasis_involutive (hB : B.Nondegenerate) (hB' : B.IsSymm) :
    Function.Involutive (B.dualBasis hB : Basis ι K V -> Basis ι K V) :=
  fun b => dualBasis_dualBasis hB hB' b

/--
lemma `dualBasis_injective` / 引理 `dualBasis_injective`

English:
lemma dualBasis_injective
  given: (hB : B.Nondegenerate) (hB' : B.IsSymm)
  proof: (B.dualBasis_involutive hB hB').injective

@[simp]

中文:
引理 dualBasis_injective
  条件: (hB : B.Nondegenerate) (hB' : B.IsSymm)
  证明: (B.dualBasis_involutive hB hB').injective

@[simp]

Depends on / 依赖: B.dualBasis_involutive, dualBasis_involutive, injective
-/
lemma dualBasis_injective (hB : B.Nondegenerate) (hB' : B.IsSymm) :
    Function.Injective (B.dualBasis hB : Basis ι K V -> Basis ι K V) :=
  (B.dualBasis_involutive hB hB').injective

@[simp]
/--
theorem `dualBasis_eq_iff` / 定理 `dualBasis_eq_iff`

English:
theorem dualBasis_eq_iff
  given: (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι -> V)
  proof: ⟨fun h _ _ => by rw [← h, apply_dualBasis_left],
    fun h => funext fun _ => (B.dualBasis hB b).ext_elem_iff.mpr fun _ => by
      rw [dualBasis_repr_apply]; rw [dualBasis_repr_apply]; rw [apply_dualBasis_left]; rw [h]⟩

中文:
定理 dualBasis_eq_iff
  条件: (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι -> V)
  证明: ⟨fun h _ _ => by rw [← h, apply_dualBasis_left],
    fun h => funext fun _ => (B.dualBasis hB b).ext_elem_iff.mpr fun _ => by
      rw [dualBasis_repr_apply]; rw [dualBasis_repr_apply]; rw [apply_dualBasis_left]; rw [h]⟩

Depends on / 依赖: B.dualBasis, apply_dualBasis_left, dualBasis, dualBasis_repr_apply, ext_elem_iff, ext_elem_iff.mpr
-/
theorem dualBasis_eq_iff (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι -> V) :
    B.dualBasis hB b = v ↔ forall i j, B (v i) (b j) = if j = i then 1 else 0 :=
  ⟨fun h _ _ => by rw [← h, apply_dualBasis_left],
    fun h => funext fun _ => (B.dualBasis hB b).ext_elem_iff.mpr fun _ => by
      rw [dualBasis_repr_apply]; rw [dualBasis_repr_apply]; rw [apply_dualBasis_left]; rw [h]⟩

end DualBasis

section LinearAdjoints

variable [FiniteDimensional K V]

/--
Definition of `symmCompOfNondegenerate` / `symmCompOfNondegenerate` 的定义

English:
definition symmCompOfNondegenerate
  signature: (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate)
  body: (B₂.toDual b₂).symm.toLinearMap.comp B₁

中文:
定义 symmCompOfNondegenerate
  签名: (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate)
  定义体: (B₂.toDual b₂).symm.toLinearMap.comp B₁

Depends on / 依赖: symm.toLinearMap.comp, toDual, toLinearMap
-/
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) :
    V ->ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁

/--
theorem `comp_symmCompOfNondegenerate_apply` / 定理 `comp_symmCompOfNondegenerate_apply`

English:
theorem comp_symmCompOfNondegenerate_apply
  statement: (B₁ : BilinForm K V) {B₂ : BilinForm K V}
  proof: by
  rw [symmCompOfNondegenerate]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  erw [LinearEquiv.apply_symm_apply (B₂.toDual b₂)]

@[simp]

中文:
定理 comp_symmCompOfNondegenerate_apply
  结论: (B₁ : BilinForm K V) {B₂ : BilinForm K V}
  证明: by
  rw [symmCompOfNondegenerate]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  erw [LinearEquiv.apply_symm_apply (B₂.toDual b₂)]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.coe_coe, apply_symm_apply, coe_coe, coe_comp, comp_apply, symmCompOfNondegenerate, toDual
-/
theorem comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v : V) :
    B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = B₁ v := by
  rw [symmCompOfNondegenerate]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  erw [LinearEquiv.apply_symm_apply (B₂.toDual b₂)]

@[simp]
/--
theorem `symmCompOfNondegenerate_left_apply` / 定理 `symmCompOfNondegenerate_left_apply`

English:
theorem symmCompOfNondegenerate_left_apply
  statement: (B₁ : BilinForm K V) {B₂ : BilinForm K V}
  proof: by
  conv_lhs => rw [comp_symmCompOfNondegenerate_apply]

中文:
定理 symmCompOfNondegenerate_left_apply
  结论: (B₁ : BilinForm K V) {B₂ : BilinForm K V}
  证明: by
  conv_lhs => rw [comp_symmCompOfNondegenerate_apply]

Depends on / 依赖: comp_symmCompOfNondegenerate_apply, conv_lhs
-/
theorem symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [comp_symmCompOfNondegenerate_apply]

/--
Definition of `leftAdjointOfNondegenerate` / `leftAdjointOfNondegenerate` 的定义

English:
definition leftAdjointOfNondegenerate
  signature: (B : BilinForm K V) (b : B.Nondegenerate)
  body: symmCompOfNondegenerate (B.compRight φ) B b

中文:
定义 leftAdjointOfNondegenerate
  签名: (B : BilinForm K V) (b : B.Nondegenerate)
  定义体: symmCompOfNondegenerate (B.compRight φ) B b

Depends on / 依赖: B.compRight, compRight, symmCompOfNondegenerate
-/
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V ->ₗ[K] V) : V ->ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b

/--
theorem `isAdjointPairLeftAdjointOfNondegenerate` / 定理 `isAdjointPairLeftAdjointOfNondegenerate`

English:
theorem isAdjointPairLeftAdjointOfNondegenerate
  statement: (B : BilinForm K V) (b : B.Nondegenerate)
  proof: fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x

中文:
定理 isAdjointPairLeftAdjointOfNondegenerate
  结论: (B : BilinForm K V) (b : B.Nondegenerate)
  证明: fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x
-/
theorem isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V ->ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x

/--
theorem `isAdjointPair_iff_eq_of_nondegenerate` / 定理 `isAdjointPair_iff_eq_of_nondegenerate`

English:
theorem isAdjointPair_iff_eq_of_nondegenerate
  statement: (B : BilinForm K V) (b : B.Nondegenerate)
  proof: ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩

中文:
定理 isAdjointPair_iff_eq_of_nondegenerate
  结论: (B : BilinForm K V) (b : B.Nondegenerate)
  证明: ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩

Depends on / 依赖: B.isAdjointPair_unique_of_nondegenerate, h.symm, isAdjointPairLeftAdjointOfNondegenerate, isAdjointPair_unique_of_nondegenerate
-/
theorem isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (ψ φ : V ->ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩

end LinearAdjoints

end BilinForm

end LinearMap
