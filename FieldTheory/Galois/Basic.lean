/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz, Yongle Hu, Jingting Wang
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `IsGalois F E` where `E` is an extension of `F`
- `fixedField H` where `H : Subgroup Gal(E/F)`
- `fixingSubgroup K` where `K : IntermediateField F E`
- `intermediateFieldEquivSubgroup` where `E/F` is finite dimensional and Galois

## Main results

- `IntermediateField.fixingSubgroup_fixedField` : If `E/F` is finite dimensional (but not
  necessarily Galois) then `fixingSubgroup (fixedField H) = H`
- `IsGalois.fixedField_fixingSubgroup`: If `E/F` is finite dimensional and Galois
  then `fixedField (fixingSubgroup K) = K`

Together, these two results prove the Galois correspondence.

- `IsGalois.tfae` : Equivalent characterizations of a Galois extension of finite degree

## Additional results

- Instances for `Algebra.IsQuadraticExtension`: a quadratic extension is Galois (if separable)
  with cyclic and thus abelian Galois group.

-/

@[expose] public section


open scoped Polynomial IntermediateField

open Module AlgEquiv IntermediateField

section

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

/-- A field extension E/F is Galois if it is both separable and normal. Note that in mathlib
a separable extension of fields is by definition algebraic. -/
@[stacks 09I0]
/--
Definition of `IsGalois` / `IsGalois` 的定义

English:
class IsGalois
  parameters: : Prop where
  axioms and operations (2):
    - [to_isSeparable : Algebra.IsSeparable F E]
    - [to_normal : Normal F E]

中文:
类 是Galois
  参数: : 命题 where
  公理与运算 (2 个):
    - [to_isSeparable : 代数.是可分 F E]
    - [to_normal : 正规 F E]
-/
class IsGalois : Prop where
  [to_isSeparable : Algebra.IsSeparable F E]
  [to_normal : Normal F E]

variable {F E}

/--
theorem `isGalois_iff` / 定理 `isGalois_iff`

English:
theorem isGalois_iff
  statement: IsGalois F E ↔ Algebra.IsSeparable F E ∧ Normal F E
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h =>
    { to_isSeparable := h.1
      to_normal := h.2 }⟩

中文:
定理 isGalois_iff
  结论: 是Galois F E ↔ 代数.是可分 F E ∧ 正规 F E
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h =>
    { to_isSeparable := h.1
      to_normal := h.2 }⟩

Depends on / 依赖: to_isSeparable, to_normal
-/
theorem isGalois_iff : IsGalois F E ↔ Algebra.IsSeparable F E ∧ Normal F E :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h =>
    { to_isSeparable := h.1
      to_normal := h.2 }⟩

attribute [instance 100] IsGalois.to_isSeparable IsGalois.to_normal

-- see Note [lower instance priority]
variable (F E)

namespace IsGalois

/--
Instance `self` / 实例 `self`

English:
instance self
  signature: : IsGalois F F
  body: ⟨⟩

中文:
实例 self
  签名: : 是Galois F F
  定义体: ⟨⟩
-/
instance self : IsGalois F F :=
  ⟨⟩

variable {E}

/--
theorem `integral` / 定理 `integral`

English:
theorem integral
  given: [IsGalois F E] (x : E)
  statement: IsIntegral F x
  proof: to_normal.isIntegral x

中文:
定理 integral
  条件: [是Galois F E] (x : E)
  结论: 是整 F x
  证明: to_normal.isIntegral x

Depends on / 依赖: isIntegral, to_normal, to_normal.isIntegral
-/
theorem integral [IsGalois F E] (x : E) : IsIntegral F x :=
  to_normal.isIntegral x

/--
theorem `separable` / 定理 `separable`

English:
theorem separable
  given: [IsGalois F E] (x : E)
  statement: IsSeparable F x
  proof: Algebra.IsSeparable.isSeparable F x

中文:
定理 separable
  条件: [是Galois F E] (x : E)
  结论: 是可分 F x
  证明: Algebra.IsSeparable.isSeparable F x

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, isSeparable
-/
theorem separable [IsGalois F E] (x : E) : IsSeparable F x :=
  Algebra.IsSeparable.isSeparable F x

/--
theorem `splits` / 定理 `splits`

English:
theorem splits
  given: [IsGalois F E] (x : E)
  statement: ((minpoly F x).map (algebraMap F E)).Splits
  proof: Normal.splits' x

中文:
定理 splits
  条件: [是Galois F E] (x : E)
  结论: ((minpoly F x).map (algebraMap F E)).Splits
  证明: Normal.splits' x

Depends on / 依赖: Normal, Normal.splits, splits
-/
theorem splits [IsGalois F E] (x : E) : ((minpoly F x).map (algebraMap F E)).Splits :=
  Normal.splits' x

variable (E)

/-- Let $E$ be a field. Let $G$ be a finite group acting on $E$.
Then the extension $E / E^G$ is Galois. -/
@[stacks 09I3 "first part"]
/--
Instance `of_fixed_field` / 实例 `of_fixed_field`

English:
instance of_fixed_field
  signature: (G : Type*) [Group G] [Finite G] [MulSemiringAction G E]
  body: ⟨⟩

中文:
实例 of_fixed_field
  签名: (G : 类型) [群 G] [有限 G] [MulSemiring作用 G E]
  定义体: ⟨⟩
-/
instance of_fixed_field (G : Type*) [Group G] [Finite G] [MulSemiringAction G E] :
    IsGalois (FixedPoints.subfield G E) E :=
  ⟨⟩

/--
theorem `IntermediateField.AdjoinSimple.card_aut_eq_finrank` / 定理 `IntermediateField.AdjoinSimple.card_aut_eq_finrank`

English:
theorem IntermediateField.AdjoinSimple.card_aut_eq_finrank
  statement: [FiniteDimensional F E] {α : E}
  proof: by
  rw [IntermediateField.adjoin.finrank hα]
  rw [← IntermediateField.card_algHom_adjoin_integral F hα h_sep h_splits]
  exact Nat.card_congr (algEquivEquivAlgHom F F⟮α⟯)

中文:
定理 中间域.AdjoinSimple.card_aut_eq_finrank
  结论: [有限维 F E] {α : E}
  证明: by
  rw [IntermediateField.adjoin.finrank hα]
  rw [← IntermediateField.card_algHom_adjoin_integral F hα h_sep h_splits]
  exact Nat.card_congr (algEquivEquivAlgHom F F⟮α⟯)

Depends on / 依赖: IntermediateField, IntermediateField.adjoin.finrank, IntermediateField.card_algHom_adjoin_integral, Nat.card_congr, adjoin, algEquivEquivAlgHom, card_algHom_adjoin_integral, card_congr, finrank, h_sep, h_splits
-/
theorem IntermediateField.AdjoinSimple.card_aut_eq_finrank [FiniteDimensional F E] {α : E}
    (hα : IsIntegral F α) (h_sep : IsSeparable F α)
    (h_splits : ((minpoly F α).map (algebraMap F F⟮α⟯)).Splits) :
    Nat.card Gal(F⟮α⟯/F) = finrank F F⟮α⟯ := by
  rw [IntermediateField.adjoin.finrank hα]
  rw [← IntermediateField.card_algHom_adjoin_integral F hα h_sep h_splits]
  exact Nat.card_congr (algEquivEquivAlgHom F F⟮α⟯)

/-- Let $E / F$ be a finite extension of fields. If $E$ is Galois over $F$, then
$|\text{Aut}(E/F)| = [E : F]$. -/
@[stacks 09I1 "'only if' part"]
/--
theorem `card_aut_eq_finrank` / 定理 `card_aut_eq_finrank`

English:
theorem card_aut_eq_finrank
  given: [FiniteDimensional F E] [IsGalois F E]
  proof: by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let iso : F⟮α⟯ ≃ₐ[F] E :=
    { toFun := fun e => e.val
      invFun := fun e => ⟨e, by rw [hα]; exact IntermediateField.mem_top⟩
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have H :

中文:
定理 card_aut_eq_finrank
  条件: [有限维 F E] [是Galois F E]
  证明: by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let iso : F⟮α⟯ ≃ₐ[F] E :=
    { toFun := fun e => e.val
      invFun := fun e => ⟨e, by rw [hα]; exact IntermediateField.mem_top⟩
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have H :

Depends on / 依赖: Field.exists_primitive_element, IntermediateField, IntermediateField.mem_top, IsGalois, IsGalois.integral, IsGalois.separable, IsGalois.splits, IsIntegral, IsSeparable, Splits, algebraMap, commutes, e.val, exists_primitive_element, h_sep, h_splits, integral, invFun, map_add, map_mul
-/
theorem card_aut_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Nat.card Gal(E/F) = finrank F E := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  let iso : F⟮α⟯ ≃ₐ[F] E :=
    { toFun := fun e => e.val
      invFun := fun e => ⟨e, by rw [hα]; exact IntermediateField.mem_top⟩
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have H : IsIntegral F α := IsGalois.integral F α
  have h_sep : IsSeparable F α := IsGalois.separable F α
  have h_splits : ((minpoly F α).map (algebraMap F E)).Splits := IsGalois.splits F α
  replace h_splits : ((minpoly F α).map (algebraMap F F⟮α⟯)).Splits := by
    simpa [Polynomial.map_map] using! h_splits.map iso.symm.toRingHom
  rw [← LinearEquiv.finrank_eq iso.toLinearEquiv]
  rw [← IntermediateField.AdjoinSimple.card_aut_eq_finrank F E H h_sep h_splits]
  apply Nat.card_congr
  exact Equiv.mk (fun ϕ => iso.trans (ϕ.trans iso.symm)) fun ϕ => iso.symm.trans (ϕ.trans iso)

/--
lemma `finiteDimensional_of_finite` / 引理 `finiteDimensional_of_finite`

English:
lemma finiteDimensional_of_finite
  given: [IsGalois F E] [Finite Gal(E/F)]
  statement: FiniteDimensional F E
  proof: by
  by_contra H
  obtain ⟨K, h₁, h₂⟩ := exists_lt_finrank_of_infinite_dimensional H (Nat.card Gal(E/F))
  let K' := normalClosure F K E
  have : IsGalois F K' := ⟨⟩
  have := Nat.card_le_card_of_surjective _
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K') (E := E))
  rw [IsGalois.car

中文:
引理 finiteDimensional_of_finite
  条件: [是Galois F E] [有限 Gal(E/F)]
  结论: 有限维 F E
  证明: by
  by_contra H
  obtain ⟨K, h₁, h₂⟩ := exists_lt_finrank_of_infinite_dimensional H (Nat.card Gal(E/F))
  let K' := normalClosure F K E
  have : IsGalois F K' := ⟨⟩
  have := Nat.card_le_card_of_surjective _
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K') (E := E))
  rw [IsGalois.car

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom_surjective, IsGalois, IsGalois.card_aut_eq_finrank, K.le_normalClosure, Nat.card, Nat.card_le_card_of_surjective, card_aut_eq_finrank, card_le_card_of_surjective, exists_lt_finrank_of_infinite_dimensional, finrank_le_of_le_right, le_normalClosure, normalClosure, not_ge, restrictNormalHom_surjective, this.trans_lt, trans_lt
-/
lemma finiteDimensional_of_finite [IsGalois F E] [Finite Gal(E/F)] : FiniteDimensional F E := by
  by_contra H
  obtain ⟨K, h₁, h₂⟩ := exists_lt_finrank_of_infinite_dimensional H (Nat.card Gal(E/F))
  let K' := normalClosure F K E
  have : IsGalois F K' := ⟨⟩
  have := Nat.card_le_card_of_surjective _
    (AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K') (E := E))
  rw [IsGalois.card_aut_eq_finrank] at this
  exact (this.trans_lt h₂).not_ge (finrank_le_of_le_right K.le_normalClosure)

end IsGalois

end

section IsGaloisTower

variable (F K E : Type*) [Field F] [Field K] [Field E] {E' : Type*} [Field E'] [Algebra F E']
variable [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

/-- Let $E / K / F$ be a tower of field extensions.
If $E$ is Galois over $F$, then $E$ is Galois over $K$. -/
@[stacks 09I2]
/--
theorem `IsGalois.tower_top_of_isGalois` / 定理 `IsGalois.tower_top_of_isGalois`

English:
theorem IsGalois.tower_top_of_isGalois
  given: [IsGalois F E]
  statement: IsGalois K E
  proof: { to_isSeparable := Algebra.isSeparable_tower_top_of_isSeparable F K E
    to_normal := Normal.tower_top_of_normal F K E }

中文:
定理 是Galois.tower_top_of_isGalois
  条件: [是Galois F E]
  结论: 是Galois K E
  证明: { to_isSeparable := Algebra.isSeparable_tower_top_of_isSeparable F K E
    to_normal := Normal.tower_top_of_normal F K E }

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_top_of_isSeparable, Normal, Normal.tower_top_of_normal, isSeparable_tower_top_of_isSeparable, to_isSeparable, to_normal, tower_top_of_normal
-/
theorem IsGalois.tower_top_of_isGalois [IsGalois F E] : IsGalois K E :=
  { to_isSeparable := Algebra.isSeparable_tower_top_of_isSeparable F K E
    to_normal := Normal.tower_top_of_normal F K E }

variable {F E}

-- see Note [lower instance priority]
instance (priority := 100) IsGalois.tower_top_intermediateField (K : IntermediateField F E)
    [IsGalois F E] : IsGalois K E :=
  IsGalois.tower_top_of_isGalois F K E

/--
theorem `isGalois_iff_isGalois_bot` / 定理 `isGalois_iff_isGalois_bot`

English:
theorem isGalois_iff_isGalois_bot
  statement: IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E
  proof: by
  constructor
  · intro h
    exact IsGalois.tower_top_of_isGalois (⊥ : IntermediateField F E) F E
  · intro h; infer_instance

中文:
定理 isGalois_iff_isGalois_bot
  结论: 是Galois (⊥ : 中间域 F E) E ↔ 是Galois F E
  证明: by
  constructor
  · intro h
    exact IsGalois.tower_top_of_isGalois (⊥ : IntermediateField F E) F E
  · intro h; infer_instance

Depends on / 依赖: IntermediateField, IsGalois, IsGalois.tower_top_of_isGalois, infer_instance, tower_top_of_isGalois
-/
theorem isGalois_iff_isGalois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E := by
  constructor
  · intro h
    exact IsGalois.tower_top_of_isGalois (⊥ : IntermediateField F E) F E
  · intro h; infer_instance

/--
theorem `IsGalois.of_algEquiv` / 定理 `IsGalois.of_algEquiv`

English:
theorem IsGalois.of_algEquiv
  given: [IsGalois F E] (f : E ≃ₐ[F] E')
  statement: IsGalois F E'
  proof: { to_isSeparable := Algebra.IsSeparable.of_algHom F E f.symm
    to_normal := Normal.of_algEquiv f }

中文:
定理 是Galois.of_algEquiv
  条件: [是Galois F E] (f : E ≃ₐ[F] E')
  结论: 是Galois F E'
  证明: { to_isSeparable := Algebra.IsSeparable.of_algHom F E f.symm
    to_normal := Normal.of_algEquiv f }

Depends on / 依赖: Algebra, Algebra.IsSeparable.of_algHom, Disjoint, IsSeparable, Normal, Normal.of_algEquiv, f.symm, imp_self, of_algEquiv, of_algHom, or_comm, to_isSeparable, to_normal
-/
theorem IsGalois.of_algEquiv [IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E' :=
  { to_isSeparable := Algebra.IsSeparable.of_algHom F E f.symm
    to_normal := Normal.of_algEquiv f }

/--
theorem `AlgEquiv.transfer_galois` / 定理 `AlgEquiv.transfer_galois`

English:
theorem AlgEquiv.transfer_galois
  given: (f : E ≃ₐ[F] E')
  statement: IsGalois F E ↔ IsGalois F E'
  proof: ⟨fun _ => IsGalois.of_algEquiv f, fun _ => IsGalois.of_algEquiv f.symm⟩

中文:
定理 代数等价.transfer_galois
  条件: (f : E ≃ₐ[F] E')
  结论: 是Galois F E ↔ 是Galois F E'
  证明: ⟨fun _ => IsGalois.of_algEquiv f, fun _ => IsGalois.of_algEquiv f.symm⟩

Depends on / 依赖: IsGalois, IsGalois.of_algEquiv, f.symm, of_algEquiv
-/
theorem AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E' :=
  ⟨fun _ => IsGalois.of_algEquiv f, fun _ => IsGalois.of_algEquiv f.symm⟩

/--
theorem `isGalois_iff_isGalois_top` / 定理 `isGalois_iff_isGalois_top`

English:
theorem isGalois_iff_isGalois_top
  statement: IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E
  proof: (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois

中文:
定理 isGalois_iff_isGalois_top
  结论: 是Galois F (⊤ : 中间域 F E) ↔ 是Galois F E
  证明: (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois

Depends on / 依赖: IntermediateField, IntermediateField.topEquiv, topEquiv, transfer_galois
-/
theorem isGalois_iff_isGalois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E :=
  (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois

/--
Instance `isGalois_bot` / 实例 `isGalois_bot`

English:
instance isGalois_bot
  signature: : IsGalois F (⊥ : IntermediateField F E)
  body: (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)

中文:
实例 isGalois_bot
  签名: : 是Galois F (⊥ : 中间域 F E)
  定义体: (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)

Depends on / 依赖: IntermediateField, IntermediateField.botEquiv, IsGalois, IsGalois.self, botEquiv, transfer_galois, transfer_galois.mpr
-/
instance isGalois_bot : IsGalois F (⊥ : IntermediateField F E) :=
  (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)

/--
theorem `IsGalois.of_equiv_equiv` / 定理 `IsGalois.of_equiv_equiv`

English:
theorem IsGalois.of_equiv_equiv
  statement: {M N : Type*} [Field N] [Field M] [Algebra M N]
  proof: isGalois_iff.mpr ⟨Algebra.IsSeparable.of_equiv_equiv f g hcomp, Normal.of_equiv_equiv hcomp⟩

中文:
定理 是Galois.of_equiv_equiv
  结论: {M N : 类型} [域 N] [域 M] [代数 M N]
  证明: isGalois_iff.mpr ⟨Algebra.IsSeparable.of_equiv_equiv f g hcomp, Normal.of_equiv_equiv hcomp⟩

Depends on / 依赖: Algebra, Algebra.IsSeparable.of_equiv_equiv, IsSeparable, Normal, Normal.of_equiv_equiv, isGalois_iff, isGalois_iff.mpr, of_equiv_equiv
-/
theorem IsGalois.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N]
    [h : IsGalois F E] {f : F ≃+* M} {g : E ≃+* N}
    (hcomp : (algebraMap M N).comp f = (g : E ->+* N).comp (algebraMap F E)) :
    IsGalois M N :=
  isGalois_iff.mpr ⟨Algebra.IsSeparable.of_equiv_equiv f g hcomp, Normal.of_equiv_equiv hcomp⟩

end IsGaloisTower

section GaloisCorrespondence

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
variable (H : Subgroup Gal(E/F)) (K : IntermediateField F E)

/--
Definition of `FixedPoints.intermediateField` / `FixedPoints.intermediateField` 的定义

English:
definition FixedPoints.intermediateField
  signature: (M : Type*) [Monoid M] [MulSemiringAction M E]
  body: { FixedPoints.subfield M E with
    carrier := MulAction.fixedPoints M E
    algebraMap_mem' := fun a g => smul_algebraMap g a }

中文:
定义 FixedPoints.intermediateField
  签名: (M : 类型) [幺半群 M] [MulSemiring作用 M E]
  定义体: { FixedPoints.subfield M E with
    carrier := MulAction.fixedPoints M E
    algebraMap_mem' := fun a g => smul_algebraMap g a }

Depends on / 依赖: FixedPoints, FixedPoints.subfield, MulAction, MulAction.fixedPoints, algebraMap_mem, carrier, fixedPoints, smul_algebraMap, subfield
-/
def FixedPoints.intermediateField (M : Type*) [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] : IntermediateField F E :=
  { FixedPoints.subfield M E with
    carrier := MulAction.fixedPoints M E
    algebraMap_mem' := fun a g => smul_algebraMap g a }

/--
lemma `FixedPoints.mem_intermediateField_iff` / 引理 `FixedPoints.mem_intermediateField_iff`

English:
lemma FixedPoints.mem_intermediateField_iff
  proof: .rfl

中文:
引理 FixedPoints.mem_intermediateField_iff
  证明: .rfl
-/
@[simp] lemma FixedPoints.mem_intermediateField_iff
    {M : Type*} [Monoid M] [MulSemiringAction M E] [SMulCommClass M F E] {x : E} :
    x in FixedPoints.intermediateField (F := F) M ↔ forall m : M, m • x = x := .rfl

namespace IntermediateField

/--
Definition of `fixedField` / `fixedField` 的定义

English:
definition fixedField
  signature: : IntermediateField F E
  body: FixedPoints.intermediateField H

中文:
定义 fixedField
  签名: : 中间域 F E
  定义体: FixedPoints.intermediateField H

Depends on / 依赖: FixedPoints, FixedPoints.intermediateField, intermediateField
-/
def fixedField : IntermediateField F E :=
  FixedPoints.intermediateField H

/--
lemma `mem_fixedField_iff` / 引理 `mem_fixedField_iff`

English:
lemma mem_fixedField_iff
  given: (x)
  proof: by
  change x in MulAction.fixedPoints H E ↔ _
  simp only [MulAction.mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, AlgEquiv.smul_def]

中文:
引理 mem_fixedField_iff
  条件: (x)
  证明: by
  change x in MulAction.fixedPoints H E ↔ _
  simp only [MulAction.mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, AlgEquiv.smul_def]
-/
@[simp] lemma mem_fixedField_iff (x) :
    x in fixedField H ↔ forall f in H, f x = x := by
  change x in MulAction.fixedPoints H E ↔ _
  simp only [MulAction.mem_fixedPoints, Subtype.forall, Subgroup.mk_smul, AlgEquiv.smul_def]

/--
lemma `fixedField_bot` / 引理 `fixedField_bot`

English:
lemma fixedField_bot
  statement: fixedField (⊥ : Subgroup Gal(E/F)) = ⊤
  proof: by
  ext
  simp

中文:
引理 fixedField_bot
  结论: fixedField (⊥ : 子群 Gal(E/F)) = ⊤
  证明: by
  ext
  simp
-/
@[simp] lemma fixedField_bot : fixedField (⊥ : Subgroup Gal(E/F)) = ⊤ := by
  ext
  simp

/--
theorem `finrank_fixedField_eq_card` / 定理 `finrank_fixedField_eq_card`

English:
theorem finrank_fixedField_eq_card
  given: [FiniteDimensional F E]
  proof: by
  have := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H E

中文:
定理 finrank_fixedField_eq_card
  条件: [有限维 F E]
  证明: by
  have := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H E

Depends on / 依赖: Fintype, Fintype.ofFinite, FixedPoints, FixedPoints.finrank_eq_card, Nat.card_eq_fintype_card, card_eq_fintype_card, finrank_eq_card, ofFinite
-/
theorem finrank_fixedField_eq_card [FiniteDimensional F E] :
    finrank (fixedField H) E = Nat.card H := by
  have := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  exact FixedPoints.finrank_eq_card H E

/-- The subgroup fixing an intermediate field. -/
nonrec def fixingSubgroup : Subgroup Gal(E/F) :=
  fixingSubgroup Gal(E/F) (K : Set E)

/--
theorem `le_iff_le` / 定理 `le_iff_le`

English:
theorem le_iff_le
  statement: K <= fixedField H ↔ H <= fixingSubgroup K
  proof: ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

中文:
定理 le_iff_le
  结论: K <= fixedField H ↔ H <= fixingSubgroup K
  证明: ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

Depends on / 依赖: Subtype, Subtype.mem
-/
theorem le_iff_le : K <= fixedField H ↔ H <= fixingSubgroup K :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

/--
theorem `fixingSubgroup_le` / 定理 `fixingSubgroup_le`

English:
theorem fixingSubgroup_le
  given: {K1 K2 : IntermediateField F E} (h12 : K1 <= K2)
  proof: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h12 hx⟩

中文:
定理 fixingSubgroup_le
  条件: {K1 K2 : 中间域 F E} (h12 : K1 <= K2)
  证明: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h12 hx⟩
-/
theorem fixingSubgroup_le {K1 K2 : IntermediateField F E} (h12 : K1 <= K2) :
    K2.fixingSubgroup <= K1.fixingSubgroup :=
  fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h12 hx⟩

/--
theorem `fixedField_le` / 定理 `fixedField_le`

English:
theorem fixedField_le
  given: {H1 H2 : Subgroup Gal(E/F)} (h12 : H1 <= H2)
  proof: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h12 hx⟩

中文:
定理 fixedField_le
  条件: {H1 H2 : 子群 Gal(E/F)} (h12 : H1 <= H2)
  证明: fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h12 hx⟩
-/
theorem fixedField_le {H1 H2 : Subgroup Gal(E/F)} (h12 : H1 <= H2) :
    fixedField H2 <= fixedField H1 :=
  fun _ hσ ⟨x, hx⟩ => hσ ⟨x, h12 hx⟩

/--
lemma `fixingSubgroup_antitone` / 引理 `fixingSubgroup_antitone`

English:
lemma fixingSubgroup_antitone
  statement: Antitone (@fixingSubgroup F _ E _ _)
  proof: fun _ _ => fixingSubgroup_le

中文:
引理 fixingSubgroup_antitone
  结论: 递减 (@fixingSubgroup F _ E _ _)
  证明: fun _ _ => fixingSubgroup_le

Depends on / 依赖: fixingSubgroup_le
-/
lemma fixingSubgroup_antitone : Antitone (@fixingSubgroup F _ E _ _) :=
  fun _ _ => fixingSubgroup_le

/--
lemma `fixedField_antitone` / 引理 `fixedField_antitone`

English:
lemma fixedField_antitone
  statement: Antitone (@fixedField F _ E _ _)
  proof: fun _ _ => fixedField_le

中文:
引理 fixedField_antitone
  结论: 递减 (@fixedField F _ E _ _)
  证明: fun _ _ => fixedField_le

Depends on / 依赖: fixedField_le
-/
lemma fixedField_antitone : Antitone (@fixedField F _ E _ _) :=
  fun _ _ => fixedField_le

/--
lemma `mem_fixingSubgroup_iff` / 引理 `mem_fixingSubgroup_iff`

English:
lemma mem_fixingSubgroup_iff
  given: (σ)
  statement: σ in fixingSubgroup K ↔ forall x in K, σ x = x
  proof: _root_.mem_fixingSubgroup_iff _

中文:
引理 mem_fixingSubgroup_iff
  条件: (σ)
  结论: σ in fixingSubgroup K ↔ 对任意 x in K, σ x = x
  证明: _root_.mem_fixingSubgroup_iff _
-/
@[simp] lemma mem_fixingSubgroup_iff (σ) : σ in fixingSubgroup K ↔ forall x in K, σ x = x :=
  _root_.mem_fixingSubgroup_iff _

/--
lemma `fixingSubgroup_top` / 引理 `fixingSubgroup_top`

English:
lemma fixingSubgroup_top
  statement: fixingSubgroup (⊤ : IntermediateField F E) = ⊥
  proof: by
  ext
  simp [DFunLike.ext_iff]

中文:
引理 fixingSubgroup_top
  结论: fixingSubgroup (⊤ : 中间域 F E) = ⊥
  证明: by
  ext
  simp [DFunLike.ext_iff]
-/
@[simp] lemma fixingSubgroup_top : fixingSubgroup (⊤ : IntermediateField F E) = ⊥ := by
  ext
  simp [DFunLike.ext_iff]

/--
lemma `fixingSubgroup_bot` / 引理 `fixingSubgroup_bot`

English:
lemma fixingSubgroup_bot
  statement: fixingSubgroup (⊥ : IntermediateField F E) = ⊤
  proof: by
  ext
  simp [mem_bot]

中文:
引理 fixingSubgroup_bot
  结论: fixingSubgroup (⊥ : 中间域 F E) = ⊤
  证明: by
  ext
  simp [mem_bot]
-/
@[simp] lemma fixingSubgroup_bot : fixingSubgroup (⊥ : IntermediateField F E) = ⊤ := by
  ext
  simp [mem_bot]

/--
theorem `fixingSubgroup_sup` / 定理 `fixingSubgroup_sup`

English:
theorem fixingSubgroup_sup
  given: {K L : IntermediateField F E}
  proof: by
  ext φ
  exact ⟨fun h => ⟨fixingSubgroup_antitone le_sup_left h, fixingSubgroup_antitone le_sup_right h⟩,
    by simp [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]⟩

中文:
定理 fixingSubgroup_sup
  条件: {K L : 中间域 F E}
  证明: by
  ext φ
  exact ⟨fun h => ⟨fixingSubgroup_antitone le_sup_left h, fixingSubgroup_antitone le_sup_right h⟩,
    by simp [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]⟩

Depends on / 依赖: IntermediateField, IntermediateField.le_iff_le, Subgroup, Subgroup.zpowers_le, fixingSubgroup_antitone, le_iff_le, le_sup_left, le_sup_right, zpowers_le
-/
theorem fixingSubgroup_sup {K L : IntermediateField F E} :
    (K ⊔ L).fixingSubgroup = K.fixingSubgroup ⊓ L.fixingSubgroup := by
  ext φ
  exact ⟨fun h => ⟨fixingSubgroup_antitone le_sup_left h, fixingSubgroup_antitone le_sup_right h⟩,
    by simp [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le]⟩

/--
Definition of `fixingSubgroupEquiv` / `fixingSubgroupEquiv` 的定义

English:
definition fixingSubgroupEquiv
  signature: : fixingSubgroup K ≃* Gal(E/K) where
  body: { AlgEquiv.toRingEquiv (ϕ : Gal(E/F)) with commutes' := ϕ.mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  map_mul' _ _ := by ext; rfl

中文:
定义 fixingSubgroupEquiv
  签名: : fixingSubgroup K ≃* Gal(E/K) where
  定义体: { AlgEquiv.toRingEquiv (ϕ : Gal(E/F)) with commutes' := ϕ.mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  map_mul' _ _ := by ext; rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.toRingEquiv, commutes, toRingEquiv
-/
def fixingSubgroupEquiv : fixingSubgroup K ≃* Gal(E/K) where
  toFun ϕ := { AlgEquiv.toRingEquiv (ϕ : Gal(E/F)) with commutes' := ϕ.mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  map_mul' _ _ := by ext; rfl

/--
theorem `fixingSubgroup_fixedField` / 定理 `fixingSubgroup_fixedField`

English:
theorem fixingSubgroup_fixedField
  given: [FiniteDimensional F E]
  statement: fixingSubgroup (fixedField H) = H
  proof: by
  have H_le : H <= fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  suffices Nat.card H = Nat.card (fixingSubgroup (fixedField H)) by
    exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Nat.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
        ⟨Set.inc

中文:
定理 fixingSubgroup_fixedField
  条件: [有限维 F E]
  结论: fixingSubgroup (fixedField H) = H
  证明: by
  have H_le : H <= fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  suffices Nat.card H = Nat.card (fixingSubgroup (fixedField H)) by
    exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Nat.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
        ⟨Set.inc

Depends on / 依赖: FixedPoints, FixedPoints.toAlgHomEquiv, H_le, Nat.bijective_iff_injective_and_card, Nat.card, Nat.card_congr, Set.eq_of_inclusion_surjective, Set.inclusion, Set.inclusion_injective, SetLike, SetLike.coe_injective, algEquivEquivAlgHom, bijective_iff_injective_and_card, card_congr, coe_injective, eq_of_inclusion_surjective, fixedField, fixingSubgroup, fixingSubgroupEquiv, inclusion
-/
theorem fixingSubgroup_fixedField [FiniteDimensional F E] : fixingSubgroup (fixedField H) = H := by
  have H_le : H <= fixingSubgroup (fixedField H) := (le_iff_le _ _).mp le_rfl
  suffices Nat.card H = Nat.card (fixingSubgroup (fixedField H)) by
    exact SetLike.coe_injective (Set.eq_of_inclusion_surjective
      ((Nat.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
        ⟨Set.inclusion_injective H_le, this⟩).2).symm
  apply Nat.card_congr
  refine (FixedPoints.toAlgHomEquiv H E).trans ?_
  refine (algEquivEquivAlgHom (fixedField H) E).toEquiv.symm.trans ?_
  exact (fixingSubgroupEquiv (fixedField H)).toEquiv.symm

/--
Definition of `subgroupEquivAlgEquiv` / `subgroupEquivAlgEquiv` 的定义

English:
definition subgroupEquivAlgEquiv
  signature: [FiniteDimensional F E] (H : Subgroup Gal(E/F))
  body: (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans (fixingSubgroupEquiv _)

中文:
定义 subgroupEquivAlgEquiv
  签名: [有限维 F E] (H : 子群 Gal(E/F))
  定义体: (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans (fixingSubgroupEquiv _)

Depends on / 依赖: MulEquiv, MulEquiv.subgroupCongr, fixingSubgroupEquiv, fixingSubgroup_fixedField, subgroupCongr
-/
def subgroupEquivAlgEquiv [FiniteDimensional F E] (H : Subgroup Gal(E/F)) :
    H ≃* Gal(E/IntermediateField.fixedField H) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans (fixingSubgroupEquiv _)

/--
Instance `fixedField.smul` / 实例 `fixedField.smul`

English:
instance fixedField.smul
  signature: : SMul K (fixedField (fixingSubgroup K)) where
  body: ⟨x * y, fun ϕ => by
    rw [smul_mul']; rw [show ϕ • (x : E) = ↑x from ϕ.2 x]; rw [show ϕ • (y : E) = ↑y from y.2 ϕ]⟩

中文:
实例 fixedField.smul
  签名: : 标量乘法 K (fixedField (fixingSubgroup K)) where
  定义体: ⟨x * y, fun ϕ => by
    rw [smul_mul']; rw [show ϕ • (x : E) = ↑x from ϕ.2 x]; rw [show ϕ • (y : E) = ↑y from y.2 ϕ]⟩

Depends on / 依赖: smul_mul
-/
instance fixedField.smul : SMul K (fixedField (fixingSubgroup K)) where
  smul x y := ⟨x * y, fun ϕ => by
    rw [smul_mul']; rw [show ϕ • (x : E) = ↑x from ϕ.2 x]; rw [show ϕ • (y : E) = ↑y from y.2 ϕ]⟩

/--
Instance `fixedField.algebra` / 实例 `fixedField.algebra`

English:
instance fixedField.algebra
  signature: : Algebra K (fixedField (fixingSubgroup K)) where
  body: { toFun x := ⟨x, fun ϕ => Subtype.mem ϕ x⟩
    map_zero' := rfl
    map_add' _ _ := rfl
    map_one' := rfl
    map_mul' _ _ := rfl }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

中文:
实例 fixedField.algebra
  签名: : 代数 K (fixedField (fixingSubgroup K)) where
  定义体: { toFun x := ⟨x, fun ϕ => Subtype.mem ϕ x⟩
    map_zero' := rfl
    map_add' _ _ := rfl
    map_one' := rfl
    map_mul' _ _ := rfl }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

Depends on / 依赖: Subtype, Subtype.mem, commutes, map_add, map_mul, map_one, map_zero, mul_comm, smul_def
-/
instance fixedField.algebra : Algebra K (fixedField (fixingSubgroup K)) where
  algebraMap :=
  { toFun x := ⟨x, fun ϕ => Subtype.mem ϕ x⟩
    map_zero' := rfl
    map_add' _ _ := rfl
    map_one' := rfl
    map_mul' _ _ := rfl }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

/--
Instance `fixedField.isScalarTower` / 实例 `fixedField.isScalarTower`

English:
instance fixedField.isScalarTower
  signature: : IsScalarTower K (fixedField (fixingSubgroup K)) E
  body: ⟨fun _ _ _ => mul_assoc _ _ _⟩

中文:
实例 fixedField.isScalarTower
  签名: : 标量塔 K (fixedField (fixingSubgroup K)) E
  定义体: ⟨fun _ _ _ => mul_assoc _ _ _⟩

Depends on / 依赖: mul_assoc
-/
instance fixedField.isScalarTower : IsScalarTower K (fixedField (fixingSubgroup K)) E :=
  ⟨fun _ _ _ => mul_assoc _ _ _⟩

end IntermediateField

namespace IsGalois

/--
theorem `fixedField_fixingSubgroup` / 定理 `fixedField_fixingSubgroup`

English:
theorem fixedField_fixingSubgroup
  given: [FiniteDimensional F E] [h : IsGalois F E]
  proof: by
  have K_le : K <= IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
    (IntermediateField.le_iff_le _ _).mpr le_rfl
  suffices
    finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E by
    exact (IntermediateField.eq_of_le_of_finrank_e

中文:
定理 fixedField_fixingSubgroup
  条件: [有限维 F E] [h : 是Galois F E]
  证明: by
  have K_le : K <= IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
    (IntermediateField.le_iff_le _ _).mpr le_rfl
  suffices
    finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E by
    exact (IntermediateField.eq_of_le_of_finrank_e

Depends on / 依赖: IntermediateField, IntermediateField.eq_of_le_of_finrank_eq, IntermediateField.finrank_fixedField_eq_card, IntermediateField.fixedField, IntermediateField.fixingSubgroup, IntermediateField.fixingSubgroupEquiv, IntermediateField.le_iff_le, K_le, Nat.card_congr, card_aut_eq_finrank, card_congr, eq_of_le_of_finrank_eq, finrank, finrank_fixedField_eq_card, fixedField, fixingSubgroup, fixingSubgroupEquiv, le_iff_le, le_rfl, toEquiv
-/
theorem fixedField_fixingSubgroup [FiniteDimensional F E] [h : IsGalois F E] :
    IntermediateField.fixedField (IntermediateField.fixingSubgroup K) = K := by
  have K_le : K <= IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
    (IntermediateField.le_iff_le _ _).mpr le_rfl
  suffices
    finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E by
    exact (IntermediateField.eq_of_le_of_finrank_eq' K_le this).symm
  rw [IntermediateField.finrank_fixedField_eq_card]; rw [Nat.card_congr (IntermediateField.fixingSubgroupEquiv K).toEquiv]
  exact (card_aut_eq_finrank K E).symm

/--
lemma `fixedField_top` / 引理 `fixedField_top`

English:
lemma fixedField_top
  given: [IsGalois F E] [FiniteDimensional F E]
  proof: by
  rw [← fixingSubgroup_bot]; rw [fixedField_fixingSubgroup]

中文:
引理 fixedField_top
  条件: [是Galois F E] [有限维 F E]
  证明: by
  rw [← fixingSubgroup_bot]; rw [fixedField_fixingSubgroup]
-/
@[simp] lemma fixedField_top [IsGalois F E] [FiniteDimensional F E] :
    fixedField (⊤ : Subgroup Gal(E/F)) = ⊥ := by
  rw [← fixingSubgroup_bot]; rw [fixedField_fixingSubgroup]

/--
theorem `mem_bot_iff_fixed` / 定理 `mem_bot_iff_fixed`

English:
theorem mem_bot_iff_fixed
  given: [IsGalois F E] [FiniteDimensional F E] (x : E)
  proof: by
  rw [← fixedField_top]; rw [mem_fixedField_iff]
  simp only [Subgroup.mem_top, forall_const]

中文:
定理 mem_bot_iff_fixed
  条件: [是Galois F E] [有限维 F E] (x : E)
  证明: by
  rw [← fixedField_top]; rw [mem_fixedField_iff]
  simp only [Subgroup.mem_top, forall_const]

Depends on / 依赖: Subgroup, Subgroup.mem_top, fixedField_top, forall_const, mem_fixedField_iff, mem_top
-/
theorem mem_bot_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x in (⊥ : IntermediateField F E) ↔ forall f : Gal(E/F), f x = x := by
  rw [← fixedField_top]; rw [mem_fixedField_iff]
  simp only [Subgroup.mem_top, forall_const]

/--
theorem `mem_range_algebraMap_iff_fixed` / 定理 `mem_range_algebraMap_iff_fixed`

English:
theorem mem_range_algebraMap_iff_fixed
  given: [IsGalois F E] [FiniteDimensional F E] (x : E)
  proof: mem_bot_iff_fixed x

中文:
定理 mem_range_algebraMap_iff_fixed
  条件: [是Galois F E] [有限维 F E] (x : E)
  证明: mem_bot_iff_fixed x

Depends on / 依赖: mem_bot_iff_fixed
-/
theorem mem_range_algebraMap_iff_fixed [IsGalois F E] [FiniteDimensional F E] (x : E) :
    x in Set.range (algebraMap F E) ↔ forall f : Gal(E/F), f x = x :=
  mem_bot_iff_fixed x

/--
theorem `card_fixingSubgroup_eq_finrank` / 定理 `card_fixingSubgroup_eq_finrank`

English:
theorem card_fixingSubgroup_eq_finrank
  given: [FiniteDimensional F E] [IsGalois F E]
  proof: by
  conv_rhs => rw [← fixedField_fixingSubgroup K, IntermediateField.finrank_fixedField_eq_card]

中文:
定理 card_fixingSubgroup_eq_finrank
  条件: [有限维 F E] [是Galois F E]
  证明: by
  conv_rhs => rw [← fixedField_fixingSubgroup K, IntermediateField.finrank_fixedField_eq_card]

Depends on / 依赖: IntermediateField, IntermediateField.finrank_fixedField_eq_card, conv_rhs, finrank_fixedField_eq_card, fixedField_fixingSubgroup
-/
theorem card_fixingSubgroup_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (IntermediateField.fixingSubgroup K) = finrank K E := by
  conv_rhs => rw [← fixedField_fixingSubgroup K, IntermediateField.finrank_fixedField_eq_card]

/-- The Galois correspondence from intermediate fields to subgroups. -/
@[simps! apply, stacks 09DW]
/--
Definition of `intermediateFieldEquivSubgroup` / `intermediateFieldEquivSubgroup` 的定义

English:
definition intermediateFieldEquivSubgroup
  signature: [FiniteDimensional F E] [IsGalois F E]
  body: OrderDual.toDual ∘ IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField ∘ OrderDual.ofDual
  left_inv K := fixedField_fixingSubgroup K
  right_inv H := IntermediateField.fixingSubgroup_fixedField H
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L]; rw [Intermedia

中文:
定义 intermediateFieldEquivSubgroup
  签名: [有限维 F E] [是Galois F E]
  定义体: OrderDual.toDual ∘ IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField ∘ OrderDual.ofDual
  left_inv K := fixedField_fixingSubgroup K
  right_inv H := IntermediateField.fixingSubgroup_fixedField H
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L]; rw [Intermedia

Depends on / 依赖: IntermediateField, IntermediateField.fixingSubgroup, OrderDual, OrderDual.toDual, fixingSubgroup, toDual
-/
def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup Gal(E/F))ᵒᵈ where
  toFun := OrderDual.toDual ∘ IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField ∘ OrderDual.ofDual
  left_inv K := fixedField_fixingSubgroup K
  right_inv H := IntermediateField.fixingSubgroup_fixedField H
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L]; rw [IntermediateField.le_iff_le]; rw [fixedField_fixingSubgroup L]
    rfl

section
variable [FiniteDimensional F E] [IsGalois F E]

/--
lemma `ofDual_intermediateFieldEquivSubgroup_apply` / 引理 `ofDual_intermediateFieldEquivSubgroup_apply`

English:
lemma ofDual_intermediateFieldEquivSubgroup_apply
  given: (K : IntermediateField F E)
  proof: rfl

中文:
引理 ofDual_intermediateFieldEquivSubgroup_apply
  条件: (K : 中间域 F E)
  证明: rfl
-/
lemma ofDual_intermediateFieldEquivSubgroup_apply (K : IntermediateField F E) :
    (intermediateFieldEquivSubgroup K).ofDual = K.fixingSubgroup := rfl

/--
lemma `intermediateFieldEquivSubgroup_symm_apply` / 引理 `intermediateFieldEquivSubgroup_symm_apply`

English:
lemma intermediateFieldEquivSubgroup_symm_apply
  given: (H : (Subgroup Gal(E/F))ᵒᵈ)
  proof: rfl

中文:
引理 intermediateFieldEquivSubgroup_symm_apply
  条件: (H : (子群 Gal(E/F))ᵒᵈ)
  证明: rfl
-/
@[simp] lemma intermediateFieldEquivSubgroup_symm_apply (H : (Subgroup Gal(E/F))ᵒᵈ) :
    intermediateFieldEquivSubgroup.symm H = fixedField H.ofDual := rfl

/--
lemma `intermediateFieldEquivSubgroup_symm_apply_toDual` / 引理 `intermediateFieldEquivSubgroup_symm_apply_toDual`

English:
lemma intermediateFieldEquivSubgroup_symm_apply_toDual
  given: (H : Subgroup Gal(E/F))
  proof: rfl

中文:
引理 intermediateFieldEquivSubgroup_symm_apply_toDual
  条件: (H : 子群 Gal(E/F))
  证明: rfl
-/
lemma intermediateFieldEquivSubgroup_symm_apply_toDual (H : Subgroup Gal(E/F)) :
    intermediateFieldEquivSubgroup.symm (.toDual H) = fixedField H := rfl

/--
theorem `fixedField_eq_iff_fixingSubgroup_eq` / 定理 `fixedField_eq_iff_fixingSubgroup_eq`

English:
theorem fixedField_eq_iff_fixingSubgroup_eq
  given: {K : IntermediateField F E} {H : Subgroup Gal(E/F)}
  proof: by
  simp [← OrderIso.apply_eq_iff_eq intermediateFieldEquivSubgroup, fixingSubgroup_fixedField,
    eq_comm]

中文:
定理 fixedField_eq_iff_fixingSubgroup_eq
  条件: {K : 中间域 F E} {H : 子群 Gal(E/F)}
  证明: by
  simp [← OrderIso.apply_eq_iff_eq intermediateFieldEquivSubgroup, fixingSubgroup_fixedField,
    eq_comm]

Depends on / 依赖: OrderIso, OrderIso.apply_eq_iff_eq, apply_eq_iff_eq, eq_comm, fixingSubgroup_fixedField, intermediateFieldEquivSubgroup
-/
theorem fixedField_eq_iff_fixingSubgroup_eq {K : IntermediateField F E} {H : Subgroup Gal(E/F)} :
    fixedField H = K ↔ K.fixingSubgroup = H := by
  simp [← OrderIso.apply_eq_iff_eq intermediateFieldEquivSubgroup, fixingSubgroup_fixedField,
    eq_comm]

end

/--
Definition of `galoisInsertionIntermediateFieldSubgroup` / `galoisInsertionIntermediateFieldSubgroup` 的定义

English:
definition galoisInsertionIntermediateFieldSubgroup
  signature: [FiniteDimensional F E]
  body: IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixingSubgroup_fixedField H).symm
  choice_eq _ _ := rfl

中文:
定义 galoisInsertion整数ermediateFieldSubgroup
  签名: [有限维 F E]
  定义体: IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixingSubgroup_fixedField H).symm
  choice_eq _ _ := rfl

Depends on / 依赖: IntermediateField, IntermediateField.fixingSubgroup, fixingSubgroup
-/
def galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] :
    GaloisInsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E -> Subgroup Gal(E/F)))
      ((IntermediateField.fixedField : Subgroup Gal(E/F) -> IntermediateField F E) ∘
        OrderDual.toDual) where
  choice K _ := IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixingSubgroup_fixedField H).symm
  choice_eq _ _ := rfl

/--
Definition of `galoisCoinsertionIntermediateFieldSubgroup` / `galoisCoinsertionIntermediateFieldSubgroup` 的定义

English:
definition galoisCoinsertionIntermediateFieldSubgroup
  signature: [FiniteDimensional F E] [IsGalois F E]
  body: OrderIso.toGaloisCoinsertion intermediateFieldEquivSubgroup

中文:
定义 galoisCoinsertion整数ermediateFieldSubgroup
  签名: [有限维 F E] [是Galois F E]
  定义体: OrderIso.toGaloisCoinsertion intermediateFieldEquivSubgroup

Depends on / 依赖: OrderIso, OrderIso.toGaloisCoinsertion, intermediateFieldEquivSubgroup, toGaloisCoinsertion
-/
def galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalois F E] :
    GaloisCoinsertion (OrderDual.toDual ∘
      (IntermediateField.fixingSubgroup : IntermediateField F E -> Subgroup Gal(E/F)))
      ((IntermediateField.fixedField : Subgroup Gal(E/F) -> IntermediateField F E) ∘
        OrderDual.toDual) :=
  OrderIso.toGaloisCoinsertion intermediateFieldEquivSubgroup

end IsGalois

section

/-In this section we prove that the normal subgroups correspond to the Galois subextensions
in the Galois correspondence and its related results. -/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open IntermediateField

open scoped Pointwise

/--
lemma `IntermediateField.restrictNormalHom_ker` / 引理 `IntermediateField.restrictNormalHom_ker`

English:
lemma IntermediateField.restrictNormalHom_ker
  given: (E : IntermediateField K L) [Normal K E]
  proof: by
  simp only [Subgroup.ext_iff, MonoidHom.mem_ker, AlgEquiv.ext_iff, one_apply, Subtype.ext_iff,
    restrictNormalHom_apply, Subtype.forall, mem_fixingSubgroup_iff, implies_true]

中文:
引理 中间域.restrictNormalHom_ker
  条件: (E : 中间域 K L) [正规 K E]
  证明: by
  simp only [Subgroup.ext_iff, MonoidHom.mem_ker, AlgEquiv.ext_iff, one_apply, Subtype.ext_iff,
    restrictNormalHom_apply, Subtype.forall, mem_fixingSubgroup_iff, implies_true]

Depends on / 依赖: AlgEquiv, AlgEquiv.ext_iff, MonoidHom, MonoidHom.mem_ker, Subgroup, Subgroup.ext_iff, Subtype, Subtype.ext_iff, Subtype.forall, ext_iff, implies_true, mem_fixingSubgroup_iff, mem_ker, one_apply, restrictNormalHom_apply
-/
lemma IntermediateField.restrictNormalHom_ker (E : IntermediateField K L) [Normal K E] :
    (restrictNormalHom E).ker = E.fixingSubgroup := by
  simp only [Subgroup.ext_iff, MonoidHom.mem_ker, AlgEquiv.ext_iff, one_apply, Subtype.ext_iff,
    restrictNormalHom_apply, Subtype.forall, mem_fixingSubgroup_iff, implies_true]

namespace IsGalois

variable (E : IntermediateField K L)

/--
Instance `of_fixedField_normal_subgroup` / 实例 `of_fixedField_normal_subgroup`

English:
instance of_fixedField_normal_subgroup
  signature: [IsGalois K L]
  body: Algebra.isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply normal_iff_forall_map_le'.mpr
    rintro σ x ⟨a, ha, rfl⟩ τ
    exact (symm_apply_eq σ).mp (ha ⟨σ⁻¹ * τ * σ, Subgroup.Normal.conj_mem' hn τ.1 τ.2 σ⟩)

中文:
实例 of_fixedField_normal_subgroup
  签名: [是Galois K L]
  定义体: Algebra.isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply normal_iff_forall_map_le'.mpr
    rintro σ x ⟨a, ha, rfl⟩ τ
    exact (symm_apply_eq σ).mp (ha ⟨σ⁻¹ * τ * σ, Subgroup.Normal.conj_mem' hn τ.1 τ.2 σ⟩)

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_bot_of_isSeparable, fixedField, isSeparable_tower_bot_of_isSeparable
-/
instance of_fixedField_normal_subgroup [IsGalois K L]
    (H : Subgroup Gal(L/K)) [hn : Subgroup.Normal H] : IsGalois K (fixedField H) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable K (fixedField H) L
  to_normal := by
    apply normal_iff_forall_map_le'.mpr
    rintro σ x ⟨a, ha, rfl⟩ τ
    exact (symm_apply_eq σ).mp (ha ⟨σ⁻¹ * τ * σ, Subgroup.Normal.conj_mem' hn τ.1 τ.2 σ⟩)

/--
Definition of `normalAutEquivQuotient` / `normalAutEquivQuotient` 的定义

English:
definition normalAutEquivQuotient
  signature: [FiniteDimensional K L] [IsGalois K L]
  body: QuotientGroup.liftEquiv _ (restrictNormalHom_surjective L)
    (fixingSubgroup_fixedField H).symm.trans (fixedField H).restrictNormalHom_ker.symm

中文:
定义 normalAutEquivQuotient
  签名: [有限维 K L] [是Galois K L]
  定义体: QuotientGroup.liftEquiv _ (restrictNormalHom_surjective L)
    (fixingSubgroup_fixedField H).symm.trans (fixedField H).restrictNormalHom_ker.symm

Depends on / 依赖: QuotientGroup, QuotientGroup.liftEquiv, fixedField, fixingSubgroup_fixedField, liftEquiv, restrictNormalHom_ker, restrictNormalHom_ker.symm, restrictNormalHom_surjective, symm.trans
-/
noncomputable def normalAutEquivQuotient [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [Subgroup.Normal H] :
    Gal(L/K) ⧸ H ≃* Gal(fixedField H/K) :=
QuotientGroup.liftEquiv _ (restrictNormalHom_surjective L)
    (fixingSubgroup_fixedField H).symm.trans (fixedField H).restrictNormalHom_ker.symm

/--
lemma `normalAutEquivQuotient_apply` / 引理 `normalAutEquivQuotient_apply`

English:
lemma normalAutEquivQuotient_apply
  statement: [FiniteDimensional K L] [IsGalois K L]
  proof: rfl

中文:
引理 normalAutEquivQuotient_apply
  结论: [有限维 K L] [是Galois K L]
  证明: rfl
-/
lemma normalAutEquivQuotient_apply [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [Subgroup.Normal H] (σ : Gal(L/K)) :
    normalAutEquivQuotient H σ = (restrictNormalHom (fixedField H)) σ := rfl

open scoped Pointwise

@[simp]
/--
theorem `map_fixingSubgroup` / 定理 `map_fixingSubgroup`

English:
theorem map_fixingSubgroup
  given: (σ : Gal(L/K))
  proof: by
  ext τ
  simp only [coe_map, AlgEquiv.coe_toAlgHom, Set.mem_image, SetLike.mem_coe, AlgEquiv.smul_def,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← symm_apply_eq,
    IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
  rf

中文:
定理 map_fixingSubgroup
  条件: (σ : Gal(L/K))
  证明: by
  ext τ
  simp only [coe_map, AlgEquiv.coe_toAlgHom, Set.mem_image, SetLike.mem_coe, AlgEquiv.smul_def,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← symm_apply_eq,
    IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
  rf

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.smul_def, IntermediateField, IntermediateField.fixingSubgroup, Set.mem_image, SetLike, SetLike.mem_coe, Subgroup, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, and_imp, coe_map, coe_toAlgHom, fixingSubgroup, forall_exists_index, mem_coe, mem_fixingSubgroup_iff, mem_image, mem_pointwise_smul_iff_inv_smul_mem, smul_def
-/
theorem map_fixingSubgroup (σ : Gal(L/K)) :
    (E.map σ).fixingSubgroup = (MulAut.conj σ) • E.fixingSubgroup := by
  ext τ
  simp only [coe_map, AlgEquiv.coe_toAlgHom, Set.mem_image, SetLike.mem_coe, AlgEquiv.smul_def,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← symm_apply_eq,
    IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
  rfl

/--
Instance `fixingSubgroup_normal_of_isGalois` / 实例 `fixingSubgroup_normal_of_isGalois`

English:
instance fixingSubgroup_normal_of_isGalois
  signature: [IsGalois K L] [IsGalois K E]
  body: by
  apply Subgroup.Normal.of_conjugate_fixed (fun σ => ?_)
  rw [← map_fixingSubgroup]; rw [normal_iff_forall_map_eq'.mp inferInstance σ]

中文:
实例 fixingSubgroup_normal_of_isGalois
  签名: [是Galois K L] [是Galois K E]
  定义体: by
  apply Subgroup.Normal.of_conjugate_fixed (fun σ => ?_)
  rw [← map_fixingSubgroup]; rw [normal_iff_forall_map_eq'.mp inferInstance σ]

Depends on / 依赖: Normal, Subgroup, Subgroup.Normal.of_conjugate_fixed, map_fixingSubgroup, normal_iff_forall_map_eq, of_conjugate_fixed
-/
instance fixingSubgroup_normal_of_isGalois [IsGalois K L] [IsGalois K E] :
    E.fixingSubgroup.Normal := by
  apply Subgroup.Normal.of_conjugate_fixed (fun σ => ?_)
  rw [← map_fixingSubgroup]; rw [normal_iff_forall_map_eq'.mp inferInstance σ]

end IsGalois

end

end GaloisCorrespondence

section GaloisEquivalentDefinitions

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

namespace IsGalois

/--
theorem `is_separable_splitting_field` / 定理 `is_separable_splitting_field`

English:
theorem is_separable_splitting_field
  given: [FiniteDimensional F E] [IsGalois F E]
  proof: by
  obtain ⟨α, h1⟩ := Field.exists_primitive_element F E
  use minpoly F α, separable F α, IsGalois.splits F α
  rw [eq_top_iff]; rw [← IntermediateField.top_toSubalgebra]; rw [← h1]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (integral F α).isAlgebraic]
  apply Algebra.adjoin

中文:
定理 is_separable_splitting_field
  条件: [有限维 F E] [是Galois F E]
  证明: by
  obtain ⟨α, h1⟩ := Field.exists_primitive_element F E
  use minpoly F α, separable F α, IsGalois.splits F α
  rw [eq_top_iff]; rw [← IntermediateField.top_toSubalgebra]; rw [← h1]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (integral F α).isAlgebraic]
  apply Algebra.adjoin

Depends on / 依赖: Algebra, Algebra.adjoin_mono, Field.exists_primitive_element, IntermediateField, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic, IntermediateField.top_toSubalgebra, IsGalois, IsGalois.splits, Polynomial, Polynomial.mem_rootSet, Set.singleton_subset_iff, adjoin_mono, adjoin_simple_toSubalgebra_of_isAlgebraic, eq_top_iff, exists_primitive_element, integral, isAlgebraic, mem_rootSet, minpoly, minpoly.aeval
-/
theorem is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] :
    exists p : F[X], p.Separable ∧ p.IsSplittingField F E := by
  obtain ⟨α, h1⟩ := Field.exists_primitive_element F E
  use minpoly F α, separable F α, IsGalois.splits F α
  rw [eq_top_iff]; rw [← IntermediateField.top_toSubalgebra]; rw [← h1]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (integral F α).isAlgebraic]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff]; rw [Polynomial.mem_rootSet]
  exact ⟨minpoly.ne_zero (integral F α), minpoly.aeval _ _⟩

/--
theorem `of_fixedField_eq_bot` / 定理 `of_fixedField_eq_bot`

English:
theorem of_fixedField_eq_bot
  statement: [FiniteDimensional F E]
  proof: by
  rw [← isGalois_iff_isGalois_bot]; rw [← h]
  exact IsGalois.of_fixed_field E (⊤ : Subgroup Gal(E/F))

中文:
定理 of_fixedField_eq_bot
  结论: [有限维 F E]
  证明: by
  rw [← isGalois_iff_isGalois_bot]; rw [← h]
  exact IsGalois.of_fixed_field E (⊤ : Subgroup Gal(E/F))

Depends on / 依赖: IsGalois, IsGalois.of_fixed_field, Subgroup, isGalois_iff_isGalois_bot, of_fixed_field
-/
theorem of_fixedField_eq_bot [FiniteDimensional F E]
    (h : IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥) : IsGalois F E := by
  rw [← isGalois_iff_isGalois_bot]; rw [← h]
  exact IsGalois.of_fixed_field E (⊤ : Subgroup Gal(E/F))

/-- Let $E / F$ be a finite extension of fields. If $|\text{Aut}(E/F)| = [E : F]$, then
$E$ is Galois over $F$. -/
@[stacks 09I1 "'if' part"]
/--
theorem `of_card_aut_eq_finrank` / 定理 `of_card_aut_eq_finrank`

English:
theorem of_card_aut_eq_finrank
  statement: [FiniteDimensional F E]
  proof: by
  apply of_fixedField_eq_bot
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup Gal(E/F))) E := finrank_pos
  rw [← IntermediateField.finrank_eq_one_iff]; rw [← mul_left_inj' (ne_of_lt p).symm]; rw [finrank_mul_finrank]; rw [← h]; rw [one_mul]; rw [IntermediateField.finrank_fixedF

中文:
定理 of_card_aut_eq_finrank
  结论: [有限维 F E]
  证明: by
  apply of_fixedField_eq_bot
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup Gal(E/F))) E := finrank_pos
  rw [← IntermediateField.finrank_eq_one_iff]; rw [← mul_left_inj' (ne_of_lt p).symm]; rw [finrank_mul_finrank]; rw [← h]; rw [one_mul]; rw [IntermediateField.finrank_fixedF

Depends on / 依赖: IntermediateField, IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_fixedField_eq_card, IntermediateField.fixedField, Nat.card_congr, Subgroup, Subgroup.mem_top, card_congr, finrank, finrank_eq_one_iff, finrank_fixedField_eq_card, finrank_mul_finrank, finrank_pos, fixedField, invFun, mem_top, mul_left_inj, ne_of_lt, of_fixedField_eq_bot, one_mul
-/
theorem of_card_aut_eq_finrank [FiniteDimensional F E]
    (h : Nat.card Gal(E/F) = finrank F E) : IsGalois F E := by
  apply of_fixedField_eq_bot
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup Gal(E/F))) E := finrank_pos
  rw [← IntermediateField.finrank_eq_one_iff]; rw [← mul_left_inj' (ne_of_lt p).symm]; rw [finrank_mul_finrank]; rw [← h]; rw [one_mul]; rw [IntermediateField.finrank_fixedField_eq_card]
  apply Nat.card_congr
  exact { toFun := fun g => ⟨g, Subgroup.mem_top g⟩, invFun := (↑) }

variable {F} {E}
variable {p : F[X]}

@[deprecated "No replacement; this was an auxiliary lemma used to prove \
`Algebra.isSeparable_of_separable_splitting_field`." (since := "2026-06-12")]
/--
theorem `of_separable_splitting_field_aux` / 定理 `of_separable_splitting_field_aux`

English:
theorem of_separable_splitting_field_aux
  statement: [hFE : FiniteDimensional F E] [sp : p.IsSplittingField F E]
  proof: by
  have h : IsIntegral K x := (isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x).tower_top
  have h1 : p != 0 := fun hp => by
    rw [hp]; rw [Polynomial.aroots_zero] at hx
    exact Multiset.notMem_zero x hx
  have h2 : minpoly K x ∣ p.map (algebraMap F K) := by
    apply minpoly.dvd
    rw

中文:
定理 of_separable_splitting_field_aux
  结论: [hFE : 有限维 F E] [sp : p.是分裂域 F E]
  证明: by
  have h : IsIntegral K x := (isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x).tower_top
  have h1 : p != 0 := fun hp => by
    rw [hp]; rw [Polynomial.aroots_zero] at hx
    exact Multiset.notMem_zero x hx
  have h2 : minpoly K x ∣ p.map (algebraMap F K) := by
    apply minpoly.dvd
    rw

Depends on / 依赖: IsIntegral, IsNoetherian, IsNoetherian.iff_fg, IsScalarTower, IsScalarTower.algebraMap_eq, Multiset, Multiset.notMem_zero, Polynomial, Polynomial.aeval_def, Polynomial.aroots_zero, Polynomial.eval, Polynomial.eval_map, Polynomial.map_ne_zero, Polynomial.mem_roots, aeval_def, algebraMap, algebraMap_eq, aroots_zero, eval_map, iff_fg
-/
theorem of_separable_splitting_field_aux [hFE : FiniteDimensional F E] [sp : p.IsSplittingField F E]
    (hp : p.Separable) (K : Type*) [Field K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    {x : E} (hx : x in p.aroots E) :
    Nat.card (K⟮x⟯.restrictScalars F ->ₐ[F] E) = Nat.card (K ->ₐ[F] E) * finrank K K⟮x⟯ := by
  have h : IsIntegral K x := (isIntegral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x).tower_top
  have h1 : p != 0 := fun hp => by
    rw [hp]; rw [Polynomial.aroots_zero] at hx
    exact Multiset.notMem_zero x hx
  have h2 : minpoly K x ∣ p.map (algebraMap F K) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_def]; rw [Polynomial.eval₂_map]; rw [← Polynomial.eval_map]; rw [←
      IsScalarTower.algebraMap_eq]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero h1)).mp hx
  let key_equiv : (K⟮x⟯.restrictScalars F ->ₐ[F] E) ≃
      Σ f : K ->ₐ[F] E, @AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f) := by
    change (K⟮x⟯ ->ₐ[F] E) ≃ Σ f : K ->ₐ[F] E, _
    exact algHomEquivSigma
  have : forall f : K ->ₐ[F] E, Finite (@AlgHom K K⟮x⟯ E _ _ _ _ (RingHom.toAlgebra f)) := fun f => by
    have := Finite.of_equiv _ key_equiv
    apply Finite.of_injective (Sigma.mk f) fun _ _ H => eq_of_heq (Sigma.ext_iff.mp H).2
  have : FiniteDimensional F K := FiniteDimensional.left F K E
  rw [Nat.card_congr key_equiv]; rw [Nat.card_sigma]; rw [IntermediateField.adjoin.finrank h]; rw [Nat.card_eq_fintype_card]
  apply Finset.sum_const_nat
  intro f _
  rw [← @IntermediateField.card_algHom_adjoin_integral K _ E _ _ x E _ (RingHom.toAlgebra f) h]
  · exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap F K)).mpr hp) h2
  · apply sp.splits.of_dvd (Polynomial.map_ne_zero h1)
    rwa [← f.comp_algebraMap, ← p.map_map, RingHom.algebraMap_toAlgebra, Polynomial.map_dvd_map']

/--
theorem `of_separable_splitting_field` / 定理 `of_separable_splitting_field`

English:
theorem of_separable_splitting_field
  given: [p.IsSplittingField F E] (hp : p.Separable)
  proof: { to_isSeparable := Algebra.isSeparable_of_separable_splitting_field F E hp,
    to_normal := Normal.of_isSplittingField p }

中文:
定理 of_separable_splitting_field
  条件: [p.是分裂域 F E] (hp : p.可分)
  证明: { to_isSeparable := Algebra.isSeparable_of_separable_splitting_field F E hp,
    to_normal := Normal.of_isSplittingField p }

Depends on / 依赖: Algebra, Algebra.isSeparable_of_separable_splitting_field, Normal, Normal.of_isSplittingField, isSeparable_of_separable_splitting_field, of_isSplittingField, to_isSeparable, to_normal
-/
theorem of_separable_splitting_field [p.IsSplittingField F E] (hp : p.Separable) :
    IsGalois F E :=
  { to_isSeparable := Algebra.isSeparable_of_separable_splitting_field F E hp,
    to_normal := Normal.of_isSplittingField p }

/--
theorem `tfae` / 定理 `tfae`

English:
theorem tfae
  given: [FiniteDimensional F E]
  statement: List.TFAE [
  proof: by
  tfae_have 1 -> 2 := fun h => OrderIso.map_bot (@intermediateFieldEquivSubgroup F _ E _ _ _ h).symm
  tfae_have 1 -> 3 := fun _ => card_aut_eq_finrank F E
  tfae_have 1 -> 4 := fun _ => is_separable_splitting_field F E
  tfae_have 2 -> 1 := of_fixedField_eq_bot F E
  tfae_have 3 -> 1 := of_card_

中文:
定理 tfae
  条件: [有限维 F E]
  结论: 列表.TFAE [
  证明: by
  tfae_have 1 -> 2 := fun h => OrderIso.map_bot (@intermediateFieldEquivSubgroup F _ E _ _ _ h).symm
  tfae_have 1 -> 3 := fun _ => card_aut_eq_finrank F E
  tfae_have 1 -> 4 := fun _ => is_separable_splitting_field F E
  tfae_have 2 -> 1 := of_fixedField_eq_bot F E
  tfae_have 3 -> 1 := of_card_

Depends on / 依赖: OrderIso, OrderIso.map_bot, card_aut_eq_finrank, intermediateFieldEquivSubgroup, is_separable_splitting_field, map_bot, of_card_aut_eq_finrank, of_fixedField_eq_bot, of_separable_splitting_field, tfae_finish, tfae_have
-/
theorem tfae [FiniteDimensional F E] : List.TFAE [
    IsGalois F E,
    IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥,
    Nat.card Gal(E/F) = finrank F E,
    exists p : F[X], p.Separable ∧ p.IsSplittingField F E] := by
  tfae_have 1 -> 2 := fun h => OrderIso.map_bot (@intermediateFieldEquivSubgroup F _ E _ _ _ h).symm
  tfae_have 1 -> 3 := fun _ => card_aut_eq_finrank F E
  tfae_have 1 -> 4 := fun _ => is_separable_splitting_field F E
  tfae_have 2 -> 1 := of_fixedField_eq_bot F E
  tfae_have 3 -> 1 := of_card_aut_eq_finrank F E
  tfae_have 4 -> 1 := fun ⟨h, hp1, _⟩ => of_separable_splitting_field hp1
  tfae_finish

/--
theorem `sup_right` / 定理 `sup_right`

English:
theorem sup_right
  statement: (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional F K]
  proof: by
  obtain ⟨T, hT₁, hT₂⟩ := IsGalois.is_separable_splitting_field F K
  let T' := T.map (algebraMap F L)
  suffices T'.IsSplittingField L E from IsGalois.of_separable_splitting_field (p := T') hT₁.map
  rw [isSplittingField_iff_intermediateField] at hT₂ ⊢
  constructor
  · rw [Polynomial.map_map, ←

中文:
定理 sup_right
  结论: (K L : 中间域 F E) [是Galois F K] [有限维 F K]
  证明: by
  obtain ⟨T, hT₁, hT₂⟩ := IsGalois.is_separable_splitting_field F K
  let T' := T.map (algebraMap F L)
  suffices T'.IsSplittingField L E from IsGalois.of_separable_splitting_field (p := T') hT₁.map
  rw [isSplittingField_iff_intermediateField] at hT₂ ⊢
  constructor
  · rw [Polynomial.map_map, ←

Depends on / 依赖: IsGalois, IsGalois.is_separable_splitting_field, IsGalois.of_separable_splitting_field, IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.toAlgHom, IsSplittingField, Polynomial, Polynomial.Splits.of_algHom, Polynomial.map_map, Polynomial.mem_rootSet, Set.ext_iff, Splits, T.map, T.rootSet, algebraMap, algebraMap_eq, ext_iff, isSplittingField_iff_intermediateField, is_separable_splitting_field
-/
theorem sup_right (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional F K]
    (h : K ⊔ L = ⊤) : IsGalois L E := by
  obtain ⟨T, hT₁, hT₂⟩ := IsGalois.is_separable_splitting_field F K
  let T' := T.map (algebraMap F L)
  suffices T'.IsSplittingField L E from IsGalois.of_separable_splitting_field (p := T') hT₁.map
  rw [isSplittingField_iff_intermediateField] at hT₂ ⊢
  constructor
  · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact Polynomial.Splits.of_algHom hT₂.1 (IsScalarTower.toAlgHom _ _ _)
  · have h' : T'.rootSet E = T.rootSet E := by simp [Set.ext_iff, Polynomial.mem_rootSet', T']
    rw [← lift_inj]; rw [lift_adjoin]; rw [← coe_val]; rw [hT₂.1.image_rootSet] at hT₂
    rw [← restrictScalars_eq_top_iff (K := F)]; rw [restrictScalars_adjoin]; rw [adjoin_union]; rw [adjoin_self]; rw [h']; rw [hT₂.2]; rw [lift_top]; rw [sup_comm]; rw [h]

end IsGalois

end GaloisEquivalentDefinitions

section normalClosure

variable (k K F : Type*) [Field k] [Field K] [Field F] [Algebra k K] [Algebra k F] [Algebra K F]
  [IsScalarTower k K F] [IsGalois k F]

/-- Let $F / K / k$ be a tower of field extensions. If $F$ is Galois over $k$,
then the normal closure of $K$ over $k$ in $F$ is Galois over $k$. -/
@[stacks 0EXM]
/--
Instance `IsGalois.normalClosure` / 实例 `IsGalois.normalClosure`

English:
instance IsGalois.normalClosure
  signature: : IsGalois k (normalClosure k K F) where
  body: Algebra.isSeparable_tower_bot_of_isSeparable k _ F

中文:
实例 是Galois.normalClosure
  签名: : 是Galois k (normalClosure k K F) where
  定义体: Algebra.isSeparable_tower_bot_of_isSeparable k _ F

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_bot_of_isSeparable, isSeparable_tower_bot_of_isSeparable
-/
instance IsGalois.normalClosure : IsGalois k (normalClosure k K F) where
  to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable k _ F

end normalClosure

section IsAlgClosure

instance (priority := 100) IsAlgClosure.isGalois (k K : Type*) [Field k] [Field K] [Algebra k K]
    [IsAlgClosure k K] [CharZero k] : IsGalois k K where

end IsAlgClosure


section restrictRestrictAlgEquivMapHom

namespace IntermediateField

/--
Definition of `restrictRestrictAlgEquivMapHom` / `restrictRestrictAlgEquivMapHom` 的定义

English:
definition restrictRestrictAlgEquivMapHom
  signature: (F K L E : Type*) [Field F] [Field K] [Field L]
  body: (AlgEquiv.restrictNormalHom K).comp (MulSemiringAction.toAlgAut Gal(E/L) F E)

中文:
定义 restrictRestrictAlgEquivMapHom
  签名: (F K L E : 类型) [域 F] [域 K] [域 L]
  定义体: (AlgEquiv.restrictNormalHom K).comp (MulSemiringAction.toAlgAut Gal(E/L) F E)

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom, MulSemiringAction, MulSemiringAction.toAlgAut, restrictNormalHom, toAlgAut
-/
noncomputable def restrictRestrictAlgEquivMapHom (F K L E : Type*) [Field F] [Field K] [Field L]
    [Field E] [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
    [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K] :
    Gal(E/L) ->* Gal(K/F) :=
  (AlgEquiv.restrictNormalHom K).comp (MulSemiringAction.toAlgAut Gal(E/L) F E)

variable {F E : Type*} (E' : Type*) [Field F] [Field E] [Field E']
  [Algebra F E] [Algebra F E'] [Algebra E E'] [IsScalarTower F E E']
  (K L : IntermediateField F E) [Normal F K]

@[simp]
/--
theorem `restrictRestrictAlgEquivMapHom_apply` / 定理 `restrictRestrictAlgEquivMapHom_apply`

English:
theorem restrictRestrictAlgEquivMapHom_apply
  given: (φ : Gal(E/L)) (x : K)
  proof: by
  simp [restrictRestrictAlgEquivMapHom, AlgEquiv.restrictNormalHom_apply]

中文:
定理 restrictRestrictAlgEquivMapHom_apply
  条件: (φ : Gal(E/L)) (x : K)
  证明: by
  simp [restrictRestrictAlgEquivMapHom, AlgEquiv.restrictNormalHom_apply]

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom_apply, restrictNormalHom_apply, restrictRestrictAlgEquivMapHom
-/
theorem restrictRestrictAlgEquivMapHom_apply (φ : Gal(E/L)) (x : K) :
    restrictRestrictAlgEquivMapHom F K L E φ x = φ x := by
  simp [restrictRestrictAlgEquivMapHom, AlgEquiv.restrictNormalHom_apply]

/--
theorem `restrictRestrictAlgEquivMapHom_injective` / 定理 `restrictRestrictAlgEquivMapHom_injective`

English:
theorem restrictRestrictAlgEquivMapHom_injective
  given: (h : K ⊔ L = ⊤)
  proof: by
  refine (injective_iff_map_eq_one _).mpr fun φ hφ => ?_
  suffices h : MulSemiringAction.toAlgAut Gal(E/L) F E φ = 1 by rwa [AlgEquiv.ext_iff] at h ⊢
  rw [← Subgroup.mem_bot]; rw [← fixingSubgroup_top]; rw [← h]; rw [fixingSubgroup_sup]
  exact ⟨fun x => (hφ ▸ restrictRestrictAlgEquivMapHom_app

中文:
定理 restrictRestrictAlgEquivMapHom_injective
  条件: (h : K ⊔ L = ⊤)
  证明: by
  refine (injective_iff_map_eq_one _).mpr fun φ hφ => ?_
  suffices h : MulSemiringAction.toAlgAut Gal(E/L) F E φ = 1 by rwa [AlgEquiv.ext_iff] at h ⊢
  rw [← Subgroup.mem_bot]; rw [← fixingSubgroup_top]; rw [← h]; rw [fixingSubgroup_sup]
  exact ⟨fun x => (hφ ▸ restrictRestrictAlgEquivMapHom_app

Depends on / 依赖: AlgEquiv, AlgEquiv.ext_iff, MulSemiringAction, MulSemiringAction.toAlgAut, Subgroup, Subgroup.mem_bot, commutes, ext_iff, fixingSubgroup_sup, fixingSubgroup_top, injective_iff_map_eq_one, mem_bot, restrictRestrictAlgEquivMapHom_apply, toAlgAut
-/
theorem restrictRestrictAlgEquivMapHom_injective (h : K ⊔ L = ⊤) :
    Function.Injective (restrictRestrictAlgEquivMapHom F K L E) := by
  refine (injective_iff_map_eq_one _).mpr fun φ hφ => ?_
  suffices h : MulSemiringAction.toAlgAut Gal(E/L) F E φ = 1 by rwa [AlgEquiv.ext_iff] at h ⊢
  rw [← Subgroup.mem_bot]; rw [← fixingSubgroup_top]; rw [← h]; rw [fixingSubgroup_sup]
  exact ⟨fun x => (hφ ▸ restrictRestrictAlgEquivMapHom_apply K L φ x).symm, φ.commutes⟩

/--
theorem `restrictRestrictAlgEquivMapHom_surjective` / 定理 `restrictRestrictAlgEquivMapHom_surjective`

English:
theorem restrictRestrictAlgEquivMapHom_surjective
  statement: [FiniteDimensional F K] [FiniteDimensional L E]
  proof: by
  suffices fixedField (restrictRestrictAlgEquivMapHom F K L E).range = ⊥ from
MonoidHom.range_eq_top.mp
      fixingSubgroup_fixedField (restrictRestrictAlgEquivMapHom F K L E).range ▸
        this ▸ fixingSubgroup_bot
  refine eq_bot_iff.mpr fun ⟨x, hx₁⟩ hx₂ => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ : x in 

中文:
定理 restrictRestrictAlgEquivMapHom_surjective
  结论: [有限维 F K] [有限维 L E]
  证明: by
  suffices fixedField (restrictRestrictAlgEquivMapHom F K L E).range = ⊥ from
MonoidHom.range_eq_top.mp
      fixingSubgroup_fixedField (restrictRestrictAlgEquivMapHom F K L E).range ▸
        this ▸ fixingSubgroup_bot
  refine eq_bot_iff.mpr fun ⟨x, hx₁⟩ hx₂ => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ : x in 

Depends on / 依赖: IsGalois, IsGalois.mem_bot_iff_fixed, MonoidHom, MonoidHom.range_eq_top.mp, Set.range, algebraMap, congr_arg, eq_bot_iff, eq_bot_iff.mpr, fixedField, fixingSubgroup_bot, fixingSubgroup_fixedField, mem_bot, mem_bot.mp, mem_bot_iff_fixed, mem_fixedField_iff, range_eq_top, restrictRestrictAlgEquivMapHom, restrictRestrictAlgEquivMapHom_apply
-/
theorem restrictRestrictAlgEquivMapHom_surjective [FiniteDimensional F K] [FiniteDimensional L E]
    [IsGalois L E] (h : K ⊓ L = ⊥) :
    Function.Surjective (restrictRestrictAlgEquivMapHom F K L E) := by
  suffices fixedField (restrictRestrictAlgEquivMapHom F K L E).range = ⊥ from
MonoidHom.range_eq_top.mp
      fixingSubgroup_fixedField (restrictRestrictAlgEquivMapHom F K L E).range ▸
        this ▸ fixingSubgroup_bot
  refine eq_bot_iff.mpr fun ⟨x, hx₁⟩ hx₂ => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ : x in Set.range (algebraMap L E) := by
refine mem_bot.mp (IsGalois.mem_bot_iff_fixed _).mpr fun φ => ?_
    rw [← restrictRestrictAlgEquivMapHom_apply K L φ ⟨x]; rw [hx₁⟩]
    rw [mem_fixedField_iff] at hx₂
exact congr_arg ((↑) : K -> E) hx₂ (restrictRestrictAlgEquivMapHom F K L E φ) ⟨φ, rfl⟩
  obtain ⟨z, rfl⟩ : y in (⊥ : IntermediateField F E) := h ▸ mem_inf.mpr ⟨hx₁, hy⟩
  exact mem_bot.mp ⟨z, rfl⟩

/--
theorem `map_fixingSubgroup` / 定理 `map_fixingSubgroup`

English:
theorem map_fixingSubgroup
  given: [Normal F E]
  proof: by
  ext f
  simp only [Subgroup.mem_comap, mem_fixingSubgroup_iff]
  constructor
  · rintro h x hx
    change f.restrictNormal E x = x
    apply_fun _ using (algebraMap E E').injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    replace h := 

中文:
定理 map_fixingSubgroup
  条件: [正规 F E]
  证明: by
  ext f
  simp only [Subgroup.mem_comap, mem_fixingSubgroup_iff]
  constructor
  · rintro h x hx
    change f.restrictNormal E x = x
    apply_fun _ using (algebraMap E E').injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    replace h := 

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormal_commutes, Subgroup, Subgroup.mem_comap, algebraMap, apply_fun, f.restrictNormal, injective, mem_comap, mem_fixingSubgroup_iff, replace, restrictNormal, restrictNormal_commutes
-/
theorem map_fixingSubgroup [Normal F E] :
    (L.map (IsScalarTower.toAlgHom F E E')).fixingSubgroup =
      L.fixingSubgroup.comap (AlgEquiv.restrictNormalHom (F := F) (K₁ := E') E) := by
  ext f
  simp only [Subgroup.mem_comap, mem_fixingSubgroup_iff]
  constructor
  · rintro h x hx
    change f.restrictNormal E x = x
    apply_fun _ using (algebraMap E E').injective
    rw [AlgEquiv.restrictNormal_commutes]
    exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    replace h := congr(algebraMap E E' $(show f.restrictNormal E x = x from h x hx))
    rwa [AlgEquiv.restrictNormal_commutes] at h

/--
theorem `map_fixingSubgroup_index` / 定理 `map_fixingSubgroup_index`

English:
theorem map_fixingSubgroup_index
  given: [Normal F E] [Normal F E']
  proof: by
  rw [L.map_fixingSubgroup E']; rw [L.fixingSubgroup.index_comap_of_surjective
    (AlgEquiv.restrictNormalHom_surjective _)]

中文:
定理 map_fixingSubgroup_index
  条件: [正规 F E] [正规 F E']
  证明: by
  rw [L.map_fixingSubgroup E']; rw [L.fixingSubgroup.index_comap_of_surjective
    (AlgEquiv.restrictNormalHom_surjective _)]

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom_surjective, L.fixingSubgroup.index_comap_of_surjective, L.map_fixingSubgroup, fixingSubgroup, index_comap_of_surjective, map_fixingSubgroup, restrictNormalHom_surjective
-/
theorem map_fixingSubgroup_index [Normal F E] [Normal F E'] :
    (L.map (IsScalarTower.toAlgHom F E E')).fixingSubgroup.index = L.fixingSubgroup.index := by
  rw [L.map_fixingSubgroup E']; rw [L.fixingSubgroup.index_comap_of_surjective
    (AlgEquiv.restrictNormalHom_surjective _)]

variable {K} in
/--
theorem `finrank_eq_fixingSubgroup_index` / 定理 `finrank_eq_fixingSubgroup_index`

English:
theorem finrank_eq_fixingSubgroup_index
  given: (L : IntermediateField F E') [IsGalois F E']
  proof: by
  wlog hnfd : FiniteDimensional F L generalizing L
  · rw [Module.finrank_of_infinite_dimensional hnfd]
    by_contra! h
    replace h : L.fixingSubgroup.FiniteIndex := ⟨h.symm⟩
    obtain ⟨L', hfd, hL'⟩ :=
      exists_lt_finrank_of_infinite_dimensional hnfd L.fixingSubgroup.index
    let i := (

中文:
定理 finrank_eq_fixingSubgroup_index
  条件: (L : 中间域 F E') [是Galois F E']
  证明: by
  wlog hnfd : FiniteDimensional F L generalizing L
  · rw [Module.finrank_of_infinite_dimensional hnfd]
    by_contra! h
    replace h : L.fixingSubgroup.FiniteIndex := ⟨h.symm⟩
    obtain ⟨L', hfd, hL'⟩ :=
      exists_lt_finrank_of_infinite_dimensional hnfd L.fixingSubgroup.index
    let i := (

Depends on / 依赖: FiniteDimensional, FiniteIndex, IntermediateField, IntermediateField.lift_le, L.fixingSubgroup.FiniteIndex, L.fixingSubgroup.index, Module, Module.finrank_of_infinite_dimensional, Subgroup, Subgroup.index_antitone, exists_lt_finrank_of_infinite_dimensional, finiteDimensional, finrank_eq, finrank_of_infinite_dimensional, fixingSubgroup, fixingSubgroup_le, generalizing, h.symm, i.finiteDimensional, i.finrank_eq
-/
theorem finrank_eq_fixingSubgroup_index (L : IntermediateField F E') [IsGalois F E'] :
    Module.finrank F L = L.fixingSubgroup.index := by
  wlog hnfd : FiniteDimensional F L generalizing L
  · rw [Module.finrank_of_infinite_dimensional hnfd]
    by_contra! h
    replace h : L.fixingSubgroup.FiniteIndex := ⟨h.symm⟩
    obtain ⟨L', hfd, hL'⟩ :=
      exists_lt_finrank_of_infinite_dimensional hnfd L.fixingSubgroup.index
    let i := (liftAlgEquiv L').toLinearEquiv
    replace hfd := i.finiteDimensional
    rw [i.finrank_eq]; rw [this _ hfd] at hL'
    exact (Subgroup.index_antitone <| fixingSubgroup_le <|
      IntermediateField.lift_le L').not_gt hL'
  let E := normalClosure F L E'
  have hle : L <= E := by simpa only [fieldRange_val] using L.val.fieldRange_le_normalClosure
  let L' := restrict hle
  have h := Module.finrank_mul_finrank F ↥L' ↥E
  classical
  rw [← IsGalois.card_fixingSubgroup_eq_finrank L']; rw [← IsGalois.card_aut_eq_finrank F E] at h
  rw [← L'.fixingSubgroup.index_mul_card]; rw [Nat.mul_left_inj Finite.card_pos.ne'] at h
  rw [(restrictAlgEquiv hle).toLinearEquiv.finrank_eq]; rw [h]; rw [← L'.map_fixingSubgroup_index E']
  congr 2
  exact lift_restrict hle

end IntermediateField

end restrictRestrictAlgEquivMapHom

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [IsQuadraticExtension F K]

/--
Instance `IsQuadraticExtension.isGalois` / 实例 `IsQuadraticExtension.isGalois`

English:
instance IsQuadraticExtension.isGalois
  signature: [Algebra.IsSeparable F K]

中文:
实例 是QuadraticExtension.isGalois
  签名: [代数.是可分 F K]
-/
instance IsQuadraticExtension.isGalois [Algebra.IsSeparable F K] : IsGalois F K where

/--
Instance `IsQuadraticExtension.isCyclic` / 实例 `IsQuadraticExtension.isCyclic`

English:
instance IsQuadraticExtension.isCyclic
  signature: : IsCyclic Gal(K/F)
  body: by
  have := finrank_eq_two F K ▸ AlgEquiv.card_le
  rw [← Nat.card_eq_fintype_card] at this
  interval_cases h : Nat.card Gal(K/F)
  · simp_all
  · exact @isCyclic_of_subsingleton _ _ (Finite.card_le_one_iff_subsingleton.mp h.le)
  · exact isCyclic_of_prime_card h

@[deprecated inferInstance (since

中文:
实例 是QuadraticExtension.isCyclic
  签名: : 是循环 Gal(K/F)
  定义体: by
  have := finrank_eq_two F K ▸ AlgEquiv.card_le
  rw [← Nat.card_eq_fintype_card] at this
  interval_cases h : Nat.card Gal(K/F)
  · simp_all
  · exact @isCyclic_of_subsingleton _ _ (Finite.card_le_one_iff_subsingleton.mp h.le)
  · exact isCyclic_of_prime_card h

@[deprecated inferInstance (since

Depends on / 依赖: AlgEquiv, AlgEquiv.card_le, Finite, Finite.card_le_one_iff_subsingleton.mp, Nat.card, Nat.card_eq_fintype_card, card_eq_fintype_card, card_le, card_le_one_iff_subsingleton, finrank_eq_two, h.le, interval_cases, isCyclic_of_prime_card, isCyclic_of_subsingleton
-/
instance IsQuadraticExtension.isCyclic : IsCyclic Gal(K/F) := by
  have := finrank_eq_two F K ▸ AlgEquiv.card_le
  rw [← Nat.card_eq_fintype_card] at this
  interval_cases h : Nat.card Gal(K/F)
  · simp_all
  · exact @isCyclic_of_subsingleton _ _ (Finite.card_le_one_iff_subsingleton.mp h.le)
  · exact isCyclic_of_prime_card h

@[deprecated inferInstance (since := "2026-04-09")]
/--
theorem `IsQuadraticExtension.isMulCommutative_galoisGroup` / 定理 `IsQuadraticExtension.isMulCommutative_galoisGroup`

English:
theorem IsQuadraticExtension.isMulCommutative_galoisGroup
  statement: IsMulCommutative Gal(K/F)
  proof: inferInstance

中文:
定理 是QuadraticExtension.isMulCommutative_galoisGroup
  结论: 是MulCommutative Gal(K/F)
  证明: inferInstance
-/
theorem IsQuadraticExtension.isMulCommutative_galoisGroup : IsMulCommutative Gal(K/F) :=
  inferInstance

end Algebra
