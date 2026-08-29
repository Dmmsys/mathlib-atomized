/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Over

/-!

# Residue Field of local rings

We prove basic properties of the residue field of a local ring.

-/

@[expose] public section

variable {R S T : Type*}

namespace IsLocalRing

section

variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]

/--
lemma `residue_def` / 引理 `residue_def`

English:
lemma residue_def
  given: (x)
  statement: residue R x = Ideal.Quotient.mk (maximalIdeal R) x
  proof: rfl

中文:
引理 residue_def
  条件: (x)
  结论: residue R x = 理想.商.mk (maximalIdeal R) x
  证明: rfl
-/
lemma residue_def (x) : residue R x = Ideal.Quotient.mk (maximalIdeal R) x := rfl

/--
lemma `ker_residue` / 引理 `ker_residue`

English:
lemma ker_residue
  statement: RingHom.ker (residue R) = maximalIdeal R
  proof: Ideal.mk_ker

@[simp]

中文:
引理 ker_residue
  结论: 环态射.ker (residue R) = maximalIdeal R
  证明: Ideal.mk_ker

@[simp]

Depends on / 依赖: Ideal.mk_ker, mk_ker
-/
lemma ker_residue : RingHom.ker (residue R) = maximalIdeal R :=
  Ideal.mk_ker

@[simp]
/--
lemma `residue_eq_zero_iff` / 引理 `residue_eq_zero_iff`

English:
lemma residue_eq_zero_iff
  given: (x : R)
  statement: residue R x = 0 ↔ x in maximalIdeal R
  proof: by
  rw [← RingHom.mem_ker]; rw [ker_residue]

中文:
引理 residue_eq_zero_iff
  条件: (x : R)
  结论: residue R x = 0 ↔ x in maximalIdeal R
  证明: by
  rw [← RingHom.mem_ker]; rw [ker_residue]

Depends on / 依赖: RingHom, RingHom.mem_ker, ker_residue, mem_ker
-/
lemma residue_eq_zero_iff (x : R) : residue R x = 0 ↔ x in maximalIdeal R := by
  rw [← RingHom.mem_ker]; rw [ker_residue]

/--
lemma `residue_ne_zero_iff_isUnit` / 引理 `residue_ne_zero_iff_isUnit`

English:
lemma residue_ne_zero_iff_isUnit
  given: (x : R)
  statement: residue R x != 0 ↔ IsUnit x
  proof: by
  simp

中文:
引理 residue_ne_zero_iff_isUnit
  条件: (x : R)
  结论: residue R x != 0 ↔ 是单位 x
  证明: by
  simp
-/
lemma residue_ne_zero_iff_isUnit (x : R) : residue R x != 0 ↔ IsUnit x := by
  simp

/--
lemma `residue_surjective` / 引理 `residue_surjective`

English:
lemma residue_surjective
  proof: Ideal.Quotient.mk_surjective

中文:
引理 residue_surjective
  证明: Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective
-/
lemma residue_surjective :
    Function.Surjective (IsLocalRing.residue R) :=
  Ideal.Quotient.mk_surjective

variable (R)

/--
Instance `ResidueField.algebra` / 实例 `ResidueField.algebra`

English:
instance ResidueField.algebra
  signature: {R₀} [CommRing R₀] [Algebra R₀ R]
  body: inferInstanceAs Algebra R₀ (_ ⧸ _)

中文:
实例 ResidueField.algebra
  签名: {R₀} [交换环 R₀] [代数 R₀ R]
  定义体: inferInstanceAs Algebra R₀ (_ ⧸ _)

Depends on / 依赖: Algebra
-/
instance ResidueField.algebra {R₀} [CommRing R₀] [Algebra R₀ R] :
    Algebra R₀ (ResidueField R) :=
inferInstanceAs Algebra R₀ (_ ⧸ _)

instance {R₁ R₂} [CommRing R₁] [CommRing R₂]
    [Algebra R₁ R₂] [Algebra R₁ R] [Algebra R₂ R] [IsScalarTower R₁ R₂ R] :
    IsScalarTower R₁ R₂ (ResidueField R) :=
inferInstanceAs IsScalarTower R₁ R₂ (_ ⧸ _)

@[simp]
/--
theorem `ResidueField.algebraMap_eq` / 定理 `ResidueField.algebraMap_eq`

English:
theorem ResidueField.algebraMap_eq
  statement: algebraMap R (ResidueField R) = residue R
  proof: rfl

中文:
定理 ResidueField.algebraMap_eq
  结论: algebraMap R (ResidueField R) = residue R
  证明: rfl
-/
theorem ResidueField.algebraMap_eq : algebraMap R (ResidueField R) = residue R :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsLocalHom (IsLocalRing.residue R)
  body: ⟨fun _ ha =>
    Classical.not_not.mp (Ideal.Quotient.eq_zero_iff_mem.not.mp (isUnit_iff_ne_zero.mp ha))⟩

#adaptation_note /-- Needed after leanprover/lean4#12564 -/

中文:
实例 :
  签名: 是Local态射 (是局部环.residue R)
  定义体: ⟨fun _ ha =>
    Classical.not_not.mp (Ideal.Quotient.eq_zero_iff_mem.not.mp (isUnit_iff_ne_zero.mp ha))⟩

#adaptation_note /-- Needed after leanprover/lean4#12564 -/

Depends on / 依赖: Classical, Classical.not_not.mp, Ideal.Quotient.eq_zero_iff_mem.not.mp, Quotient, eq_zero_iff_mem, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mp, not_not
-/
instance : IsLocalHom (IsLocalRing.residue R) :=
  ⟨fun _ ha =>
    Classical.not_not.mp (Ideal.Quotient.eq_zero_iff_mem.not.mp (isUnit_iff_ne_zero.mp ha))⟩

#adaptation_note /-- Needed after leanprover/lean4#12564 -/
noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] : Module R₀ (ResidueField R) :=
inferInstanceAs Module R₀ (R ⧸ maximalIdeal R)

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Module.Finite R₀ R] :
    Module.Finite R₀ (ResidueField R) :=
  .of_surjective (IsScalarTower.toAlgHom R₀ R _).toLinearMap Ideal.Quotient.mk_surjective

variable {R}

namespace ResidueField

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R ->+* S) [IsLocalHom f]
  body: Ideal.Quotient.lift _ f fun a ha =>
    by_contradiction fun h => ha (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))

中文:
定义 lift
  签名: {R S : 类型} [交换环 R] [是局部环 R] [域 S] (f : R ->+* S) [是Local态射 f]
  定义体: Ideal.Quotient.lift _ f fun a ha =>
    by_contradiction fun h => ha (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))

Depends on / 依赖: Ideal.Quotient.lift, Quotient, by_contradiction, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr, isUnit_of_map_unit
-/
def lift {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R ->+* S) [IsLocalHom f] :
    IsLocalRing.ResidueField R ->+* S :=
  Ideal.Quotient.lift _ f fun a ha =>
    by_contradiction fun h => ha (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))

/--
theorem `lift_comp_residue` / 定理 `lift_comp_residue`

English:
theorem lift_comp_residue
  statement: {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R ->+* S)
  proof: RingHom.ext fun _ => rfl

@[simp]

中文:
定理 lift_comp_residue
  结论: {R S : 类型} [交换环 R] [是局部环 R] [域 S] (f : R ->+* S)
  证明: RingHom.ext fun _ => rfl

@[simp]

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem lift_comp_residue {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R ->+* S)
    [IsLocalHom f] : (lift f).comp (residue R) = f :=
  RingHom.ext fun _ => rfl

@[simp]
/--
theorem `lift_residue_apply` / 定理 `lift_residue_apply`

English:
theorem lift_residue_apply
  statement: {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R ->+* S)
  proof: rfl

中文:
定理 lift_residue_apply
  结论: {R S : 类型} [交换环 R] [是局部环 R] [域 S] (f : R ->+* S)
  证明: rfl
-/
theorem lift_residue_apply {R S : Type*} [CommRing R] [IsLocalRing R] [Field S] (f : R ->+* S)
    [IsLocalHom f] (x) : lift f (residue R x) = f x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S) [IsLocalHom f]
  body: Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    unfold ResidueField
    rw [RingHom.comp_apply]; rw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha

中文:
定义 map
  签名: (f : R ->+* S) [是Local态射 f]
  定义体: Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    unfold ResidueField
    rw [RingHom.comp_apply]; rw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.lift, Ideal.Quotient.mk, Quotient, ResidueField, RingHom, RingHom.comp_apply, comp_apply, eq_zero_iff_mem, map_nonunit, maximalIdeal
-/
noncomputable def map (f : R ->+* S) [IsLocalHom f] : ResidueField R ->+* ResidueField S :=
  Ideal.Quotient.lift (maximalIdeal R) ((Ideal.Quotient.mk _).comp f) fun a ha => by
    unfold ResidueField
    rw [RingHom.comp_apply]; rw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_nonunit f a ha

/-- Applying `IsLocalRing.ResidueField.map` to the identity ring homomorphism gives the identity
ring homomorphism. -/
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  proof: Ideal.Quotient.ringHom_ext RingHom.ext fun _ => rfl

中文:
定理 map_id
  证明: Ideal.Quotient.ringHom_ext RingHom.ext fun _ => rfl

Depends on / 依赖: Ideal.Quotient.ringHom_ext, Quotient, RingHom, RingHom.ext, ringHom_ext
-/
theorem map_id :
    IsLocalRing.ResidueField.map (RingHom.id R) = RingHom.id (IsLocalRing.ResidueField R) :=
Ideal.Quotient.ringHom_ext RingHom.ext fun _ => rfl

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : T ->+* R) (g : R ->+* S) [IsLocalHom f] [IsLocalHom g]
  proof: Ideal.Quotient.ringHom_ext RingHom.ext fun _ => rfl

中文:
定理 map_comp
  条件: (f : T ->+* R) (g : R ->+* S) [是Local态射 f] [是Local态射 g]
  证明: Ideal.Quotient.ringHom_ext RingHom.ext fun _ => rfl

Depends on / 依赖: Ideal.Quotient.ringHom_ext, Quotient, RingHom, RingHom.ext, ringHom_ext
-/
theorem map_comp (f : T ->+* R) (g : R ->+* S) [IsLocalHom f] [IsLocalHom g] :
    IsLocalRing.ResidueField.map (g.comp f) =
      (IsLocalRing.ResidueField.map g).comp (IsLocalRing.ResidueField.map f) :=
Ideal.Quotient.ringHom_ext RingHom.ext fun _ => rfl

/--
theorem `map_comp_residue` / 定理 `map_comp_residue`

English:
theorem map_comp_residue
  given: (f : R ->+* S) [IsLocalHom f]
  proof: rfl

@[simp]

中文:
定理 map_comp_residue
  条件: (f : R ->+* S) [是Local态射 f]
  证明: rfl

@[simp]
-/
theorem map_comp_residue (f : R ->+* S) [IsLocalHom f] :
    (ResidueField.map f).comp (residue R) = (residue S).comp f :=
  rfl

@[simp]
/--
theorem `map_residue` / 定理 `map_residue`

English:
theorem map_residue
  given: (f : R ->+* S) [IsLocalHom f] (r : R)
  proof: rfl

中文:
定理 map_residue
  条件: (f : R ->+* S) [是Local态射 f] (r : R)
  证明: rfl
-/
theorem map_residue (f : R ->+* S) [IsLocalHom f] (r : R) :
    ResidueField.map f (residue R r) = residue S (f r) :=
  rfl

/--
theorem `map_id_apply` / 定理 `map_id_apply`

English:
theorem map_id_apply
  given: (x : ResidueField R)
  statement: map (RingHom.id R) x = x
  proof: DFunLike.congr_fun map_id x

@[simp]

中文:
定理 map_id_apply
  条件: (x : ResidueField R)
  结论: map (环态射.id R) x = x
  证明: DFunLike.congr_fun map_id x

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_id
-/
theorem map_id_apply (x : ResidueField R) : map (RingHom.id R) x = x :=
  DFunLike.congr_fun map_id x

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  statement: (f : R ->+* S) (g : S ->+* T) (x : ResidueField R) [IsLocalHom f]
  proof: DFunLike.congr_fun (map_comp f g).symm x

中文:
定理 map_map
  结论: (f : R ->+* S) (g : S ->+* T) (x : ResidueField R) [是Local态射 f]
  证明: DFunLike.congr_fun (map_comp f g).symm x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp
-/
theorem map_map (f : R ->+* S) (g : S ->+* T) (x : ResidueField R) [IsLocalHom f]
    [IsLocalHom g] : map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp f g).symm x

/-- A ring isomorphism defines an isomorphism of residue fields. -/
@[simps apply]
/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (f : R ≃+* S)
  body: map (f : R ->+* S)
  invFun := map (f.symm : S ->+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]

中文:
定义 mapEquiv
  签名: (f : R ≃+* S)
  定义体: map (f : R ->+* S)
  invFun := map (f.symm : S ->+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
-/
noncomputable def mapEquiv (f : R ≃+* S) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S where
  toFun := map (f : R ->+* S)
  invFun := map (f.symm : S ->+* R)
  left_inv x := by simp only [map_map, RingEquiv.symm_comp, map_id, RingHom.id_apply]
  right_inv x := by simp only [map_map, RingEquiv.comp_symm, map_id, RingHom.id_apply]
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
/--
theorem `mapEquiv.symm` / 定理 `mapEquiv.symm`

English:
theorem mapEquiv.symm
  given: (f : R ≃+* S)
  statement: (mapEquiv f).symm = mapEquiv f.symm
  proof: rfl

@[simp]

中文:
定理 mapEquiv.symm
  条件: (f : R ≃+* S)
  结论: (mapEquiv f).symm = mapEquiv f.symm
  证明: rfl

@[simp]
-/
theorem mapEquiv.symm (f : R ≃+* S) : (mapEquiv f).symm = mapEquiv f.symm :=
  rfl

@[simp]
/--
theorem `mapEquiv_trans` / 定理 `mapEquiv_trans`

English:
theorem mapEquiv_trans
  given: (e₁ : R ≃+* S) (e₂ : S ≃+* T)
  proof: RingEquiv.toRingHom_injective map_comp (e₁ : R ->+* S) (e₂ : S ->+* T)

@[simp]

中文:
定理 mapEquiv_trans
  条件: (e₁ : R ≃+* S) (e₂ : S ≃+* T)
  证明: RingEquiv.toRingHom_injective map_comp (e₁ : R ->+* S) (e₂ : S ->+* T)

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.toRingHom_injective, map_comp, toRingHom_injective
-/
theorem mapEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    mapEquiv (e₁.trans e₂) = (mapEquiv e₁).trans (mapEquiv e₂) :=
RingEquiv.toRingHom_injective map_comp (e₁ : R ->+* S) (e₂ : S ->+* T)

@[simp]
/--
theorem `mapEquiv_refl` / 定理 `mapEquiv_refl`

English:
theorem mapEquiv_refl
  statement: mapEquiv (RingEquiv.refl R) = RingEquiv.refl _
  proof: RingEquiv.toRingHom_injective map_id

中文:
定理 mapEquiv_refl
  结论: mapEquiv (环等价.refl R) = 环等价.refl _
  证明: RingEquiv.toRingHom_injective map_id

Depends on / 依赖: RingEquiv, RingEquiv.toRingHom_injective, map_id, toRingHom_injective
-/
theorem mapEquiv_refl : mapEquiv (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.toRingHom_injective map_id

/-- The group homomorphism from `RingAut R` to `RingAut k` where `k`
is the residue field of `R`. -/
@[simps]
/--
Definition of `mapAut` / `mapAut` 的定义

English:
definition mapAut
  signature: : RingAut R ->* RingAut (IsLocalRing.ResidueField R) where
  body: mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl

中文:
定义 mapAut
  签名: : RingAut R ->* RingAut (是局部环.ResidueField R) where
  定义体: mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl

Depends on / 依赖: mapEquiv
-/
noncomputable def mapAut : RingAut R ->* RingAut (IsLocalRing.ResidueField R) where
  toFun := mapEquiv
  map_mul' e₁ e₂ := mapEquiv_trans e₂ e₁
  map_one' := mapEquiv_refl

section MulSemiringAction

variable (G : Type*) [Group G] [MulSemiringAction G R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module (ResidueField R) (ResidueField S)
  body: inferInstanceAs Module (R ⧸ maximalIdeal R) (S ⧸ maximalIdeal S)

中文:
实例 :
  签名: 模 (ResidueField R) (ResidueField S)
  定义体: inferInstanceAs Module (R ⧸ maximalIdeal R) (S ⧸ maximalIdeal S)

Depends on / 依赖: Module, maximalIdeal
-/
noncomputable instance : Module (ResidueField R) (ResidueField S) :=
inferInstanceAs Module (R ⧸ maximalIdeal R) (S ⧸ maximalIdeal S)

/--
Instance `finite_of_module_finite` / 实例 `finite_of_module_finite`

English:
instance finite_of_module_finite
  signature: [Module.Finite R S]
  body: .of_restrictScalars_finite R _ _

中文:
实例 finite_of_module_finite
  签名: [模.有限 R S]
  定义体: .of_restrictScalars_finite R _ _

Depends on / 依赖: of_restrictScalars_finite
-/
instance finite_of_module_finite [Module.Finite R S] :
    Module.Finite (ResidueField R) (ResidueField S) :=
  .of_restrictScalars_finite R _ _

/--
lemma `finite_of_finite` / 引理 `finite_of_finite`

English:
lemma finite_of_finite
  given: [Module.Finite R S] (hfin : Finite (ResidueField R))
  proof: Module.finite_of_finite (ResidueField R)

中文:
引理 finite_of_finite
  条件: [模.有限 R S] (hfin : 有限 (ResidueField R))
  证明: Module.finite_of_finite (ResidueField R)

Depends on / 依赖: Module, Module.finite_of_finite, ResidueField, finite_of_finite
-/
lemma finite_of_finite [Module.Finite R S] (hfin : Finite (ResidueField R)) :
    Finite (ResidueField S) := Module.finite_of_finite (ResidueField R)

end FiniteDimensional

omit [IsLocalRing R]

variable [Algebra R S] [Algebra R T]

/--
Definition of `mapAlgHom` / `mapAlgHom` 的定义

English:
definition mapAlgHom
  signature: (e : S ->ₐ[R] T) [IsLocalHom e]
  body: map e
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (ResidueField S),
      IsScalarTower.algebraMap_apply R T (ResidueField T)]

@[simp]

中文:
定义 mapAlgHom
  签名: (e : S ->ₐ[R] T) [是Local态射 e]
  定义体: map e
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (ResidueField S),
      IsScalarTower.algebraMap_apply R T (ResidueField T)]

@[simp]
-/
noncomputable def mapAlgHom (e : S ->ₐ[R] T) [IsLocalHom e] :
    ResidueField S ->ₐ[R] ResidueField T where
  __ := map e
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (ResidueField S),
      IsScalarTower.algebraMap_apply R T (ResidueField T)]

@[simp]
/--
theorem `mapAlgHom_residue` / 定理 `mapAlgHom_residue`

English:
theorem mapAlgHom_residue
  given: (e : S ->ₐ[R] T) [IsLocalHom e] (x : S)
  proof: rfl

中文:
定理 mapAlgHom_residue
  条件: (e : S ->ₐ[R] T) [是Local态射 e] (x : S)
  证明: rfl
-/
theorem mapAlgHom_residue (e : S ->ₐ[R] T) [IsLocalHom e] (x : S) :
    mapAlgHom e (residue S x) = residue T (e x) :=
  rfl

/--
Definition of `mapAlgEquiv` / `mapAlgEquiv` 的定义

English:
definition mapAlgEquiv
  signature: (e : S ≃ₐ[R] T)
  body: mapAlgHom e.toAlgHom
  __ := mapEquiv e.toRingEquiv

@[simp]

中文:
定义 mapAlgEquiv
  签名: (e : S ≃ₐ[R] T)
  定义体: mapAlgHom e.toAlgHom
  __ := mapEquiv e.toRingEquiv

@[simp]

Depends on / 依赖: e.toAlgHom, mapAlgHom, toAlgHom
-/
noncomputable def mapAlgEquiv (e : S ≃ₐ[R] T) : ResidueField S ≃ₐ[R] ResidueField T where
  __ := mapAlgHom e.toAlgHom
  __ := mapEquiv e.toRingEquiv

@[simp]
/--
theorem `mapAlgEquiv_residue` / 定理 `mapAlgEquiv_residue`

English:
theorem mapAlgEquiv_residue
  given: (e : S ≃ₐ[R] T) (x : S)
  proof: rfl

中文:
定理 mapAlgEquiv_residue
  条件: (e : S ≃ₐ[R] T) (x : S)
  证明: rfl
-/
theorem mapAlgEquiv_residue (e : S ≃ₐ[R] T) (x : S) :
    mapAlgEquiv e (residue S x) = residue T (e x) :=
  rfl

variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap R T)]

/--
Definition of `mapAlgHom'` / `mapAlgHom'` 的定义

English:
definition mapAlgHom'
  signature: (e : S ->ₐ[R] T) [IsLocalHom e]
  body: (mapAlgHom e).extendScalarsOfSurjective residue_surjective

@[simp]

中文:
定义 mapAlgHom'
  签名: (e : S ->ₐ[R] T) [是Local态射 e]
  定义体: (mapAlgHom e).extendScalarsOfSurjective residue_surjective

@[simp]

Depends on / 依赖: extendScalarsOfSurjective, mapAlgHom, residue_surjective
-/
noncomputable def mapAlgHom' (e : S ->ₐ[R] T) [IsLocalHom e] :
    ResidueField S ->ₐ[ResidueField R] ResidueField T :=
  (mapAlgHom e).extendScalarsOfSurjective residue_surjective

@[simp]
/--
theorem `mapAlgHom'_residue` / 定理 `mapAlgHom'_residue`

English:
theorem mapAlgHom'_residue
  given: [IsLocalRing R] (e : S ->ₐ[R] T) [IsLocalHom e] (x : S)
  proof: rfl

中文:
定理 mapAlgHom'_residue
  条件: [是局部环 R] (e : S ->ₐ[R] T) [是Local态射 e] (x : S)
  证明: rfl

Depends on / 依赖: ContinuousConstSMul, TopologicalSpace
-/
theorem mapAlgHom'_residue [IsLocalRing R] (e : S ->ₐ[R] T) [IsLocalHom e] (x : S) :
    mapAlgHom' e (residue S x) = residue T (e x) :=
  rfl

/--
Definition of `mapAlgEquiv'` / `mapAlgEquiv'` 的定义

English:
definition mapAlgEquiv'
  signature: (e : S ≃ₐ[R] T)
  body: (mapAlgEquiv e).extendScalarsOfSurjective residue_surjective

@[simp]

中文:
定义 mapAlgEquiv'
  签名: (e : S ≃ₐ[R] T)
  定义体: (mapAlgEquiv e).extendScalarsOfSurjective residue_surjective

@[simp]

Depends on / 依赖: MulAction, TopologicalSpace, extendScalarsOfSurjective, mapAlgEquiv, residue_surjective
-/
noncomputable def mapAlgEquiv' (e : S ≃ₐ[R] T) :
    ResidueField S ≃ₐ[ResidueField R] ResidueField T :=
  (mapAlgEquiv e).extendScalarsOfSurjective residue_surjective

@[simp]
/--
theorem `mapAlgEquiv'_residue` / 定理 `mapAlgEquiv'_residue`

English:
theorem mapAlgEquiv'_residue
  given: [IsLocalRing R] (e : S ≃ₐ[R] T) (x : S)
  proof: rfl

中文:
定理 mapAlgEquiv'_residue
  条件: [是局部环 R] (e : S ≃ₐ[R] T) (x : S)
  证明: rfl

Depends on / 依赖: isProperMap_smul, prodMap
-/
theorem mapAlgEquiv'_residue [IsLocalRing R] (e : S ≃ₐ[R] T) (x : S) :
    mapAlgEquiv' e (residue S x) = residue T (e x) :=
  rfl

end ResidueField

end

end IsLocalRing
