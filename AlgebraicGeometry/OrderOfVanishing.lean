/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`.
-/

@[expose] public section

open WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X]

/--
Order of vanishing on a locally Noetherian integral scheme as a monoid with zero hom to `ℤᵐ⁰`.
-/
noncomputable
/--
Definition of `ordHom` / `ordHom` 的定义

English:
definition ordHom
  signature: (z : X) (hz : coheight z = 1)
  body: haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  Ring.ordFrac (X.presheaf.stalk z)

中文:
定义 ordHom
  签名: (z : X) (hz : coheight z = 1)
  定义体: haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  Ring.ordFrac (X.presheaf.stalk z)

Depends on / 依赖: KrullDimLE, Ring.KrullDimLE, Ring.ordFrac, X.presheaf.stalk, hz.le, krullDimLE_of_coheight_le, ordFrac, presheaf
-/
def ordHom (z : X) (hz : coheight z = 1) : X.functionField ->*₀ Intᵐ⁰ :=
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  Ring.ordFrac (X.presheaf.stalk z)

/--
lemma `ordHom_of_isUnit` / 引理 `ordHom_of_isUnit`

English:
lemma ordHom_of_isUnit
  statement: {U : X.Opens}
  proof: by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← algebraMap_germ_eq_germToFunctionField _ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

中文:
引理 ordHom_of_isUnit
  结论: {U : X.Opens}
  证明: by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← algebraMap_germ_eq_germToFunctionField _ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

Depends on / 依赖: KrullDimLE, Ring.KrullDimLE, Ring.ordFrac_of_isUnit, X.presheaf.germ, X.presheaf.stalk, algebraMap_germ_eq_germToFunctionField, hf.map, hx.le, krullDimLE_of_coheight_le, ordFrac_of_isUnit, presheaf
-/
lemma ordHom_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x in U) :
    ordHom x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← algebraMap_germ_eq_germToFunctionField _ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

/--
The order of vanishing of an element of the function field of a locally Noetherian integral scheme
at a point. This has a junk value of `0` if `f = 0` or if `coheight z ≠ 1`.
-/
@[no_expose]
noncomputable
/--
Definition of `ord` / `ord` 的定义

English:
definition ord
  signature: (f : X.functionField) (z : X)
  body: if hz : coheight z = 1
then Multiplicative.toAdd (X.ordHom z hz f).unzeroD 1
  else 0

中文:
定义 ord
  签名: (f : X.functionField) (z : X)
  定义体: if hz : coheight z = 1
then Multiplicative.toAdd (X.ordHom z hz f).unzeroD 1
  else 0

Depends on / 依赖: Multiplicative, Multiplicative.toAdd, X.ordHom, coheight, ordHom, unzeroD
-/
def ord (f : X.functionField) (z : X) : Int :=
  if hz : coheight z = 1
then Multiplicative.toAdd (X.ordHom z hz f).unzeroD 1
  else 0

/--
lemma `ord_eq_ordHom_of_coheight_eq_one` / 引理 `ord_eq_ordHom_of_coheight_eq_one`

English:
lemma ord_eq_ordHom_of_coheight_eq_one
  given: {z : X} (hz : coheight z = 1) (f : X.functionField)
  proof: dif_pos hz

@[simp]

中文:
引理 ord_eq_ordHom_of_coheight_eq_one
  条件: {z : X} (hz : coheight z = 1) (f : X.functionField)
  证明: dif_pos hz

@[simp]

Depends on / 依赖: dif_pos
-/
lemma ord_eq_ordHom_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.functionField) :
    ord f z = Multiplicative.toAdd ((X.ordHom z hz f).unzeroD 1) := dif_pos hz

@[simp]
/--
lemma `ord_eq_zero_of_coheight_neq_one` / 引理 `ord_eq_zero_of_coheight_neq_one`

English:
lemma ord_eq_zero_of_coheight_neq_one
  given: {z : X} (hz : coheight z != 1) (f : X.functionField)
  proof: dif_neg hz

@[simp]

中文:
引理 ord_eq_zero_of_coheight_neq_one
  条件: {z : X} (hz : coheight z != 1) (f : X.functionField)
  证明: dif_neg hz

@[simp]

Depends on / 依赖: dif_neg
-/
lemma ord_eq_zero_of_coheight_neq_one {z : X} (hz : coheight z != 1) (f : X.functionField) :
    ord f z = 0 := dif_neg hz

@[simp]
/--
lemma `ord_zero` / 引理 `ord_zero`

English:
lemma ord_zero
  statement: ord (0 : X.functionField) = 0
  proof: by
  ext z
  by_cases h : coheight z = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one h, unzeroD]
  · simp [h]

中文:
引理 ord_zero
  结论: ord (0 : X.functionField) = 0
  证明: by
  ext z
  by_cases h : coheight z = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one h, unzeroD]
  · simp [h]

Depends on / 依赖: coheight, ord_eq_ordHom_of_coheight_eq_one, unzeroD
-/
lemma ord_zero : ord (0 : X.functionField) = 0 := by
  ext z
  by_cases h : coheight z = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one h, unzeroD]
  · simp [h]

/--
lemma `ord_eq_unzero_ordHom` / 引理 `ord_eq_unzero_ordHom`

English:
lemma ord_eq_unzero_ordHom
  given: {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f != 0)
  proof: by
  simp [ord, hx, unzeroD_eq_unzero ((map_ne_zero (ordHom x hx)).mpr hf)]

中文:
引理 ord_eq_unzero_ordHom
  条件: {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f != 0)
  证明: by
  simp [ord, hx, unzeroD_eq_unzero ((map_ne_zero (ordHom x hx)).mpr hf)]

Depends on / 依赖: map_ne_zero, ordHom, unzeroD_eq_unzero
-/
lemma ord_eq_unzero_ordHom {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f != 0) :
    ord f x = (WithZero.unzero ((map_ne_zero (ordHom x hx)).mpr hf)).toAdd := by
  simp [ord, hx, unzeroD_eq_unzero ((map_ne_zero (ordHom x hx)).mpr hf)]

/--
lemma `ord_eq_iff` / 引理 `ord_eq_iff`

English:
lemma ord_eq_iff
  given: {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f != 0) {n : Int}
  proof: by
  rw [ord_eq_unzero_ordHom hz hf]
  exact WithZero.toAdd_unzero_eq_iff _ _

@[simp]

中文:
引理 ord_eq_iff
  条件: {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f != 0) {n : 整数}
  证明: by
  rw [ord_eq_unzero_ordHom hz hf]
  exact WithZero.toAdd_unzero_eq_iff _ _

@[simp]

Depends on / 依赖: WithZero, WithZero.toAdd_unzero_eq_iff, ord_eq_unzero_ordHom, toAdd_unzero_eq_iff
-/
lemma ord_eq_iff {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f != 0) {n : Int} :
    ord f z = n ↔ ordHom z hz f = Multiplicative.ofAdd n := by
  rw [ord_eq_unzero_ordHom hz hf]
  exact WithZero.toAdd_unzero_eq_iff _ _

@[simp]
/--
lemma `ord_mul` / 引理 `ord_mul`

English:
lemma ord_mul
  statement: {x : X} {f g : X.functionField}
  proof: by
  by_cases! hx : coheight x != 1
  · simp [hx]
  rw [ord_eq_iff hx <| (mul_ne_zero_iff_right hg).mpr hf]
  simp [hf, hg, ord_eq_ordHom_of_coheight_eq_one hx, unzeroD_eq_unzero]

中文:
引理 ord_mul
  结论: {x : X} {f g : X.functionField}
  证明: by
  by_cases! hx : coheight x != 1
  · simp [hx]
  rw [ord_eq_iff hx <| (mul_ne_zero_iff_right hg).mpr hf]
  simp [hf, hg, ord_eq_ordHom_of_coheight_eq_one hx, unzeroD_eq_unzero]

Depends on / 依赖: coheight, mul_ne_zero_iff_right, ord_eq_iff, ord_eq_ordHom_of_coheight_eq_one, unzeroD_eq_unzero
-/
lemma ord_mul {x : X} {f g : X.functionField}
    (hf : f != 0) (hg : g != 0) : ord (f * g) x = ord f x + ord g x := by
  by_cases! hx : coheight x != 1
  · simp [hx]
  rw [ord_eq_iff hx <| (mul_ne_zero_iff_right hg).mpr hf]
  simp [hf, hg, ord_eq_ordHom_of_coheight_eq_one hx, unzeroD_eq_unzero]

/--
lemma `ord_of_isUnit` / 引理 `ord_of_isUnit`

English:
lemma ord_of_isUnit
  statement: {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X}
  proof: by
  by_cases! hx : coheight x != 1
  · simp [hx]
  simp [map_ne_zero_iff, germToFunctionField_injective, IsUnit.ne_zero hf,
    ord_eq_iff hx, ordHom_of_isUnit hf hx hx']

中文:
引理 ord_of_isUnit
  结论: {U : X.Opens} [非空 U] {f : Γ(X, U)} (hf : 是单位 f) {x : X}
  证明: by
  by_cases! hx : coheight x != 1
  · simp [hx]
  simp [map_ne_zero_iff, germToFunctionField_injective, IsUnit.ne_zero hf,
    ord_eq_iff hx, ordHom_of_isUnit hf hx hx']

Depends on / 依赖: IsUnit, IsUnit.ne_zero, coheight, germToFunctionField_injective, map_ne_zero_iff, ne_zero, ordHom_of_isUnit, ord_eq_iff
-/
lemma ord_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X}
    (hx' : x in U) : ord (X.germToFunctionField U f) x = 0 := by
  by_cases! hx : coheight x != 1
  · simp [hx]
  simp [map_ne_zero_iff, germToFunctionField_injective, IsUnit.ne_zero hf,
    ord_eq_iff hx, ordHom_of_isUnit hf hx hx']

/--
lemma `ord_le_ord_iff` / 引理 `ord_le_ord_iff`

English:
lemma ord_le_ord_iff
  statement: {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
  proof: by
  simp [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg, Multiplicative.toAdd_le]

中文:
引理 ord_le_ord_iff
  结论: {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
  证明: by
  simp [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg, Multiplicative.toAdd_le]

Depends on / 依赖: Multiplicative, Multiplicative.toAdd_le, ord_eq_unzero_ordHom, toAdd_le
-/
lemma ord_le_ord_iff {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
    (hf : f != 0) (hg : g != 0) :
    ord f x <= ord g y ↔ ordHom x hx f <= ordHom y hy g := by
  simp [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg, Multiplicative.toAdd_le]

/--
lemma `le_ord_iff` / 引理 `le_ord_iff`

English:
lemma le_ord_iff
  statement: {x : X} (hx : coheight x = 1) {f : X.functionField}
  proof: by
  rw [ord_eq_unzero_ordHom hx hf]
  nth_rw 1 [← toAdd_ofAdd n]
  rw [Multiplicative.toAdd_le]; rw [le_unzero_iff]

中文:
引理 le_ord_iff
  结论: {x : X} (hx : coheight x = 1) {f : X.functionField}
  证明: by
  rw [ord_eq_unzero_ordHom hx hf]
  nth_rw 1 [← toAdd_ofAdd n]
  rw [Multiplicative.toAdd_le]; rw [le_unzero_iff]

Depends on / 依赖: Multiplicative, Multiplicative.toAdd_le, le_unzero_iff, nth_rw, ord_eq_unzero_ordHom, toAdd_le, toAdd_ofAdd
-/
lemma le_ord_iff {x : X} (hx : coheight x = 1) {f : X.functionField}
    (hf : f != 0) {n : Int} :
    n <= ord f x ↔ Multiplicative.ofAdd n <= ordHom x hx f := by
  rw [ord_eq_unzero_ordHom hx hf]
  nth_rw 1 [← toAdd_ofAdd n]
  rw [Multiplicative.toAdd_le]; rw [le_unzero_iff]

/--
lemma `ord_add` / 引理 `ord_add`

English:
lemma ord_add
  statement: {x : X} [IsDiscreteValuationRing (X.presheaf.stalk x)]
  proof: by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases! hx : coheight x != 1
  · simp [hx]
  rw [inf_le_iff]; rw [ord_le_ord_iff hx hx hf hfg]; rw [ord_le_ord_iff hx hx hg hfg]
exact inf_le_iff.mp Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg

中文:
引理 ord_add
  结论: {x : X} [是离散赋值环 (X.presheaf.stalk x)]
  证明: by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases! hx : coheight x != 1
  · simp [hx]
  rw [inf_le_iff]; rw [ord_le_ord_iff hx hx hf hfg]; rw [ord_le_ord_iff hx hx hg hfg]
exact inf_le_iff.mp Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg

Depends on / 依赖: Ring.ordFrac_add, X.presheaf.stalk, coheight, inf_le_iff, inf_le_iff.mp, ordFrac_add, ord_le_ord_iff, presheaf
-/
lemma ord_add {x : X} [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f g : X.functionField} (hfg : f + g != 0) :
    min (ord f x) (ord g x) <= ord (f + g) x := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases! hx : coheight x != 1
  · simp [hx]
  rw [inf_le_iff]; rw [ord_le_ord_iff hx hx hf hfg]; rw [ord_le_ord_iff hx hx hg hfg]
exact inf_le_iff.mp Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg

/--
lemma `ord_le_smul` / 引理 `ord_le_smul`

English:
lemma ord_le_smul
  statement: {x : X} {U : X.Opens} [Nonempty U] (hxU : x in U)
  proof: by
  by_cases! hx : coheight x != 1
  · simp [hx]
  by_cases hf : f = 0
  · simp [hf]
  have : a • f != 0 := by simp [ha, Algebra.smul_def, hf, germToFunctionField_injective,
    RingHom.algebraMap_toAlgebra, map_ne_zero_iff]
  rw [ord_le_ord_iff hx hx hf this]
  algebraize [(X.presheaf.germ U x hxU

中文:
引理 ord_le_smul
  结论: {x : X} {U : X.Opens} [非空 U] (hxU : x in U)
  证明: by
  by_cases! hx : coheight x != 1
  · simp [hx]
  by_cases hf : f = 0
  · simp [hf]
  have : a • f != 0 := by simp [ha, Algebra.smul_def, hf, germToFunctionField_injective,
    RingHom.algebraMap_toAlgebra, map_ne_zero_iff]
  rw [ord_le_ord_iff hx hx hf this]
  algebraize [(X.presheaf.germ U x hxU

Depends on / 依赖: Algebra, Algebra.smul_def, IsScalarTower, KrullDimLE, Ring.KrullDimLE, RingHom, RingHom.algebraMap_toAlgebra, X.functionField, X.presheaf.germ, X.presheaf.stalk, algebraMap_toAlgebra, algebraize, coheight, functionField, functionField_isScalarTower, germToFunctionField_injective, hx.le, krullDimLE_of_coheight_le, map_ne_zero_iff, ordHom
-/
lemma ord_le_smul {x : X} {U : X.Opens} [Nonempty U] (hxU : x in U)
    {a : Γ(X, U)} (ha : a != 0) (f : X.functionField) : ord f x <= ord (a • f) x := by
  by_cases! hx : coheight x != 1
  · simp [hx]
  by_cases hf : f = 0
  · simp [hf]
  have : a • f != 0 := by simp [ha, Algebra.smul_def, hf, germToFunctionField_injective,
    RingHom.algebraMap_toAlgebra, map_ne_zero_iff]
  rw [ord_le_ord_iff hx hx hf this]
  algebraize [(X.presheaf.germ U x hxU).hom]
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑X.functionField :=
    functionField_isScalarTower X U ⟨x, hxU⟩
  simp [ordHom, Ring.ordFrac_le_smul, RingHom.algebraMap_toAlgebra, map_ne_zero_iff,
    germ_injective_of_isIntegral, ha]

end AlgebraicGeometry.Scheme
