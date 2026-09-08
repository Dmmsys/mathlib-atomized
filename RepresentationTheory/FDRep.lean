/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided  -- shake: keep (`example`)
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# `FDRep k G` is the category of finite-dimensional `k`-linear representations of `G`.

If `V : FDRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `Module k V` and `FiniteDimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We prove Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is
`0` if they are not isomorphic, and `1` if they are.
This is the content of `finrank_hom_simple_simple`

We verify that `FDRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`FDRep k G` has all finite limits.

## Implementation notes

We define `FDRep R G` for any ring `R` and monoid `G`,
as the category of finitely generated `R`-linear representations of `G`.

The main case of interest is when `R = k` is a field and `G` is a group,
and this is reflected in the documentation.

## TODO
* `FdRep k G ≌ FullSubcategory (FiniteDimensional k)`
* `FdRep k G` has all finite colimits.
* `FdRep k G` is abelian.
* `FdRep k G ≌ FGModuleCat k[G]`.

-/

@[expose] public section

suppress_compilation

universe u v

open CategoryTheory

open CategoryTheory.Limits


/-- The category of finitely generated `R`-linear representations of a monoid `G`.

Note that `R` can be any ring,
but the main case of interest is when `R = k` is a field and `G` is a group. -/
/-
**FDRep** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：FDRep (R : Type u) (G : Type v) [Ring R] [Monoid G]
参数：R : Type u；G : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finitely generated `R`-linear representations of a monoid `G`.

Note that `R` can be any ring,
but the main case of interest is when `R = k` is a field and `G` is a group.
-/
abbrev FDRep (R : Type u) (G : Type v) [Ring R] [Monoid G] :=
  Action (FGModuleCat.{u} R) G

namespace FDRep

variable {R k : Type u} {G : Type v} [CommRing R] [Field k] [Monoid G]

/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {G : Type u} [Monoid G] : LargeCategory (FDRep R G) := by infer_instance
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ConcreteCategory (FDRep R G) (Action.HomSubtype _ _) := by infer_instance
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Preadditive (FDRep R G) := by infer_instance
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasFiniteLimits (FDRep k G) := by infer_instance
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Linear R (FDRep R G) := by infer_instance
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (FDRep R G) (Type u) :=
  ⟨fun V => V.V⟩
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (V : FDRep R G) : Module.Finite R V := by infer_instance

/-- All hom spaces are finite dimensional. -/
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All hom spaces are finite dimensional.
-/
instance (V W : FDRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective (forget₂ (FDRep k G) (FGModuleCat k)))

/-- The monoid homomorphism corresponding to the action of `G` onto `V : FDRep R G`. -/
/-
**FDRep.** 是 Mathlib 中的一个定义，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoid homomorphism corresponding to the action of `G` onto `V : FDRep R G`.
-/
def ρ (V : FDRep R G) : G →* V →ₗ[R] V :=
  (ModuleCat.endRingEquiv _).toMonoidHom.comp
    (InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V))

@[simp]
/-
**FDRep.endRingEquiv_symm_comp_** 是 Mathlib 中的一个引理，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma endRingEquiv_symm_comp_ρ (V : FDRep R G) :
    (MonoidHomClass.toMonoidHom (ModuleCat.endRingEquiv V.V.obj).symm).comp (ρ V) =
      InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V) :=
  rfl
/-
**FDRep.endRingEquiv_comp_** 是 Mathlib 中的一个引理，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma endRingEquiv_comp_ρ (V : FDRep R G) :
    (MonoidHomClass.toMonoidHom (ModuleCat.endRingEquiv V.V.obj)).comp
      (InducedCategory.endEquiv.toMonoidHom.comp (Action.ρ V)) = ρ V :=
  rfl

@[simp]
/-
**FDRep.hom_hom_action_** 是 Mathlib 中的一个引理，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_hom_action_ρ (V : FDRep R G) (g : G) : (Action.ρ V g).hom.hom = (ρ V g) := rfl

/-- The underlying `LinearEquiv` of an isomorphism of representations. -/
/-
**FDRep.isoToLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FDRep`。
形式化陈述：isoToLinearEquiv {V W : FDRep R G} (i : V ≅ W) : V ≃ₗ[R] W
参数：i : V ≅ W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying `LinearEquiv` of an isomorphism of representations.
-/
def isoToLinearEquiv {V W : FDRep R G} (i : V ≅ W) : V ≃ₗ[R] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat R) G).mapIso i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**FDRep.Iso.conj_** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.conj_ρ {V W : FDRep R G} (i : V ≅ W) (g : G) :
    W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g) := by
  rw [FDRep.isoToLinearEquiv, ← hom_hom_action_ρ V, ← FGModuleCat.Iso.conj_hom_eq_conj,
    Iso.conj_apply, ← ModuleCat.hom_ofHom (W.ρ g), ← ModuleCat.hom_ext_iff]
  dsimp only [Action.forget_map, Functor.mapIso_hom]
  rw [i.hom.comm g]
  cat_disch

/-- Lift an unbundled representation to `FDRep`. -/
@[simps ρ]
/-
**FDRep.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `FDRep`。
形式化陈述：of {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V] (ρ : Rep
resentation R G V) : FDRep R G
参数：ρ : Representation R G V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an unbundled representation to `FDRep`.
-/
abbrev of {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    (ρ : Representation R G V) : FDRep R G :=
  ⟨FGModuleCat.of R V, (MulEquiv.toMonoidHom (MulEquiv.symm InducedCategory.endEquiv)).comp
    ((ModuleCat.endRingEquiv (ModuleCat.of R V)).symm.toMonoidHom.comp ρ)⟩

/-- This lemma is about `FDRep.ρ`, instead of `Action.ρ` for `of_ρ`. -/
@[simp]
/-
**FDRep.of_** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma is about `FDRep.ρ`, instead of `Action.ρ` for `of_ρ`.
-/
theorem of_ρ' {V : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V] (ρ : G →* V →ₗ[R] V) :
    (of ρ).ρ = ρ := rfl
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasForget₂ (FDRep R G) (Rep R G) where
  forget₂ := (forget₂ (FGModuleCat R) (ModuleCat R)).mapAction G ⋙ Rep.ActionToRep R G
/-
**FDRep.forget** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_ρ (V : FDRep R G) : ((forget₂ (FDRep R G) (Rep R G)).obj V).ρ = V.ρ := by
  ext g v; rfl
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherianRing R] : PreservesFiniteLimits (forget₂ (FDRep R G) (Rep R G)) :=
  Limits.comp_preservesFiniteLimits _ _
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteColimits (forget₂ (FDRep R G) (Rep R G)) :=
  Limits.comp_preservesFiniteColimits _ _

-- Verify that the monoidal structure is available.
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : MonoidalCategory (FDRep R G) := by infer_instance
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : MonoidalPreadditive (FDRep R G) := by infer_instance
/-
**FDRep.** 是 Mathlib 中的一个示例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : MonoidalLinear R (FDRep R G) := by infer_instance

open Module

-- We need to provide this instance explicitly as otherwise `finrank_hom_simple_simple` gives a
-- deterministic timeout.
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasKernels (FDRep k G) := by infer_instance

open scoped Classical in
/-- Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is `0` if
they are not isomorphic, and `1` if they are. -/
/-
**FDRep.finrank_hom_simple_simple** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Si
mple W] : finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0
参数：V W : FDRep k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.finrank_hom_simple_simple`：finrank_hom_simple_simple (X Y
 : C) [forall X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] [Simple X] [Simple Y] : finr
ank 𝕜 (X ⟶ Y) = if Nonempty (X…
· 使用定理 `FDRep.instHasKernels`：∀ {k : Type u} {G : Type v} [inst : Field k] [inst
_1 : Monoid G], CategoryTheory.Limits.HasKernels (FDRep k G)
· 使用定理 `FDRep.instFiniteDimensionalHom`：∀ {k : Type u} {G : Type v} [inst : Fiel
d k] [inst_1 : Monoid G] (V W : FDRep k G), FiniteDimensional k (V ⟶ W)

--- 原说明 ---
Schur's Lemma: the dimension of the `Hom`-space between two irreducible represen
tation is `0` if
they are not isomorphic, and `1` if they are.
-/
theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W

/-- The forgetful functor to `Rep k G` preserves hom-sets and their vector space structure. -/
/-
**FDRep.forget** 是 Mathlib 中的一个定义，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor to `Rep k G` preserves hom-sets and their vector space str
ucture.
-/
def forget₂HomLinearEquiv (X Y : FDRep R G) :
    ((forget₂ (FDRep R G) (Rep R G)).obj X ⟶
      (forget₂ (FDRep R G) (Rep R G)).obj Y) ≃ₗ[R] X ⟶ Y where
  toFun f := ⟨InducedCategory.homMk (ModuleCat.ofHom <| f.hom.toLinearMap), fun g ↦ by
    ext1
    simp only [FGModuleCat.obj_carrier]
    exact f.hom.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨((forget₂ (FGModuleCat R) (ModuleCat R)).map f.hom).hom, fun g ↦ by
    ext x
    exact ConcreteCategory.congr_hom ((forget (FGModuleCat R)).congr_map (f.comm g)) x⟩
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (FDRep R G) (Rep R G)).Full := by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance
/-
**FDRep.** 是 Mathlib 中的一个实例，位于命名空间 `FDRep`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget₂ (FDRep R G) (Rep R G)).Faithful := by
  dsimp [forget₂, HasForget₂.forget₂]
  infer_instance

end FDRep

namespace FDRep

-- The variables in this section are slightly weird, living half in `Representation` and half in
-- `FDRep`. When we have a better API for general monoidal closed and rigid categories and these
-- structures on `FDRep`, we should remove the dependency of statements about `FDRep` on
-- `Representation.linHom` and `Representation.dual`. The isomorphism `dualTensorIsoLinHom`
-- below should then just be obtained from general results about rigid categories.
open Representation

variable {k : Type u} {G : Type v} {V : Type u} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]
variable (ρV : Representation k G V) (W : FDRep k G)

open scoped MonoidalCategory

/-- Auxiliary definition for `FDRep.dualTensorIsoLinHom`. -/
/-
**FDRep.dualTensorIsoLinHomAux** 是 Mathlib 中的一个定义，位于命名空间 `FDRep`。
形式化陈述：dualTensorIsoLinHomAux : (FDRep.of ρV.dual otimes W).V ≅ (FDRep.of (linHom
 ρV W.ρ)).V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `FDRep.dualTensorIsoLinHom`.
-/
noncomputable def dualTensorIsoLinHomAux :
    (FDRep.of ρV.dual ⊗ W).V ≅ (FDRep.of (linHom ρV W.ρ)).V :=
  LinearEquiv.toFGModuleCatIso (dualTensorHomEquiv k V W)

/-- When `V` and `W` are finite-dimensional representations of a group `G`, the isomorphism
`dualTensorHomEquiv k V W` of vector spaces induces an isomorphism of representations. -/
/-
**FDRep.dualTensorIsoLinHom** 是 Mathlib 中的一个定义，位于命名空间 `FDRep`。
形式化陈述：dualTensorIsoLinHom : FDRep.of ρV.dual otimes W ≅ FDRep.of (linHom ρV W.ρ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `V` and `W` are finite-dimensional representations of a group `G`, the isom
orphism
`dualTensorHomEquiv k V W` of vector spaces induces an isomorphism of representa
tions.
-/
noncomputable def dualTensorIsoLinHom : FDRep.of ρV.dual ⊗ W ≅ FDRep.of (linHom ρV W.ρ) := by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) (fun g => ?_)
  ext : 1
  exact dualTensorHom_comm ρV W.ρ g

@[simp]
/-
**FDRep.dualTensorIsoLinHom_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `FDRep`。
形式化陈述：dualTensorIsoLinHom_hom_hom : (dualTensorIsoLinHom ρV W).hom.hom = Concret
eCategory.ofHom (dualTensorHom k V W)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FGModuleCat.instIsMonoidalModuleCatIsFG`：∀ (R : Type u) [inst : CommRing
 R], (ModuleCat.isFG R).IsMonoidal
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `FGModuleCat.instFiniteCarrier`：∀ (R : Type u) [inst : Ring R] (V : FGMod
uleCat R), Module.Finite R ↑V
-/
theorem dualTensorIsoLinHom_hom_hom :
    (dualTensorIsoLinHom ρV W).hom.hom = ConcreteCategory.ofHom (dualTensorHom k V W) :=
  rfl

end FDRep

