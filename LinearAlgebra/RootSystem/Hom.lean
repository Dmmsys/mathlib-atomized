/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Basic
public import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Morphisms of root pairings

This file defines morphisms of root pairings, following the definition of morphisms of root data
given in SGA III Exp. 21 Section 6.

## Main definitions:
* `Hom`: A morphism of root pairings is a linear map of weight spaces, its transverse on coweight
  spaces, and a bijection on the set that indexes roots and coroots.
* `Hom.id`: The identity morphism.
* `Hom.comp`: The composite of two morphisms.
* `End`: The endomorphism monoid of a root pairing.
* `Hom.weightHom`: The homomorphism from the endomorphism monoid to linear endomorphisms on the
  weight space.
* `Hom.coweightHom`: The homomorphism from the endomorphism monoid to the opposite monoid of linear
  endomorphisms on the coweight space.
* `Equiv`: An equivalence of root pairings is a morphism for which the maps on weight spaces and
  coweight spaces are bijective.
* `Equiv.toHom`: The morphism underlying an equivalence.
* `Equiv.weightEquiv`: The linear isomorphism on weight spaces given by an equivalence.
* `Equiv.coweightEquiv`: The linear isomorphism on coweight spaces given by an equivalence.
* `Equiv.id`: The identity equivalence.
* `Equiv.comp`: The composite of two equivalences.
* `Equiv.symm`: The inverse of an equivalence.
* `Aut`: The automorphism group of a root pairing.
* `Equiv.toEndUnit`: The group isomorphism between the automorphism group of a root pairing and the
  group of invertible endomorphisms.
* `Equiv.weightHom`: The homomorphism from the automorphism group to linear automorphisms on the
  weight space.
* `Equiv.coweightHom`: The homomorphism from the automorphism group to the opposite group of linear
  automorphisms on the coweight space.
* `Equiv.reflection`: The automorphism of a root pairing given by reflection in a root and
  coreflection in the corresponding coroot.

## TODO
* Special types of morphisms: Isogenies, weight/coweight space embeddings
* Weyl group reimplementation?

-/

@[expose] public section

open Set Function

noncomputable section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- A morphism of root pairings is a pair of mutually transposed maps of weight and coweight spaces
that preserves roots and coroots. We make the map of indexing sets explicit. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: {ι₂ M₂ N₂ : Type*}
  axioms and operations (6):
    - weightMap : M ->ₗ[R] M₂
    - coweightMap : N₂ ->ₗ[R] N
    - indexEquiv : ι ≃ ι₂
    - weight_coweight_transpose : weightMap.dualMap ∘ₗ Q.flip.toPerfPair = P.flip.toPerfPair ∘ₗ coweightMap
    - root_weightMap : weightMap ∘ P.root = Q.root ∘ indexEquiv
    - coroot_coweightMap : coweightMap ∘ Q.coroot = P.coroot ∘ indexEquiv.symm

中文:
结构 态射
  参数: {ι₂ M₂ N₂ : 类型}
  公理与运算 (6 个):
    - weightMap : M ->ₗ[R] M₂
    - coweightMap : N₂ ->ₗ[R] N
    - indexEquiv : ι ≃ ι₂
    - weight_coweight_transpose : weightMap.dualMap ∘ₗ Q.flip.toPerfPair = P.flip.toPerfPair ∘ₗ coweightMap
    - root_weightMap : weightMap ∘ P.root = Q.root ∘ indexEquiv
    - coroot_coweightMap : coweightMap ∘ Q.coroot = P.coroot ∘ indexEquiv.symm
-/
structure Hom {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) where
  /-- A linear map on weight space. -/
  weightMap : M ->ₗ[R] M₂
  /-- A contravariant linear map on coweight space. -/
  coweightMap : N₂ ->ₗ[R] N
  /-- A bijection on index sets. -/
  indexEquiv : ι ≃ ι₂
  weight_coweight_transpose :
    weightMap.dualMap ∘ₗ Q.flip.toPerfPair = P.flip.toPerfPair ∘ₗ coweightMap
  root_weightMap : weightMap ∘ P.root = Q.root ∘ indexEquiv
  coroot_coweightMap : coweightMap ∘ Q.coroot = P.coroot ∘ indexEquiv.symm

namespace Hom

/--
lemma `weight_coweight_transpose_apply` / 引理 `weight_coweight_transpose_apply`

English:
lemma weight_coweight_transpose_apply
  statement: {ι₂ M₂ N₂ : Type*}
  proof: Eq.mp (propext LinearMap.ext_iff) f.weight_coweight_transpose x

中文:
引理 weight_coweight_transpose_apply
  结论: {ι₂ M₂ N₂ : 类型}
  证明: Eq.mp (propext LinearMap.ext_iff) f.weight_coweight_transpose x

Depends on / 依赖: Eq.mp, LinearMap, LinearMap.ext_iff, ext_iff, f.weight_coweight_transpose, propext, weight_coweight_transpose
-/
lemma weight_coweight_transpose_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (x : N₂) (f : Hom P Q) :
    f.weightMap.dualMap (Q.flip.toPerfPair x) = P.flip.toPerfPair (f.coweightMap x) :=
  Eq.mp (propext LinearMap.ext_iff) f.weight_coweight_transpose x

/--
lemma `root_weightMap_apply` / 引理 `root_weightMap_apply`

English:
lemma root_weightMap_apply
  statement: {ι₂ M₂ N₂ : Type*}
  proof: Eq.mp (propext funext_iff) f.root_weightMap i

中文:
引理 root_weightMap_apply
  结论: {ι₂ M₂ N₂ : 类型}
  证明: Eq.mp (propext funext_iff) f.root_weightMap i

Depends on / 依赖: Eq.mp, f.root_weightMap, funext_iff, propext, root_weightMap
-/
lemma root_weightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι) (f : Hom P Q) :
    f.weightMap (P.root i) = Q.root (f.indexEquiv i) :=
  Eq.mp (propext funext_iff) f.root_weightMap i

/--
lemma `coroot_coweightMap_apply` / 引理 `coroot_coweightMap_apply`

English:
lemma coroot_coweightMap_apply
  statement: {ι₂ M₂ N₂ : Type*}
  proof: Eq.mp (propext funext_iff) f.coroot_coweightMap i

中文:
引理 coroot_coweightMap_apply
  结论: {ι₂ M₂ N₂ : 类型}
  证明: Eq.mp (propext funext_iff) f.coroot_coweightMap i

Depends on / 依赖: Eq.mp, coroot_coweightMap, f.coroot_coweightMap, funext_iff, propext
-/
lemma coroot_coweightMap_apply {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (i : ι₂) (f : Hom P Q) :
    f.coweightMap (Q.coroot i) = P.coroot (f.indexEquiv.symm i) :=
  Eq.mp (propext funext_iff) f.coroot_coweightMap i

/-- The identity morphism of a root pairing. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (P : RootPairing ι R M N)
  body: LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by simp
  root_weightMap := by simp
  coroot_coweightMap := by simp

中文:
定义 id
  签名: (P : RootPairing ι R M N)
  定义体: LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by simp
  root_weightMap := by simp
  coroot_coweightMap := by simp

Depends on / 依赖: LinearMap, LinearMap.id
-/
def id (P : RootPairing ι R M N) : Hom P P where
  weightMap := LinearMap.id
  coweightMap := LinearMap.id
  indexEquiv := Equiv.refl ι
  weight_coweight_transpose := by simp
  root_weightMap := by simp
  coroot_coweightMap := by simp

/-- Composition of morphisms -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
  body: g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  weight_coweight_transpose := by
    ext φ x
    rw [← LinearMap.dualMap_comp_dualMap]; rw [← LinearMap.comp_assoc _ f.coweightMap]; rw [← f.weight_coweight_transpose]; rw [Lin

中文:
定义 comp
  签名: {ι₁ M₁ N₁ ι₂ M₂ N₂ : 类型} [加法交换群 M₁] [模 R M₁] [加法交换群 N₁]
  定义体: g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  weight_coweight_transpose := by
    ext φ x
    rw [← LinearMap.dualMap_comp_dualMap]; rw [← LinearMap.comp_assoc _ f.coweightMap]; rw [← f.weight_coweight_transpose]; rw [Lin

Depends on / 依赖: f.weightMap, g.weightMap, weightMap
-/
def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : Hom P₁ P₂) (f : Hom P P₁) : Hom P P₂ where
  weightMap := g.weightMap ∘ₗ f.weightMap
  coweightMap := f.coweightMap ∘ₗ g.coweightMap
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  weight_coweight_transpose := by
    ext φ x
    rw [← LinearMap.dualMap_comp_dualMap]; rw [← LinearMap.comp_assoc _ f.coweightMap]; rw [← f.weight_coweight_transpose]; rw [LinearMap.comp_assoc g.coweightMap]; rw [← g.weight_coweight_transpose]; rw [← LinearMap.comp_assoc]
  root_weightMap := by
    ext i
    simp only [LinearMap.coe_comp, Equiv.coe_trans]
    rw [comp_assoc]; rw [f.root_weightMap]; rw [← comp_assoc]; rw [g.root_weightMap]; rw [comp_assoc]
  coroot_coweightMap := by
    ext i
    simp only [LinearMap.coe_comp]
    rw [comp_assoc]; rw [g.coroot_coweightMap]; rw [← comp_assoc]; rw [f.coroot_coweightMap]; rw [comp_assoc]
    simp

@[simp]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  statement: {ι₂ M₂ N₂ : Type*}
  proof: by
  ext x <;> simp

@[simp]

中文:
引理 id_comp
  结论: {ι₂ M₂ N₂ : 类型}
  证明: by
  ext x <;> simp

@[simp]
-/
lemma id_comp {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    comp f (id P) = f := by
  ext x <;> simp

@[simp]
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  statement: {ι₂ M₂ N₂ : Type*}
  proof: by
  ext x <;> simp

@[simp]

中文:
引理 comp_id
  结论: {ι₂ M₂ N₂ : 类型}
  证明: by
  ext x <;> simp

@[simp]
-/
lemma comp_id {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : Hom P Q) :
    comp (id Q) f = f := by
  ext x <;> simp

@[simp]
/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  proof: by
  ext <;> simp

中文:
引理 comp_assoc
  结论: {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : 类型} [加法交换群 M₁] [模 R M₁]
  证明: by
  ext <;> simp
-/
lemma comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃] {P : RootPairing ι R M N}
    {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃}
    (h : Hom P₂ P₃) (g : Hom P₁ P₂) (f : Hom P P₁) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp

/-- The endomorphism monoid of a root pairing. -/
instance (P : RootPairing ι R M N) : Monoid (Hom P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P

@[simp]
/--
lemma `weightMap_one` / 引理 `weightMap_one`

English:
lemma weightMap_one
  given: (P : RootPairing ι R M N)
  proof: rfl

@[simp]

中文:
引理 weightMap_one
  条件: (P : RootPairing ι R M N)
  证明: rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
lemma weightMap_one (P : RootPairing ι R M N) :
    weightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := M) :=
  rfl

@[simp]
/--
lemma `coweightMap_one` / 引理 `coweightMap_one`

English:
lemma coweightMap_one
  given: (P : RootPairing ι R M N)
  proof: rfl

@[simp]

中文:
引理 coweightMap_one
  条件: (P : RootPairing ι R M N)
  证明: rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
lemma coweightMap_one (P : RootPairing ι R M N) :
    coweightMap (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := N) :=
  rfl

@[simp]
/--
lemma `indexEquiv_one` / 引理 `indexEquiv_one`

English:
lemma indexEquiv_one
  given: (P : RootPairing ι R M N)
  proof: rfl

@[simp]

中文:
引理 indexEquiv_one
  条件: (P : RootPairing ι R M N)
  证明: rfl

@[simp]

Depends on / 依赖: Equiv.refl
-/
lemma indexEquiv_one (P : RootPairing ι R M N) :
    indexEquiv (P := P) (Q := P) 1 = Equiv.refl ι :=
  rfl

@[simp]
/--
lemma `weightMap_mul` / 引理 `weightMap_mul`

English:
lemma weightMap_mul
  given: (P : RootPairing ι R M N) (x y : Hom P P)
  proof: rfl

@[simp]

中文:
引理 weightMap_mul
  条件: (P : RootPairing ι R M N) (x y : 态射 P P)
  证明: rfl

@[simp]
-/
lemma weightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    weightMap (x * y) = weightMap x ∘ₗ weightMap y :=
  rfl

@[simp]
/--
lemma `coweightMap_mul` / 引理 `coweightMap_mul`

English:
lemma coweightMap_mul
  given: (P : RootPairing ι R M N) (x y : Hom P P)
  proof: rfl

@[simp]

中文:
引理 coweightMap_mul
  条件: (P : RootPairing ι R M N) (x y : 态射 P P)
  证明: rfl

@[simp]

Depends on / 依赖: AEMeasurable, IsZeroOrProbabilityMeasure, IsZeroOrProbabilityMeasure.measure_univ, isZeroOrProbabilityMeasure_iff, measure_univ
-/
lemma coweightMap_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    coweightMap (x * y) = coweightMap y ∘ₗ coweightMap x :=
  rfl

@[simp]
/--
lemma `indexEquiv_mul` / 引理 `indexEquiv_mul`

English:
lemma indexEquiv_mul
  given: (P : RootPairing ι R M N) (x y : Hom P P)
  proof: rfl

中文:
引理 indexEquiv_mul
  条件: (P : RootPairing ι R M N) (x y : 态射 P P)
  证明: rfl
-/
lemma indexEquiv_mul (P : RootPairing ι R M N) (x y : Hom P P) :
    indexEquiv (x * y) = indexEquiv x ∘ indexEquiv y :=
  rfl

/--
Definition of `_root_.RootPairing.End` / `_root_.RootPairing.End` 的定义

English:
abbreviation _root_.RootPairing.End
  signature: (P : RootPairing ι R M N)
  body: Hom P P

中文:
缩写 _root_.RootPairing.End
  签名: (P : RootPairing ι R M N)
  定义体: Hom P P
-/
abbrev _root_.RootPairing.End (P : RootPairing ι R M N) := Hom P P

/--
Definition of `weightHom` / `weightHom` 的定义

English:
definition weightHom
  signature: (P : RootPairing ι R M N)
  body: Hom.weightMap (P := P) (Q := P) g
  map_mul' g h := by ext; simp
  map_one' := by ext; simp

中文:
定义 weightHom
  签名: (P : RootPairing ι R M N)
  定义体: Hom.weightMap (P := P) (Q := P) g
  map_mul' g h := by ext; simp
  map_one' := by ext; simp

Depends on / 依赖: Hom.weightMap, weightMap
-/
def weightHom (P : RootPairing ι R M N) : End P ->* (Module.End R M) where
  toFun g := Hom.weightMap (P := P) (Q := P) g
  map_mul' g h := by ext; simp
  map_one' := by ext; simp

/--
lemma `weightHom_injective` / 引理 `weightHom_injective`

English:
lemma weightHom_injective
  given: (P : RootPairing ι R M N)
  statement: Injective (weightHom P)
  proof: by
  intro f g hfg
  ext x
  · exact LinearMap.congr_fun hfg x
  · refine LinearEquiv.injective P.flip.toPerfPair ?_
    simp_rw [← weight_coweight_transpose_apply]
    exact congrFun (congrArg DFunLike.coe (congrArg LinearMap.dualMap hfg)) (P.flip.toPerfPair x)
  · refine Embedding.injective P.root

中文:
引理 weightHom_injective
  条件: (P : RootPairing ι R M N)
  结论: 单射 (weightHom P)
  证明: by
  intro f g hfg
  ext x
  · exact LinearMap.congr_fun hfg x
  · refine LinearEquiv.injective P.flip.toPerfPair ?_
    simp_rw [← weight_coweight_transpose_apply]
    exact congrFun (congrArg DFunLike.coe (congrArg LinearMap.dualMap hfg)) (P.flip.toPerfPair x)
  · refine Embedding.injective P.root

Depends on / 依赖: DFunLike, DFunLike.coe, Embedding, Embedding.injective, LinearEquiv, LinearEquiv.injective, LinearMap, LinearMap.congr_fun, LinearMap.dualMap, P.flip.toPerfPair, P.root, congr_fun, dualMap, injective, root_weightMap_apply, simp_rw, toPerfPair, weight_coweight_transpose_apply
-/
lemma weightHom_injective (P : RootPairing ι R M N) : Injective (weightHom P) := by
  intro f g hfg
  ext x
  · exact LinearMap.congr_fun hfg x
  · refine LinearEquiv.injective P.flip.toPerfPair ?_
    simp_rw [← weight_coweight_transpose_apply]
    exact congrFun (congrArg DFunLike.coe (congrArg LinearMap.dualMap hfg)) (P.flip.toPerfPair x)
  · refine Embedding.injective P.root ?_
    simp_rw [← root_weightMap_apply]
    exact congrFun (congrArg DFunLike.coe hfg) (P.root x)

/--
Definition of `coweightHom` / `coweightHom` 的定义

English:
definition coweightHom
  signature: (P : RootPairing ι R M N)
  body: MulOpposite.op (Hom.coweightMap (P := P) (Q := P) g)
  map_mul' g h := by
    simp only [← MulOpposite.op_mul, coweightMap_mul, Module.End.mul_eq_comp]
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff, coweightMap_one, Module.End.one_eq_id]

中文:
定义 coweightHom
  签名: (P : RootPairing ι R M N)
  定义体: MulOpposite.op (Hom.coweightMap (P := P) (Q := P) g)
  map_mul' g h := by
    simp only [← MulOpposite.op_mul, coweightMap_mul, Module.End.mul_eq_comp]
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff, coweightMap_one, Module.End.one_eq_id]

Depends on / 依赖: Hom.coweightMap, MulOpposite, MulOpposite.op, coweightMap
-/
def coweightHom (P : RootPairing ι R M N) : End P ->* (N ->ₗ[R] N)ᵐᵒᵖ where
  toFun g := MulOpposite.op (Hom.coweightMap (P := P) (Q := P) g)
  map_mul' g h := by
    simp only [← MulOpposite.op_mul, coweightMap_mul, Module.End.mul_eq_comp]
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff, coweightMap_one, Module.End.one_eq_id]

/--
lemma `coweightHom_injective` / 引理 `coweightHom_injective`

English:
lemma coweightHom_injective
  given: (P : RootPairing ι R M N)
  statement: Injective (coweightHom P)
  proof: by
  intro f g hfg
  ext x
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    have h := congrArg (LinearMap.comp (M₃ := Module.Dual R M) (σ₂₃ := .id R) P.flip.toPerfPair) hfg
    rw [← f.weight_coweight_transpose]; rw [← g.weight_coweight_transpose] at h
    have : f.weightMap = g

中文:
引理 coweightHom_injective
  条件: (P : RootPairing ι R M N)
  结论: 单射 (coweightHom P)
  证明: by
  intro f g hfg
  ext x
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    have h := congrArg (LinearMap.comp (M₃ := Module.Dual R M) (σ₂₃ := .id R) P.flip.toPerfPair) hfg
    rw [← f.weight_coweight_transpose]; rw [← g.weight_coweight_transpose] at h
    have : f.weightMap = g

Depends on / 依赖: IsReflexive, LinearEquiv, LinearEquiv.eq_comp_toLinearMap_iff, LinearMap, LinearMap.comp, LinearMap.dualMap, Module, Module.Dual, Module.IsReflexive, Module.dualMap_dualMap_eq_iff, MulOpposite, MulOpposite.op_inj, P.flip.toPerfPair, P.toLinearMap, coweightHom, dualMap, dualMap_dualMap_eq_iff, eq_comp_toLinearMap_iff, f.weightMap, f.weightMap.dualMap
-/
lemma coweightHom_injective (P : RootPairing ι R M N) : Injective (coweightHom P) := by
  intro f g hfg
  ext x
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    have h := congrArg (LinearMap.comp (M₃ := Module.Dual R M) (σ₂₃ := .id R) P.flip.toPerfPair) hfg
    rw [← f.weight_coweight_transpose]; rw [← g.weight_coweight_transpose] at h
    have : f.weightMap = g.weightMap := by
      have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
      refine (Module.dualMap_dualMap_eq_iff R M).mp (congrArg LinearMap.dualMap
        ((LinearEquiv.eq_comp_toLinearMap_iff f.weightMap.dualMap g.weightMap.dualMap).mp h))
    exact congrFun (congrArg DFunLike.coe this) x
  · dsimp [coweightHom] at hfg
    simp_all
  · dsimp [coweightHom] at hfg
    rw [MulOpposite.op_inj] at hfg
    set y := f.indexEquiv x with hy
    have : f.coweightMap (P.coroot y) = g.coweightMap (P.coroot y) := by
      exact congrFun (congrArg DFunLike.coe hfg) (P.coroot y)
    rw [coroot_coweightMap_apply]; rw [coroot_coweightMap_apply]; rw [Embedding.apply_eq_iff_eq]; rw [hy] at this
    rw [Equiv.symm_apply_apply] at this
    rw [this]; rw [Equiv.apply_symm_apply]

/--
Definition of `indexHom` / `indexHom` 的定义

English:
definition indexHom
  signature: (P : RootPairing ι R M N)
  body: Hom.indexEquiv f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

中文:
定义 indexHom
  签名: (P : RootPairing ι R M N)
  定义体: Hom.indexEquiv f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

Depends on / 依赖: Hom.indexEquiv, indexEquiv
-/
def indexHom (P : RootPairing ι R M N) : End P ->* (ι ≃ ι) where
  toFun f := Hom.indexEquiv f
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

end Hom

variable {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)

/-- An equivalence of root pairings is a morphism where the maps of weight and coweight spaces are
bijective.

See also `RootPairing.Equiv.toEndUnit`. -/
@[ext]
/--
Definition of `Equiv` / `Equiv` 的定义

English:
structure Equiv
  parameters: extends Hom P Q
  extends: Hom P Q
  axioms and operations (2):
    - bijective_weightMap : Bijective weightMap
    - bijective_coweightMap : Bijective coweightMap

中文:
结构 等价
  参数: extends 态射 P Q
  继承: 态射 P Q
  公理与运算 (2 个):
    - bijective_weightMap : 双射 weightMap
    - bijective_coweightMap : 双射 coweightMap
-/
protected structure Equiv extends Hom P Q where
  bijective_weightMap : Bijective weightMap
  bijective_coweightMap : Bijective coweightMap

attribute [coe] Equiv.toHom

/-- The root pairing homomorphism underlying an equivalence. -/
add_decl_doc Equiv.toHom

namespace Equiv

/--
Definition of `weightEquiv` / `weightEquiv` 的定义

English:
definition weightEquiv
  signature: (e : RootPairing.Equiv P Q)
  body: LinearEquiv.ofBijective _ e.bijective_weightMap

@[simp]

中文:
定义 weightEquiv
  签名: (e : RootPairing.等价 P Q)
  定义体: LinearEquiv.ofBijective _ e.bijective_weightMap

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, bijective_weightMap, e.bijective_weightMap, ofBijective
-/
def weightEquiv (e : RootPairing.Equiv P Q) : M ≃ₗ[R] M₂ :=
    LinearEquiv.ofBijective _ e.bijective_weightMap

@[simp]
/--
lemma `weightEquiv_apply` / 引理 `weightEquiv_apply`

English:
lemma weightEquiv_apply
  given: (e : RootPairing.Equiv P Q) (m : M)
  proof: rfl

@[simp]

中文:
引理 weightEquiv_apply
  条件: (e : RootPairing.等价 P Q) (m : M)
  证明: rfl

@[simp]
-/
lemma weightEquiv_apply (e : RootPairing.Equiv P Q) (m : M) :
    weightEquiv P Q e m = e.toHom.weightMap m :=
  rfl

@[simp]
/--
lemma `weightEquiv_symm_weightMap` / 引理 `weightEquiv_symm_weightMap`

English:
lemma weightEquiv_symm_weightMap
  given: (e : RootPairing.Equiv P Q) (m : M)
  proof: (LinearEquiv.symm_apply_eq (weightEquiv P Q e)).mpr rfl

@[simp]

中文:
引理 weightEquiv_symm_weightMap
  条件: (e : RootPairing.等价 P Q) (m : M)
  证明: (LinearEquiv.symm_apply_eq (weightEquiv P Q e)).mpr rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq, weightEquiv
-/
lemma weightEquiv_symm_weightMap (e : RootPairing.Equiv P Q) (m : M) :
    (weightEquiv P Q e).symm (e.toHom.weightMap m) = m :=
  (LinearEquiv.symm_apply_eq (weightEquiv P Q e)).mpr rfl

@[simp]
/--
lemma `weightMap_weightEquiv_symm` / 引理 `weightMap_weightEquiv_symm`

English:
lemma weightMap_weightEquiv_symm
  given: (e : RootPairing.Equiv P Q) (m : M₂)
  proof: by
  rw [← weightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (weightEquiv P Q e) m

中文:
引理 weightMap_weightEquiv_symm
  条件: (e : RootPairing.等价 P Q) (m : M₂)
  证明: by
  rw [← weightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (weightEquiv P Q e) m

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, weightEquiv, weightEquiv_apply
-/
lemma weightMap_weightEquiv_symm (e : RootPairing.Equiv P Q) (m : M₂) :
    e.toHom.weightMap ((weightEquiv P Q e).symm m) = m := by
  rw [← weightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (weightEquiv P Q e) m

/--
Definition of `coweightEquiv` / `coweightEquiv` 的定义

English:
definition coweightEquiv
  signature: (e : RootPairing.Equiv P Q)
  body: LinearEquiv.ofBijective _ e.bijective_coweightMap

@[simp]

中文:
定义 coweightEquiv
  签名: (e : RootPairing.等价 P Q)
  定义体: LinearEquiv.ofBijective _ e.bijective_coweightMap

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, bijective_coweightMap, e.bijective_coweightMap, ofBijective
-/
def coweightEquiv (e : RootPairing.Equiv P Q) : N₂ ≃ₗ[R] N :=
  LinearEquiv.ofBijective _ e.bijective_coweightMap

@[simp]
/--
lemma `coweightEquiv_apply` / 引理 `coweightEquiv_apply`

English:
lemma coweightEquiv_apply
  given: (e : RootPairing.Equiv P Q) (n : N₂)
  proof: rfl

@[simp]

中文:
引理 coweightEquiv_apply
  条件: (e : RootPairing.等价 P Q) (n : N₂)
  证明: rfl

@[simp]
-/
lemma coweightEquiv_apply (e : RootPairing.Equiv P Q) (n : N₂) :
    coweightEquiv P Q e n = e.toHom.coweightMap n :=
  rfl

@[simp]
/--
lemma `coweightEquiv_symm_coweightMap` / 引理 `coweightEquiv_symm_coweightMap`

English:
lemma coweightEquiv_symm_coweightMap
  given: (e : RootPairing.Equiv P Q) (n : N₂)
  proof: (LinearEquiv.symm_apply_eq (coweightEquiv P Q e)).mpr rfl

@[simp]

中文:
引理 coweightEquiv_symm_coweightMap
  条件: (e : RootPairing.等价 P Q) (n : N₂)
  证明: (LinearEquiv.symm_apply_eq (coweightEquiv P Q e)).mpr rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, coweightEquiv, symm_apply_eq
-/
lemma coweightEquiv_symm_coweightMap (e : RootPairing.Equiv P Q) (n : N₂) :
    (coweightEquiv P Q e).symm (e.toHom.coweightMap n) = n :=
  (LinearEquiv.symm_apply_eq (coweightEquiv P Q e)).mpr rfl

@[simp]
/--
lemma `coweightMap_coweightEquiv_symm` / 引理 `coweightMap_coweightEquiv_symm`

English:
lemma coweightMap_coweightEquiv_symm
  given: (e : RootPairing.Equiv P Q) (n : N)
  proof: by
  rw [← coweightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (coweightEquiv P Q e) n

中文:
引理 coweightMap_coweightEquiv_symm
  条件: (e : RootPairing.等价 P Q) (n : N)
  证明: by
  rw [← coweightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (coweightEquiv P Q e) n

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, coweightEquiv, coweightEquiv_apply
-/
lemma coweightMap_coweightEquiv_symm (e : RootPairing.Equiv P Q) (n : N) :
    e.toHom.coweightMap ((coweightEquiv P Q e).symm n) = n := by
  rw [← coweightEquiv_apply]
  exact LinearEquiv.apply_symm_apply (coweightEquiv P Q e) n

/-- The identity equivalence of a root pairing. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (P : RootPairing ι R M N)
  body: { Hom.id P with
    bijective_weightMap := _root_.id bijective_id
    bijective_coweightMap := _root_.id bijective_id }

中文:
定义 id
  签名: (P : RootPairing ι R M N)
  定义体: { Hom.id P with
    bijective_weightMap := _root_.id bijective_id
    bijective_coweightMap := _root_.id bijective_id }

Depends on / 依赖: Hom.id, _root_, _root_.id, bijective_coweightMap, bijective_id, bijective_weightMap
-/
def id (P : RootPairing ι R M N) : RootPairing.Equiv P P :=
  { Hom.id P with
    bijective_weightMap := _root_.id bijective_id
    bijective_coweightMap := _root_.id bijective_id }

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
  body: { Hom.comp g.toHom f.toHom with
    bijective_weightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp g.bijective_weightMap f.bijective_weightMap
    bijective_coweightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp f.bijective_co

中文:
定义 comp
  签名: {ι₁ M₁ N₁ ι₂ M₂ N₂ : 类型} [加法交换群 M₁] [模 R M₁] [加法交换群 N₁]
  定义体: { Hom.comp g.toHom f.toHom with
    bijective_weightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp g.bijective_weightMap f.bijective_weightMap
    bijective_coweightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp f.bijective_co

Depends on / 依赖: Bijective, Bijective.comp, Hom.comp, LinearMap, LinearMap.coe_comp, bijective_coweightMap, bijective_weightMap, coe_comp, f.bijective_coweightMap, f.bijective_weightMap, f.toHom, g.bijective_coweightMap, g.bijective_weightMap, g.toHom
-/
def comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) : RootPairing.Equiv P P₂ :=
  { Hom.comp g.toHom f.toHom with
    bijective_weightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp g.bijective_weightMap f.bijective_weightMap
    bijective_coweightMap := by
      simp only [Hom.comp, LinearMap.coe_comp]
      exact Bijective.comp f.bijective_coweightMap g.bijective_coweightMap }

@[simp]
/--
lemma `toHom_comp` / 引理 `toHom_comp`

English:
lemma toHom_comp
  statement: {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
  proof: by
  rfl

@[simp]

中文:
引理 toHom_comp
  结论: {ι₁ M₁ N₁ ι₂ M₂ N₂ : 类型} [加法交换群 M₁] [模 R M₁] [加法交换群 N₁]
  证明: by
  rfl

@[simp]
-/
lemma toHom_comp {ι₁ M₁ N₁ ι₂ M₂ N₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup N₁]
    [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂}
    (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) :
    (Equiv.comp g f).toHom = Hom.comp g.toHom f.toHom := by
  rfl

@[simp]
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  statement: {ι₂ M₂ N₂ : Type*}
  proof: by
  ext x <;> simp

@[simp]

中文:
引理 id_comp
  结论: {ι₂ M₂ N₂ : 类型}
  证明: by
  ext x <;> simp

@[simp]
-/
lemma id_comp {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    comp f (id P) = f := by
  ext x <;> simp

@[simp]
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  statement: {ι₂ M₂ N₂ : Type*}
  proof: by
  ext x <;> simp

@[simp]

中文:
引理 comp_id
  结论: {ι₂ M₂ N₂ : 类型}
  证明: by
  ext x <;> simp

@[simp]
-/
lemma comp_id {ι₂ M₂ N₂ : Type*}
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    comp (id Q) f = f := by
  ext x <;> simp

@[simp]
/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  proof: by
  ext <;> simp

中文:
引理 comp_assoc
  结论: {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : 类型} [加法交换群 M₁] [模 R M₁]
  证明: by
  ext <;> simp
-/
lemma comp_assoc {ι₁ M₁ N₁ ι₂ M₂ N₂ ι₃ M₃ N₃ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup M₃] [Module R M₃] [AddCommGroup N₃] [Module R N₃] {P : RootPairing ι R M N}
    {P₁ : RootPairing ι₁ R M₁ N₁} {P₂ : RootPairing ι₂ R M₂ N₂} {P₃ : RootPairing ι₃ R M₃ N₃}
    (h : RootPairing.Equiv P₂ P₃) (g : RootPairing.Equiv P₁ P₂) (f : RootPairing.Equiv P P₁) :
    comp (comp h g) f = comp h (comp g f) := by
  ext <;> simp

/-- Equivalences form a monoid. -/
instance (P : RootPairing ι R M N) : Monoid (RootPairing.Equiv P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P

@[simp]
/--
lemma `weightEquiv_one` / 引理 `weightEquiv_one`

English:
lemma weightEquiv_one
  given: (P : RootPairing ι R M N)
  proof: rfl

@[simp]

中文:
引理 weightEquiv_one
  条件: (P : RootPairing ι R M N)
  证明: rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
lemma weightEquiv_one (P : RootPairing ι R M N) :
    weightEquiv (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := M) :=
  rfl

@[simp]
/--
lemma `coweightEquiv_one` / 引理 `coweightEquiv_one`

English:
lemma coweightEquiv_one
  given: (P : RootPairing ι R M N)
  proof: rfl

@[simp]

中文:
引理 coweightEquiv_one
  条件: (P : RootPairing ι R M N)
  证明: rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
lemma coweightEquiv_one (P : RootPairing ι R M N) :
    coweightEquiv (P := P) (Q := P) 1 = LinearMap.id (R := R) (M := N) :=
  rfl

@[simp]
/--
lemma `toHom_one` / 引理 `toHom_one`

English:
lemma toHom_one
  given: (P : RootPairing ι R M N)
  proof: rfl

@[simp]

中文:
引理 toHom_one
  条件: (P : RootPairing ι R M N)
  证明: rfl

@[simp]
-/
lemma toHom_one (P : RootPairing ι R M N) :
    (1 : RootPairing.Equiv P P).toHom = (1 : RootPairing.Hom P P) :=
  rfl

@[simp]
/--
lemma `mul_eq_comp` / 引理 `mul_eq_comp`

English:
lemma mul_eq_comp
  given: {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P)
  proof: rfl

@[simp]

中文:
引理 mul_eq_comp
  条件: {P : RootPairing ι R M N} (x y : RootPairing.等价 P P)
  证明: rfl

@[simp]
-/
lemma mul_eq_comp {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    x * y = Equiv.comp x y :=
  rfl

@[simp]
/--
lemma `weightEquiv_comp_toLin` / 引理 `weightEquiv_comp_toLin`

English:
lemma weightEquiv_comp_toLin
  given: {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P)
  proof: by
  ext; simp

@[simp]

中文:
引理 weightEquiv_comp_toLin
  条件: {P : RootPairing ι R M N} (x y : RootPairing.等价 P P)
  证明: by
  ext; simp

@[simp]
-/
lemma weightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    weightEquiv P P (Equiv.comp x y) = weightEquiv P P y ≪≫ₗ weightEquiv P P x := by
  ext; simp

@[simp]
/--
lemma `weightEquiv_mul` / 引理 `weightEquiv_mul`

English:
lemma weightEquiv_mul
  given: {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P)
  proof: by
  rfl

@[simp]

中文:
引理 weightEquiv_mul
  条件: {P : RootPairing ι R M N} (x y : RootPairing.等价 P P)
  证明: by
  rfl

@[simp]
-/
lemma weightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    weightEquiv P P x * weightEquiv P P y = weightEquiv P P y ≪≫ₗ weightEquiv P P x := by
  rfl

@[simp]
/--
lemma `coweightEquiv_comp_toLin` / 引理 `coweightEquiv_comp_toLin`

English:
lemma coweightEquiv_comp_toLin
  given: {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P)
  proof: by
  ext; simp

@[simp]

中文:
引理 coweightEquiv_comp_toLin
  条件: {P : RootPairing ι R M N} (x y : RootPairing.等价 P P)
  证明: by
  ext; simp

@[simp]
-/
lemma coweightEquiv_comp_toLin {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    coweightEquiv P P (Equiv.comp x y) = coweightEquiv P P x ≪≫ₗ coweightEquiv P P y := by
  ext; simp

@[simp]
/--
lemma `coweightEquiv_mul` / 引理 `coweightEquiv_mul`

English:
lemma coweightEquiv_mul
  given: {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P)
  proof: by
  rfl

中文:
引理 coweightEquiv_mul
  条件: {P : RootPairing ι R M N} (x y : RootPairing.等价 P P)
  证明: by
  rfl
-/
lemma coweightEquiv_mul {P : RootPairing ι R M N} (x y : RootPairing.Equiv P P) :
    coweightEquiv P P x * coweightEquiv P P y = coweightEquiv P P y ≪≫ₗ coweightEquiv P P x := by
  rfl

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  body: (weightEquiv P Q f).symm
  coweightMap := (coweightEquiv P Q f).symm
  indexEquiv := f.indexEquiv.symm
  weight_coweight_transpose := by
    ext n m
    nth_rw 2 [show m = (weightEquiv P Q f) ((weightEquiv P Q f).symm m) by
      exact (LinearEquiv.symm_apply_eq (weightEquiv P Q f)).mp rfl]
    nth_

中文:
定义 symm
  签名: {ι₂ M₂ N₂ : 类型} [加法交换群 M₂] [模 R M₂] [加法交换群 N₂] [模 R N₂]
  定义体: (weightEquiv P Q f).symm
  coweightMap := (coweightEquiv P Q f).symm
  indexEquiv := f.indexEquiv.symm
  weight_coweight_transpose := by
    ext n m
    nth_rw 2 [show m = (weightEquiv P Q f) ((weightEquiv P Q f).symm m) by
      exact (LinearEquiv.symm_apply_eq (weightEquiv P Q f)).mp rfl]
    nth_

Depends on / 依赖: weightEquiv
-/
def symm {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂) (f : RootPairing.Equiv P Q) :
    RootPairing.Equiv Q P where
  weightMap := (weightEquiv P Q f).symm
  coweightMap := (coweightEquiv P Q f).symm
  indexEquiv := f.indexEquiv.symm
  weight_coweight_transpose := by
    ext n m
    nth_rw 2 [show m = (weightEquiv P Q f) ((weightEquiv P Q f).symm m) by
      exact (LinearEquiv.symm_apply_eq (weightEquiv P Q f)).mp rfl]
    nth_rw 1 [show n = (coweightEquiv P Q f) ((coweightEquiv P Q f).symm n) by
      exact (LinearEquiv.symm_apply_eq (coweightEquiv P Q f)).mp rfl]
    have := f.weight_coweight_transpose
    rw [LinearMap.ext_iff₂] at this
    exact Eq.symm (this ((coweightEquiv P Q f).symm n) ((weightEquiv P Q f).symm m))
  root_weightMap := by
    ext i
    simp only [LinearEquiv.coe_coe, comp_apply]
    have := f.root_weightMap
    rw [funext_iff] at this
    specialize this (f.indexEquiv.symm i)
    simp only [comp_apply, Equiv.apply_symm_apply] at this
    simp [← this]
  coroot_coweightMap := by
    ext i
    simp only [LinearEquiv.coe_coe, comp_apply, Equiv.symm_symm]
    have := f.coroot_coweightMap
    rw [funext_iff] at this
    specialize this (f.indexEquiv i)
    simp only [comp_apply, Equiv.symm_apply_apply] at this
    simp [← this]
  bijective_weightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (weightEquiv P Q f).symm
  bijective_coweightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (coweightEquiv P Q f).symm

@[simp]
/--
lemma `inv_weightMap` / 引理 `inv_weightMap`

English:
lemma inv_weightMap
  statement: {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
  proof: rfl

@[simp]

中文:
引理 inv_weightMap
  结论: {ι₂ M₂ N₂ : 类型} [加法交换群 M₂] [模 R M₂] [加法交换群 N₂]
  证明: rfl

@[simp]
-/
lemma inv_weightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).weightMap = (weightEquiv P Q f).symm :=
  rfl

@[simp]
/--
lemma `inv_coweightMap` / 引理 `inv_coweightMap`

English:
lemma inv_coweightMap
  statement: {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
  proof: rfl

@[simp]

中文:
引理 inv_coweightMap
  结论: {ι₂ M₂ N₂ : 类型} [加法交换群 M₂] [模 R M₂] [加法交换群 N₂]
  证明: rfl

@[simp]
-/
lemma inv_coweightMap {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).coweightMap = (coweightEquiv P Q f).symm :=
  rfl

@[simp]
/--
lemma `inv_indexEquiv` / 引理 `inv_indexEquiv`

English:
lemma inv_indexEquiv
  statement: {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
  proof: rfl

中文:
引理 inv_indexEquiv
  结论: {ι₂ M₂ N₂ : 类型} [加法交换群 M₂] [模 R M₂] [加法交换群 N₂]
  证明: rfl
-/
lemma inv_indexEquiv {ι₂ M₂ N₂ : Type*} [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂]
    [Module R N₂] (P : RootPairing ι R M N) (Q : RootPairing ι₂ R M₂ N₂)
    (f : RootPairing.Equiv P Q) : (symm P Q f).indexEquiv = (Hom.indexEquiv f.toHom).symm :=
  rfl

/-- Equivalences form a group. -/
instance (P : RootPairing ι R M N) : Group (RootPairing.Equiv P P) where
  mul := comp
  mul_assoc := comp_assoc
  one := id P
  one_mul := id_comp P P
  mul_one := comp_id P P
  inv := symm P P
  inv_mul_cancel e := by
    ext m
    · rw [← weightEquiv_apply]
      simp
    · rw [← coweightEquiv_apply]
      simp
    · simp

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [IsDomain R] [CharZero R] [Module.IsTorsionFree R M₂] [Finite ι₂]
  body: f
  coweightMap := Q.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)
  indexEquiv := e
  weight_coweight_transpose := by ext; simp
  root_weightMap := by ext; simp [hf]
  coroot_coweightMap := by
let g : N ≃ₗ[R] N₂ := P.flip.toPerfPair.trans f.symm.dualMap.trans Q.flip.toPerfPair.symm

中文:
定义 mk'
  签名: [是整环 R] [特征零 R] [模.是无挠 R M₂] [有限 ι₂]
  定义体: f
  coweightMap := Q.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)
  indexEquiv := e
  weight_coweight_transpose := by ext; simp
  root_weightMap := by ext; simp [hf]
  coroot_coweightMap := by
let g : N ≃ₗ[R] N₂ := P.flip.toPerfPair.trans f.symm.dualMap.trans Q.flip.toPerfPair.symm

Depends on / 依赖: SFinite, SigmaFinite, disjointed, disjointed_subset, infer_instance, measure_mono, measure_spanningSets_lt_top, restrict, spanningSets, sum_restrict_disjointed_spanningSets, trans_lt
-/
def mk' [IsDomain R] [CharZero R] [Module.IsTorsionFree R M₂] [Finite ι₂]
    (P : RootPairing ι R M N) [P.IsRootSystem] (Q : RootPairing ι₂ R M₂ N₂) [Q.IsRootSystem]
    (f : M ≃ₗ[R] M₂) (e : ι ≃ ι₂) (hf : forall i, f (P.root i) = Q.root (e i)) :
    P.Equiv Q where
  weightMap := f
  coweightMap := Q.flip.toPerfPair.trans (f.dualMap.trans P.flip.toPerfPair.symm)
  indexEquiv := e
  weight_coweight_transpose := by ext; simp
  root_weightMap := by ext; simp [hf]
  coroot_coweightMap := by
let g : N ≃ₗ[R] N₂ := P.flip.toPerfPair.trans f.symm.dualMap.trans Q.flip.toPerfPair.symm
    suffices Q = P.map e f g by
      ext i
      rw [LinearEquiv.coe_coe]; rw [comp_apply]; rw [← LinearEquiv.eq_symm_apply]
      conv_lhs => rw [this]
      rfl
    apply IsRootSystem.ext <;> ext
    · simp [RootPairing.map, RootPairing.map, g]
    · simp [hf, RootPairing.map, RootPairing.map]
  bijective_weightMap := LinearEquiv.bijective _
  bijective_coweightMap := LinearEquiv.bijective _

end Equiv

/--
Definition of `Aut` / `Aut` 的定义

English:
abbreviation Aut
  signature: (P : RootPairing ι R M N)
  body: (RootPairing.Equiv P P)

中文:
缩写 Aut
  签名: (P : RootPairing ι R M N)
  定义体: (RootPairing.Equiv P P)

Depends on / 依赖: RootPairing, RootPairing.Equiv
-/
abbrev Aut (P : RootPairing ι R M N) := (RootPairing.Equiv P P)

namespace Equiv

/--
Definition of `toEndUnit` / `toEndUnit` 的定义

English:
definition toEndUnit
  signature: (P : RootPairing ι R M N)
  body: { val := f.toHom
    inv := (Equiv.symm P P f).toHom
    val_inv := by ext <;> simp
    inv_val := by ext <;> simp }
  invFun f :=
  { f.val with
    bijective_weightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.weightMap
      constructor
      · refine leftInverse_iff_com

中文:
定义 toEndUnit
  签名: (P : RootPairing ι R M N)
  定义体: { val := f.toHom
    inv := (Equiv.symm P P f).toHom
    val_inv := by ext <;> simp
    inv_val := by ext <;> simp }
  invFun f :=
  { f.val with
    bijective_weightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.weightMap
      constructor
      · refine leftInverse_iff_com

Depends on / 依赖: Equiv.symm, Hom.weightMap_mul, Hom.weightMap_one, LinearMap, LinearMap.coe_comp, LinearMap.id_coe, bijective_iff_has_inverse, bijective_iff_has_inverse.mpr, bijective_weightMap, coe_comp, f.inv.weightMap, f.inv_val, f.toHom, f.val, f.val_inv, id_coe, invFun, inv_val, leftInverse_iff_comp, leftInverse_iff_comp.mpr
-/
def toEndUnit (P : RootPairing ι R M N) : Aut P ≃* (End P)ˣ where
  toFun f :=
  { val := f.toHom
    inv := (Equiv.symm P P f).toHom
    val_inv := by ext <;> simp
    inv_val := by ext <;> simp }
  invFun f :=
  { f.val with
    bijective_weightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.weightMap
      constructor
      · refine leftInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.weightMap_mul]; rw [f.inv_val]; rw [Hom.weightMap_one]; rw [LinearMap.id_coe]
      · refine rightInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.weightMap_mul]; rw [f.val_inv]; rw [Hom.weightMap_one]; rw [LinearMap.id_coe]
    bijective_coweightMap := by
      refine bijective_iff_has_inverse.mpr ?_
      use f.inv.coweightMap
      constructor
      · refine leftInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.coweightMap_mul]; rw [f.val_inv]; rw [Hom.coweightMap_one]; rw [LinearMap.id_coe]
      · refine rightInverse_iff_comp.mpr ?_
        simp only [← @LinearMap.coe_comp]
        rw [← Hom.coweightMap_mul]; rw [f.inv_val]; rw [Hom.coweightMap_one]; rw [LinearMap.id_coe] }
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := by
    simp only [Equiv.mul_eq_comp, Equiv.toHom_comp]
    ext <;> simp

/--
lemma `toEndUnit_val` / 引理 `toEndUnit_val`

English:
lemma toEndUnit_val
  given: (P : RootPairing ι R M N) (g : Aut P)
  statement: (toEndUnit P g).val = g.toHom
  proof: rfl

中文:
引理 toEndUnit_val
  条件: (P : RootPairing ι R M N) (g : Aut P)
  结论: (toEndUnit P g).val = g.toHom
  证明: rfl
-/
lemma toEndUnit_val (P : RootPairing ι R M N) (g : Aut P) : (toEndUnit P g).val = g.toHom :=
  rfl

/--
lemma `toEndUnit_inv` / 引理 `toEndUnit_inv`

English:
lemma toEndUnit_inv
  given: (P : RootPairing ι R M N) (g : Aut P)
  proof: rfl

中文:
引理 toEndUnit_inv
  条件: (P : RootPairing ι R M N) (g : Aut P)
  证明: rfl
-/
lemma toEndUnit_inv (P : RootPairing ι R M N) (g : Aut P) :
    (toEndUnit P g).inv = (symm P P g).toHom :=
  rfl

/-- The weight space representation of automorphisms -/
@[simps]
/--
Definition of `weightHom` / `weightHom` 的定义

English:
definition weightHom
  signature: (P : RootPairing ι R M N)
  body: weightEquiv P P
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

中文:
定义 weightHom
  签名: (P : RootPairing ι R M N)
  定义体: weightEquiv P P
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

Depends on / 依赖: weightEquiv
-/
def weightHom (P : RootPairing ι R M N) : Aut P ->* (M ≃ₗ[R] M) where
  toFun := weightEquiv P P
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/--
lemma `weightHom_toLinearMap` / 引理 `weightHom_toLinearMap`

English:
lemma weightHom_toLinearMap
  given: {P : RootPairing ι R M N} (g : Aut P)
  proof: rfl

中文:
引理 weightHom_toLinearMap
  条件: {P : RootPairing ι R M N} (g : Aut P)
  证明: rfl
-/
lemma weightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) :
    (weightHom P g).toLinearMap = Hom.weightHom P g.toHom :=
  rfl

/--
lemma `weightHom_injective` / 引理 `weightHom_injective`

English:
lemma weightHom_injective
  given: (P : RootPairing ι R M N)
  statement: Injective (Equiv.weightHom P)
  proof: by
  refine Injective.of_comp (f := LinearEquiv.toLinearMap) fun g g' hgg' => ?_
  let h : (weightHom P g).toLinearMap = (weightHom P g').toLinearMap := hgg' --`have` gets lint
  rw [weightHom_toLinearMap]; rw [weightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext hgg

中文:
引理 weightHom_injective
  条件: (P : RootPairing ι R M N)
  结论: 单射 (等价.weightHom P)
  证明: by
  refine Injective.of_comp (f := LinearEquiv.toLinearMap) fun g g' hgg' => ?_
  let h : (weightHom P g).toLinearMap = (weightHom P g').toLinearMap := hgg' --`have` gets lint
  rw [weightHom_toLinearMap]; rw [weightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext hgg

Depends on / 依赖: Equiv.ext, Hom.coweightMap, Hom.indexEquiv, Hom.weightHom_injective, Injective, Injective.of_comp, LinearEquiv, LinearEquiv.toLinearMap, coweightMap, g.toHom, indexEquiv, of_comp, toLinearMap, weightHom, weightHom_injective, weightHom_toLinearMap
-/
lemma weightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.weightHom P) := by
  refine Injective.of_comp (f := LinearEquiv.toLinearMap) fun g g' hgg' => ?_
  let h : (weightHom P g).toLinearMap = (weightHom P g').toLinearMap := hgg' --`have` gets lint
  rw [weightHom_toLinearMap]; rw [weightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext hgg' (congrArg Hom.coweightMap h') (congrArg Hom.indexEquiv h')
  exact Hom.weightHom_injective P hgg'

@[simp]
/--
lemma `weightEquiv_inv` / 引理 `weightEquiv_inv`

English:
lemma weightEquiv_inv
  given: {P : RootPairing ι R M N} (g : Aut P)
  proof: LinearEquiv.toLinearMap_inj.mp rfl

中文:
引理 weightEquiv_inv
  条件: {P : RootPairing ι R M N} (g : Aut P)
  证明: LinearEquiv.toLinearMap_inj.mp rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, toLinearMap_inj
-/
lemma weightEquiv_inv {P : RootPairing ι R M N} (g : Aut P) :
    weightEquiv P P g⁻¹ = (weightEquiv P P g)⁻¹ :=
  LinearEquiv.toLinearMap_inj.mp rfl

/-- The coweight space representation of automorphisms -/
@[simps]
/--
Definition of `coweightHom` / `coweightHom` 的定义

English:
definition coweightHom
  signature: (P : RootPairing ι R M N)
  body: MulOpposite.op (coweightEquiv P P g)
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff]
    exact LinearEquiv.toLinearMap_inj.mp rfl
  map_mul' := by
    simp only [mul_eq_comp, coweightEquiv_comp_toLin]
    exact fun x y => rfl

中文:
定义 coweightHom
  签名: (P : RootPairing ι R M N)
  定义体: MulOpposite.op (coweightEquiv P P g)
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff]
    exact LinearEquiv.toLinearMap_inj.mp rfl
  map_mul' := by
    simp only [mul_eq_comp, coweightEquiv_comp_toLin]
    exact fun x y => rfl

Depends on / 依赖: MulOpposite, MulOpposite.op, coweightEquiv
-/
def coweightHom (P : RootPairing ι R M N) : Aut P ->* (N ≃ₗ[R] N)ᵐᵒᵖ where
  toFun g := MulOpposite.op (coweightEquiv P P g)
  map_one' := by
    simp only [MulOpposite.op_eq_one_iff]
    exact LinearEquiv.toLinearMap_inj.mp rfl
  map_mul' := by
    simp only [mul_eq_comp, coweightEquiv_comp_toLin]
    exact fun x y => rfl

/--
lemma `coweightHom_toLinearMap` / 引理 `coweightHom_toLinearMap`

English:
lemma coweightHom_toLinearMap
  given: {P : RootPairing ι R M N} (g : Aut P)
  proof: rfl

中文:
引理 coweightHom_toLinearMap
  条件: {P : RootPairing ι R M N} (g : Aut P)
  证明: rfl
-/
lemma coweightHom_toLinearMap {P : RootPairing ι R M N} (g : Aut P) :
    (MulOpposite.unop (coweightHom P g)).toLinearMap =
      MulOpposite.unop (Hom.coweightHom P g.toHom) :=
  rfl

/--
lemma `coweightHom_injective` / 引理 `coweightHom_injective`

English:
lemma coweightHom_injective
  given: (P : RootPairing ι R M N)
  statement: Injective (Equiv.coweightHom P)
  proof: by
  refine Injective.of_comp (f := fun a => MulOpposite.op a) fun g g' hgg' => ?_
  have h : (MulOpposite.unop (coweightHom P g)).toLinearMap =
      (MulOpposite.unop (coweightHom P g')).toLinearMap := by
    simp_all
  rw [coweightHom_toLinearMap]; rw [coweightHom_toLinearMap] at h
  suffices h' 

中文:
引理 coweightHom_injective
  条件: (P : RootPairing ι R M N)
  结论: 单射 (等价.coweightHom P)
  证明: by
  refine Injective.of_comp (f := fun a => MulOpposite.op a) fun g g' hgg' => ?_
  have h : (MulOpposite.unop (coweightHom P g)).toLinearMap =
      (MulOpposite.unop (coweightHom P g')).toLinearMap := by
    simp_all
  rw [coweightHom_toLinearMap]; rw [coweightHom_toLinearMap] at h
  suffices h' 

Depends on / 依赖: Equiv.ext, Hom.coweightHom_injective, Hom.indexEquiv, Hom.weightMap, Injective, Injective.of_comp, MulOpposite, MulOpposite.op, MulOpposite.unop, MulOpposite.unop_inj.mp, coweightHom, coweightHom_injective, coweightHom_toLinearMap, g.toHom, indexEquiv, of_comp, toLinearMap, unop_inj, weightMap
-/
lemma coweightHom_injective (P : RootPairing ι R M N) : Injective (Equiv.coweightHom P) := by
  refine Injective.of_comp (f := fun a => MulOpposite.op a) fun g g' hgg' => ?_
  have h : (MulOpposite.unop (coweightHom P g)).toLinearMap =
      (MulOpposite.unop (coweightHom P g')).toLinearMap := by
    simp_all
  rw [coweightHom_toLinearMap]; rw [coweightHom_toLinearMap] at h
  suffices h' : g.toHom = g'.toHom by
    exact Equiv.ext (congrArg Hom.weightMap h') h (congrArg Hom.indexEquiv h')
  apply Hom.coweightHom_injective P
  exact MulOpposite.unop_inj.mp h

/--
lemma `coweightHom_op` / 引理 `coweightHom_op`

English:
lemma coweightHom_op
  given: {P : RootPairing ι R M N} (g : Aut P)
  proof: rfl

@[simp]

中文:
引理 coweightHom_op
  条件: {P : RootPairing ι R M N} (g : Aut P)
  证明: rfl

@[simp]
-/
lemma coweightHom_op {P : RootPairing ι R M N} (g : Aut P) :
    MulOpposite.unop (coweightHom P g) = coweightEquiv P P g :=
  rfl

@[simp]
/--
lemma `coweightEquiv_inv` / 引理 `coweightEquiv_inv`

English:
lemma coweightEquiv_inv
  given: {P : RootPairing ι R M N} (g : Aut P)
  proof: LinearEquiv.toLinearMap_inj.mp rfl

中文:
引理 coweightEquiv_inv
  条件: {P : RootPairing ι R M N} (g : Aut P)
  证明: LinearEquiv.toLinearMap_inj.mp rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, toLinearMap_inj
-/
lemma coweightEquiv_inv {P : RootPairing ι R M N} (g : Aut P) :
    coweightEquiv P P g⁻¹ = (coweightEquiv P P g)⁻¹ :=
  LinearEquiv.toLinearMap_inj.mp rfl

/-- The permutation representation of the automorphism group on the root index set -/
@[simps]
/--
Definition of `indexHom` / `indexHom` 的定义

English:
definition indexHom
  signature: (P : RootPairing ι R M N)
  body: g.toHom.indexEquiv
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]

中文:
定义 indexHom
  签名: (P : RootPairing ι R M N)
  定义体: g.toHom.indexEquiv
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]

Depends on / 依赖: g.toHom.indexEquiv, indexEquiv
-/
def indexHom (P : RootPairing ι R M N) : Aut P ->* (ι ≃ ι) where
  toFun g := g.toHom.indexEquiv
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
/--
lemma `indexEquiv_inv` / 引理 `indexEquiv_inv`

English:
lemma indexEquiv_inv
  given: {P : RootPairing ι R M N} (g : Aut P)
  proof: rfl

中文:
引理 indexEquiv_inv
  条件: {P : RootPairing ι R M N} (g : Aut P)
  证明: rfl
-/
lemma indexEquiv_inv {P : RootPairing ι R M N} (g : Aut P) :
    (g⁻¹).toHom.indexEquiv = (indexHom P g)⁻¹ :=
  rfl

/--
Definition of `reflection` / `reflection` 的定义

English:
definition reflection
  signature: (P : RootPairing ι R M N) (i : ι)
  body: P.reflection i
  coweightMap := P.coreflection i
  indexEquiv := P.reflectionPerm i
  weight_coweight_transpose := by
    ext f x; simpa [reflection_apply, coreflection_apply] using mul_comm ..
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp
  bijective_weightMap := by
    simp

中文:
定义 reflection
  签名: (P : RootPairing ι R M N) (i : ι)
  定义体: P.reflection i
  coweightMap := P.coreflection i
  indexEquiv := P.reflectionPerm i
  weight_coweight_transpose := by
    ext f x; simpa [reflection_apply, coreflection_apply] using mul_comm ..
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp
  bijective_weightMap := by
    simp

Depends on / 依赖: P.reflection, reflection
-/
def reflection (P : RootPairing ι R M N) (i : ι) : Aut P where
  weightMap := P.reflection i
  coweightMap := P.coreflection i
  indexEquiv := P.reflectionPerm i
  weight_coweight_transpose := by
    ext f x; simpa [reflection_apply, coreflection_apply] using mul_comm ..
  root_weightMap := by ext; simp
  coroot_coweightMap := by ext; simp
  bijective_weightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (P.reflection i)
  bijective_coweightMap := by
    simp only [LinearEquiv.coe_coe]
    exact LinearEquiv.bijective (P.coreflection i)

@[simp]
/--
lemma `reflection_weightEquiv` / 引理 `reflection_weightEquiv`

English:
lemma reflection_weightEquiv
  given: (P : RootPairing ι R M N) (i : ι)
  proof: LinearEquiv.toLinearMap_inj.mp rfl

@[simp]

中文:
引理 reflection_weightEquiv
  条件: (P : RootPairing ι R M N) (i : ι)
  证明: LinearEquiv.toLinearMap_inj.mp rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, toLinearMap_inj
-/
lemma reflection_weightEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).weightEquiv = P.reflection i :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
/--
lemma `reflection_coweightEquiv` / 引理 `reflection_coweightEquiv`

English:
lemma reflection_coweightEquiv
  given: (P : RootPairing ι R M N) (i : ι)
  proof: LinearEquiv.toLinearMap_inj.mp rfl

@[simp]

中文:
引理 reflection_coweightEquiv
  条件: (P : RootPairing ι R M N) (i : ι)
  证明: LinearEquiv.toLinearMap_inj.mp rfl

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, toLinearMap_inj
-/
lemma reflection_coweightEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).coweightEquiv = P.coreflection i :=
  LinearEquiv.toLinearMap_inj.mp rfl

@[simp]
/--
lemma `reflection_indexEquiv` / 引理 `reflection_indexEquiv`

English:
lemma reflection_indexEquiv
  given: (P : RootPairing ι R M N) (i : ι)
  proof: rfl

@[simp]

中文:
引理 reflection_indexEquiv
  条件: (P : RootPairing ι R M N) (i : ι)
  证明: rfl

@[simp]
-/
lemma reflection_indexEquiv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i).indexEquiv = P.reflectionPerm i :=
  rfl

@[simp]
/--
lemma `reflection_inv` / 引理 `reflection_inv`

English:
lemma reflection_inv
  given: (P : RootPairing ι R M N) (i : ι)
  proof: by
  refine Equiv.ext ?_ ?_ ?_
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← weightEquiv_apply])
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← coweightEquiv_apply])
  · exact _root_.Equiv.ext (fun j => by simp)

中文:
引理 reflection_inv
  条件: (P : RootPairing ι R M N) (i : ι)
  证明: by
  refine Equiv.ext ?_ ?_ ?_
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← weightEquiv_apply])
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← coweightEquiv_apply])
  · exact _root_.Equiv.ext (fun j => by simp)

Depends on / 依赖: Equiv.ext, LinearMap, LinearMap.ext_iff.mpr, _root_, _root_.Equiv.ext, coweightEquiv_apply, ext_iff, weightEquiv_apply
-/
lemma reflection_inv (P : RootPairing ι R M N) (i : ι) :
    (reflection P i)⁻¹ = (reflection P i) := by
  refine Equiv.ext ?_ ?_ ?_
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← weightEquiv_apply])
  · exact LinearMap.ext_iff.mpr (fun x => by simp [← coweightEquiv_apply])
  · exact _root_.Equiv.ext (fun j => by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction P.Aut M
  body: weightHom P w x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show weightHom P w 0 = 0 by simp
  smul_add w x y := show weightHom P w (x + y) = weightHom P w x + weightHom P w y by simp

中文:
实例 :
  签名: 分配乘法作用 P.Aut M
  定义体: weightHom P w x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show weightHom P w 0 = 0 by simp
  smul_add w x y := show weightHom P w (x + y) = weightHom P w x + weightHom P w y by simp

Depends on / 依赖: weightHom
-/
instance : DistribMulAction P.Aut M where
  smul w x := weightHom P w x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show weightHom P w 0 = 0 by simp
  smul_add w x y := show weightHom P w (x + y) = weightHom P w x + weightHom P w y by simp

/--
lemma `reflection_smul` / 引理 `reflection_smul`

English:
lemma reflection_smul
  given: (i : ι) (x : M)
  statement: Equiv.reflection P i • x = P.reflection i x
  proof: rfl

中文:
引理 reflection_smul
  条件: (i : ι) (x : M)
  结论: 等价.reflection P i • x = P.reflection i x
  证明: rfl
-/
@[simp] lemma reflection_smul (i : ι) (x : M) : Equiv.reflection P i • x = P.reflection i x := rfl

/--
lemma `root_indexEquiv_eq_smul` / 引理 `root_indexEquiv_eq_smul`

English:
lemma root_indexEquiv_eq_smul
  given: (i : ι) (g : P.Aut)
  proof: by
  simpa using! (congr_fun g.root_weightMap i).symm

中文:
引理 root_indexEquiv_eq_smul
  条件: (i : ι) (g : P.Aut)
  证明: by
  simpa using! (congr_fun g.root_weightMap i).symm
-/
@[simp] lemma root_indexEquiv_eq_smul (i : ι) (g : P.Aut) :
    P.root (g.indexEquiv i) = g • P.root i := by
  simpa using! (congr_fun g.root_weightMap i).symm

open MulOpposite in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction P.Autᵐᵒᵖ N
  body: unop (coweightHom P (unop w)) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show unop (coweightHom P (unop w)) 0 = 0 by simp
  smul_add w x y := by
    change unop (coweightHom P _) (x + y) = unop (coweightHom P _) x + unop (coweightHom P _) y
    simp

中文:
实例 :
  签名: 分配乘法作用 P.Autᵐᵒᵖ N
  定义体: unop (coweightHom P (unop w)) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show unop (coweightHom P (unop w)) 0 = 0 by simp
  smul_add w x y := by
    change unop (coweightHom P _) (x + y) = unop (coweightHom P _) x + unop (coweightHom P _) y
    simp

Depends on / 依赖: IsFiniteMeasure, IsFiniteMeasure.toSigmaFinite, MeasurableSpace, Measure, coweightHom, toSigmaFinite
-/
instance : DistribMulAction P.Autᵐᵒᵖ N where
  smul w x := unop (coweightHom P (unop w)) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero w := show unop (coweightHom P (unop w)) 0 = 0 by simp
  smul_add w x y := by
    change unop (coweightHom P _) (x + y) = unop (coweightHom P _) x + unop (coweightHom P _) y
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass P.Aut R M
  body: show weightHom P w (t • x) = t • weightHom P w x by simp

中文:
实例 :
  签名: 标量交换类 P.Aut R M
  定义体: show weightHom P w (t • x) = t • weightHom P w x by simp

Depends on / 依赖: weightHom
-/
instance : SMulCommClass P.Aut R M where
  smul_comm w t x := show weightHom P w (t • x) = t • weightHom P w x by simp

open MulOpposite in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass P.Autᵐᵒᵖ R N
  body: by
    change unop (coweightHom P (unop w)) (t • x) = t • unop (coweightHom P (unop w)) x
    simp

中文:
实例 :
  签名: 标量交换类 P.Autᵐᵒᵖ R N
  定义体: by
    change unop (coweightHom P (unop w)) (t • x) = t • unop (coweightHom P (unop w)) x
    simp

Depends on / 依赖: coweightHom
-/
instance : SMulCommClass P.Autᵐᵒᵖ R N where
  smul_comm w t x := by
    change unop (coweightHom P (unop w)) (t • x) = t • unop (coweightHom P (unop w)) x
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction P.Aut ι
  body: Equiv.indexHom P w i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

中文:
实例 :
  签名: 乘法作用 P.Aut ι
  定义体: Equiv.indexHom P w i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

Depends on / 依赖: Equiv.indexHom, indexHom
-/
instance : MulAction P.Aut ι where
  smul w i := Equiv.indexHom P w i
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

end Equiv

end RootPairing
