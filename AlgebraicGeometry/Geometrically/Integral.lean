/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Geometrically Integral Schemes

## Main results
- `AlgebraicGeometry.GeometricallyIntegral`:
  We say that morphism `f : X ⟶ Y` is geometrically integral if for all `Spec K ⟶ Y` with `K`
  a field, `X ×[Y] Spec K` is integral.
  We also provide the fact that this is stable under base change (`by infer_instance`)
- `GeometricallyIntegral.iff_geometricallyIntegral_fiber`:
  A scheme is geometrically integral over `S` iff the fibers of all
  `s : S` are geometrically integral.
- `AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`:
  If `X` is geometrically integral, flat, and universally open (e.g. when over a field),
  over an integral locally noetherian scheme, then `X` is also integral.
- `AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_subsingleton`:
  If `X` is geometrically integral over a field, then it is integral.
-/

public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- We say that morphism `f : X ⟶ Y` is geometrically integral if for all `Spec K ⟶ Y` with `K`
a field, `X ×[Y] Spec K` is integral. -/
@[mk_iff]
/--
Definition of `GeometricallyIntegral` / `GeometricallyIntegral` 的定义

English:
class GeometricallyIntegral
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - geometrically_isIntegral : geometrically IsIntegral f

中文:
类 几何整
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - geometrically_isIntegral : geometrically 是整 f
-/
class GeometricallyIntegral (f : X ⟶ Y) : Prop where
  geometrically_isIntegral : geometrically IsIntegral f

/--
lemma `GeometricallyIntegral.eq_geometrically` / 引理 `GeometricallyIntegral.eq_geometrically`

English:
lemma GeometricallyIntegral.eq_geometrically
  proof: by
  ext; exact geometricallyIntegral_iff _

中文:
引理 几何整.eq_geometrically
  证明: by
  ext; exact geometricallyIntegral_iff _

Depends on / 依赖: geometricallyIntegral_iff
-/
lemma GeometricallyIntegral.eq_geometrically :
    @GeometricallyIntegral = geometrically IsIntegral := by
  ext; exact geometricallyIntegral_iff _

/--
lemma `GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible` / 引理 `GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible`

English:
lemma GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible
  proof: by
  rw [eq_geometrically]; rw [GeometricallyReduced.eq_geometrically]; rw [GeometricallyIrreducible.eq_geometrically]; rw [← geometrically_inf]
  eta_expand
  simp [isIntegral_iff_irreducibleSpace_and_isReduced, and_comm]

中文:
引理 几何整.eq_geometricallyReduced_inf_geometricallyIrreducible
  证明: by
  rw [eq_geometrically]; rw [GeometricallyReduced.eq_geometrically]; rw [GeometricallyIrreducible.eq_geometrically]; rw [← geometrically_inf]
  eta_expand
  simp [isIntegral_iff_irreducibleSpace_and_isReduced, and_comm]

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.eq_geometrically, GeometricallyReduced, GeometricallyReduced.eq_geometrically, and_comm, eq_geometrically, eta_expand, geometrically_inf, isIntegral_iff_irreducibleSpace_and_isReduced
-/
lemma GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible :
    @GeometricallyIntegral =
      (@GeometricallyReduced ⊓ @GeometricallyIrreducible : MorphismProperty Scheme) := by
  rw [eq_geometrically]; rw [GeometricallyReduced.eq_geometrically]; rw [GeometricallyIrreducible.eq_geometrically]; rw [← geometrically_inf]
  eta_expand
  simp [isIntegral_iff_irreducibleSpace_and_isReduced, and_comm]

instance (priority := low) [GeometricallyIntegral f] : GeometricallyReduced f :=
  (GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.le _ _ _ ‹_›).1

instance (priority := low) [GeometricallyIntegral f] : GeometricallyIrreducible f :=
  (GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.le _ _ _ ‹_›).2

/--
lemma `GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible` / 引理 `GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible`

English:
lemma GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
  proof: GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.ge _ _ _ ⟨‹_›, ‹_›⟩

中文:
引理 几何整.of_geometricallyReduced_of_geometricallyIrreducible
  证明: GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.ge _ _ _ ⟨‹_›, ‹_›⟩

Depends on / 依赖: GeometricallyIntegral, GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.ge, eq_geometricallyReduced_inf_geometricallyIrreducible
-/
lemma GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible
    [GeometricallyReduced f] [GeometricallyIrreducible f] :
    GeometricallyIntegral f :=
  GeometricallyIntegral.eq_geometricallyReduced_inf_geometricallyIrreducible.ge _ _ _ ⟨‹_›, ‹_›⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @GeometricallyIntegral
  body: GeometricallyIntegral.eq_geometrically ▸ inferInstance

中文:
实例 :
  签名: 是StableUnderBaseChange @几何整
  定义体: GeometricallyIntegral.eq_geometrically ▸ inferInstance

Depends on / 依赖: GeometricallyIntegral, GeometricallyIntegral.eq_geometrically, eq_geometrically
-/
instance : IsStableUnderBaseChange @GeometricallyIntegral :=
  GeometricallyIntegral.eq_geometrically ▸ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIntegral
  signature: g] : GeometricallyIntegral (pullback.fst f g)
  body: MorphismProperty.pullback_fst f g inferInstance

中文:
实例 [几何整
  签名: g] : 几何整 (pullback.fst f g)
  定义体: MorphismProperty.pullback_fst f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_fst, pullback_fst
-/
instance [GeometricallyIntegral g] : GeometricallyIntegral (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIntegral
  signature: f] : GeometricallyIntegral (pullback.snd f g)
  body: MorphismProperty.pullback_snd f g inferInstance

中文:
实例 [几何整
  签名: f] : 几何整 (pullback.snd f g)
  定义体: MorphismProperty.pullback_snd f g inferInstance

Depends on / 依赖: MorphismProperty, MorphismProperty.pullback_snd, pullback_snd
-/
instance [GeometricallyIntegral f] : GeometricallyIntegral (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (V : S.Opens) [GeometricallyIntegral f] : GeometricallyIntegral (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict ..).flip ‹_›

set_option backward.isDefEq.respectTransparency.types false in
instance (s : S) [GeometricallyIntegral f] :
    GeometricallyIntegral (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance (s : S) [GeometricallyIntegral f] : IsIntegral (f.fiber s) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback _ _)

instance (priority := low) [GeometricallyIntegral f] : Surjective f :=
  ⟨fun x => ⟨_, (f.range_fiberι x).le ⟨Nonempty.some inferInstance, rfl⟩⟩⟩

/--
lemma `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` / 引理 `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`

English:
lemma GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
  proof: by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

中文:
引理 几何整.is整数egral_of_isLocallyNoetherian
  证明: by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.irreducibleSpace, GeometricallyReduced, GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian, f.isOpenMap, irreducibleSpace, isIntegral_iff_irreducibleSpace_and_isReduced, isOpenMap, isReduced_of_flat_of_isLocallyNoetherian
-/
lemma GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] [IsLocallyNoetherian S] : IsIntegral X := by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

/--
lemma `GeometricallyIntegral.isIntegral_of_subsingleton` / 引理 `GeometricallyIntegral.isIntegral_of_subsingleton`

English:
lemma GeometricallyIntegral.isIntegral_of_subsingleton
  proof: by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨GeometricallyIrreducible.irreducibleSpace_of_subsingleton f,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

中文:
引理 几何整.is整数egral_of_subsingleton
  证明: by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨GeometricallyIrreducible.irreducibleSpace_of_subsingleton f,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

Depends on / 依赖: GeometricallyIrreducible, GeometricallyIrreducible.irreducibleSpace_of_subsingleton, GeometricallyReduced, GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian, irreducibleSpace_of_subsingleton, isIntegral_iff_irreducibleSpace_and_isReduced, isReduced_of_flat_of_isLocallyNoetherian
-/
lemma GeometricallyIntegral.isIntegral_of_subsingleton
    [GeometricallyIntegral f] [Subsingleton S] [IsIntegral S] : IsIntegral X := by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨GeometricallyIrreducible.irreducibleSpace_of_subsingleton f,
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIntegral
  signature: f] [Flat f] [UniversallyOpen f] [IsIntegral Y]
  body: GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd _ _)

中文:
实例 [几何整
  签名: f] [平坦 f] [普遍开 f] [是整 Y]
  定义体: GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd _ _)

Depends on / 依赖: GeometricallyIntegral, GeometricallyIntegral.isIntegral_of_isLocallyNoetherian, isIntegral_of_isLocallyNoetherian, pullback, pullback.snd
-/
instance [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [IsIntegral Y]
    [IsLocallyNoetherian Y] : IsIntegral (pullback f g) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [GeometricallyIntegral
  signature: g] [Flat g] [UniversallyOpen g]
  body: GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst _ _)

中文:
实例 [几何整
  签名: g] [平坦 g] [普遍开 g]
  定义体: GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst _ _)

Depends on / 依赖: GeometricallyIntegral, GeometricallyIntegral.isIntegral_of_isLocallyNoetherian, isIntegral_of_isLocallyNoetherian, pullback, pullback.fst
-/
instance [GeometricallyIntegral g] [Flat g] [UniversallyOpen g]
    [IsIntegral X] [IsLocallyNoetherian X] :
    IsIntegral (pullback f g) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst _ _)

/--
lemma `GeometricallyIntegral.iff_geometricallyIntegral_fiber` / 引理 `GeometricallyIntegral.iff_geometricallyIntegral_fiber`

English:
lemma GeometricallyIntegral.iff_geometricallyIntegral_fiber
  proof: by
  simp only [GeometricallyIntegral.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

中文:
引理 几何整.iff_geometrically整数egral_fiber
  证明: by
  simp only [GeometricallyIntegral.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

Depends on / 依赖: GeometricallyIntegral, GeometricallyIntegral.eq_geometrically, eq_geometrically, geometrically_iff_forall_fiberToSpecResidueField
-/
lemma GeometricallyIntegral.iff_geometricallyIntegral_fiber :
    GeometricallyIntegral f ↔ forall s, GeometricallyIntegral (f.fiberToSpecResidueField s) := by
  simp only [GeometricallyIntegral.eq_geometrically,
    ← geometrically_iff_forall_fiberToSpecResidueField]

end AlgebraicGeometry
