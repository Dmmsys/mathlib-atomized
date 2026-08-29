/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Products of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.prod`: a product of uniform spaces with nonarchimedean uniformities
  has a nonarchimedean uniformity.
* `IsUltraUniformity.pi`: an indexed product of uniform spaces with nonarchimedean uniformities
  has a nonarchimedean uniformity.

## Implementation details

This file can be split to separate imports to have the `Prod` and `Pi` instances separately,
but would be somewhat unnatural since they are closely related.
The `Prod` instance only requires `Mathlib/Topology/UniformSpace/Basic.lean`.

-/

public section

variable {X Y : Type*}

/--
Instance `SetRel.isTrans_entourageProd` / 实例 `SetRel.isTrans_entourageProd`

English:
instance SetRel.isTrans_entourageProd
  signature: {s : SetRel X X} {t : SetRel Y Y} [s.IsTrans] [t.IsTrans]
  body: ⟨s.trans h.left h'.left, t.trans h.right h'.right⟩

中文:
实例 SetRel.isTrans_entourageProd
  签名: {s : SetRel X X} {t : SetRel Y Y} [s.是Trans] [t.是Trans]
  定义体: ⟨s.trans h.left h'.left, t.trans h.right h'.right⟩

Depends on / 依赖: h.left, h.right, s.trans, t.trans
-/
instance SetRel.isTrans_entourageProd {s : SetRel X X} {t : SetRel Y Y} [s.IsTrans] [t.IsTrans] :
    (entourageProd s t).IsTrans where
  trans _ _ _ h h' := ⟨s.trans h.left h'.left, t.trans h.right h'.right⟩

/--
lemma `IsUltraUniformity.comap` / 引理 `IsUltraUniformity.comap`

English:
lemma IsUltraUniformity.comap
  given: {u : UniformSpace Y} (h : IsUltraUniformity Y) (f : X -> Y)
  proof: by
  let := u.comap f
  refine .mk_of_hasBasis (h.hasBasis.comap (Prod.map f f)) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨_, _, _⟩
    infer_instance

中文:
引理 是UltraUniformity.comap
  条件: {u : 一致空间 Y} (h : 是UltraUniformity Y) (f : X -> Y)
  证明: by
  let := u.comap f
  refine .mk_of_hasBasis (h.hasBasis.comap (Prod.map f f)) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨_, _, _⟩
    infer_instance

Depends on / 依赖: Prod.map, h.hasBasis.comap, hasBasis, infer_instance, mk_of_hasBasis, u.comap
-/
lemma IsUltraUniformity.comap {u : UniformSpace Y} (h : IsUltraUniformity Y) (f : X -> Y) :
    @IsUltraUniformity _ (u.comap f) := by
  let := u.comap f
  refine .mk_of_hasBasis (h.hasBasis.comap (Prod.map f f)) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨_, _, _⟩
    infer_instance

/--
lemma `IsUltraUniformity.inf` / 引理 `IsUltraUniformity.inf`

English:
lemma IsUltraUniformity.inf
  statement: {u u' : UniformSpace X} (h : @IsUltraUniformity _ u)
  proof: by
  let := u ⊓ u'
  refine .mk_of_hasBasis (h.hasBasis.inf h'.hasBasis) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨⟨_, _, _⟩, _, _, _⟩
    infer_instance

中文:
引理 是UltraUniformity.下确界
  结论: {u u' : 一致空间 X} (h : @是UltraUniformity _ u)
  证明: by
  let := u ⊓ u'
  refine .mk_of_hasBasis (h.hasBasis.inf h'.hasBasis) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨⟨_, _, _⟩, _, _, _⟩
    infer_instance

Depends on / 依赖: h.hasBasis.inf, hasBasis, infer_instance, mk_of_hasBasis
-/
lemma IsUltraUniformity.inf {u u' : UniformSpace X} (h : @IsUltraUniformity _ u)
    (h' : @IsUltraUniformity _ u') :
    @IsUltraUniformity _ (u ⊓ u') := by
  let := u ⊓ u'
  refine .mk_of_hasBasis (h.hasBasis.inf h'.hasBasis) ?_ ?_ <;>
  · dsimp
    rintro _ ⟨⟨_, _, _⟩, _, _, _⟩
    infer_instance

/--
Instance `IsUltraUniformity.prod` / 实例 `IsUltraUniformity.prod`

English:
instance IsUltraUniformity.prod
  signature: [UniformSpace X] [UniformSpace Y]
  body: .inf (.comap ‹_› _) (.comap ‹_› _)

中文:
实例 是UltraUniformity.乘积
  签名: [一致空间 X] [一致空间 Y]
  定义体: .inf (.comap ‹_› _) (.comap ‹_› _)
-/
instance IsUltraUniformity.prod [UniformSpace X] [UniformSpace Y]
    [IsUltraUniformity X] [IsUltraUniformity Y] :
    IsUltraUniformity (X × Y) :=
  .inf (.comap ‹_› _) (.comap ‹_› _)

/--
lemma `IsUltraUniformity.iInf` / 引理 `IsUltraUniformity.iInf`

English:
lemma IsUltraUniformity.iInf
  statement: {ι : Type*} {U : (i : ι) -> UniformSpace X}
  proof: by
  let : UniformSpace X := ⨅ i, U i
  refine .mk_of_hasBasis (iInf_uniformity ▸ Filter.HasBasis.iInf fun i => (hU i).hasBasis) ?_ ?_ <;>
  · simp only [forall_and, Subtype.forall, id_eq, Set.iInter_coe_set, and_imp]
    rintro _ _ _ _ _
    infer_instance

中文:
引理 是UltraUniformity.iInf
  结论: {ι : 类型} {U : (i : ι) -> 一致空间 X}
  证明: by
  let : UniformSpace X := ⨅ i, U i
  refine .mk_of_hasBasis (iInf_uniformity ▸ Filter.HasBasis.iInf fun i => (hU i).hasBasis) ?_ ?_ <;>
  · simp only [forall_and, Subtype.forall, id_eq, Set.iInter_coe_set, and_imp]
    rintro _ _ _ _ _
    infer_instance

Depends on / 依赖: Filter, Filter.HasBasis.iInf, HasBasis, Set.iInter_coe_set, Subtype, Subtype.forall, UniformSpace, and_imp, forall_and, hasBasis, iInf_uniformity, iInter_coe_set, id_eq, infer_instance, mk_of_hasBasis
-/
lemma IsUltraUniformity.iInf {ι : Type*} {U : (i : ι) -> UniformSpace X}
    (hU : forall i, @IsUltraUniformity X (U i)) :
    @IsUltraUniformity _ (⨅ i, U i : UniformSpace X) := by
  let : UniformSpace X := ⨅ i, U i
  refine .mk_of_hasBasis (iInf_uniformity ▸ Filter.HasBasis.iInf fun i => (hU i).hasBasis) ?_ ?_ <;>
  · simp only [forall_and, Subtype.forall, id_eq, Set.iInter_coe_set, and_imp]
    rintro _ _ _ _ _
    infer_instance

/--
Instance `IsUltraUniformity.pi` / 实例 `IsUltraUniformity.pi`

English:
instance IsUltraUniformity.pi
  signature: {ι : Type*} {X : ι -> Type*} [U : Π i, UniformSpace (X i)]
  body: by
  suffices @IsUltraUniformity _ (⨅ i, UniformSpace.comap (Function.eval i) (U i)) by
    simpa +instances [Pi.uniformSpace_eq _] using this
  exact .iInf fun i => .comap (h i) (Function.eval i)

中文:
实例 是UltraUniformity.pi
  签名: {ι : 类型} {X : ι -> 类型} [U : Π i, 一致空间 (X i)]
  定义体: by
  suffices @IsUltraUniformity _ (⨅ i, UniformSpace.comap (Function.eval i) (U i)) by
    simpa +instances [Pi.uniformSpace_eq _] using this
  exact .iInf fun i => .comap (h i) (Function.eval i)

Depends on / 依赖: Function, Function.eval, IsUltraUniformity, Pi.uniformSpace_eq, UniformSpace, UniformSpace.comap, instances, uniformSpace_eq
-/
instance IsUltraUniformity.pi {ι : Type*} {X : ι -> Type*} [U : Π i, UniformSpace (X i)]
    [h : forall i, IsUltraUniformity (X i)] :
    IsUltraUniformity (Π i, X i) := by
  suffices @IsUltraUniformity _ (⨅ i, UniformSpace.comap (Function.eval i) (U i)) by
    simpa +instances [Pi.uniformSpace_eq _] using this
  exact .iInf fun i => .comap (h i) (Function.eval i)

/--
Instance `IsUltraUniformity.bot` / 实例 `IsUltraUniformity.bot`

English:
instance IsUltraUniformity.bot
  signature: [UniformSpace X] [DiscreteUniformity X]
  body: by
  have := Filter.hasBasis_principal (SetRel.id (α := X))
  rw [← DiscreteUniformity.eq_principal_setRelId] at this
  exact mk_of_hasBasis this inferInstance inferInstance

中文:
实例 是UltraUniformity.bot
  签名: [一致空间 X] [DiscreteUniformity X]
  定义体: by
  have := Filter.hasBasis_principal (SetRel.id (α := X))
  rw [← DiscreteUniformity.eq_principal_setRelId] at this
  exact mk_of_hasBasis this inferInstance inferInstance

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.eq_principal_setRelId, Filter, Filter.hasBasis_principal, SetRel, SetRel.id, eq_principal_setRelId, hasBasis_principal, mk_of_hasBasis
-/
instance IsUltraUniformity.bot [UniformSpace X] [DiscreteUniformity X] : IsUltraUniformity X := by
  have := Filter.hasBasis_principal (SetRel.id (α := X))
  rw [← DiscreteUniformity.eq_principal_setRelId] at this
  exact mk_of_hasBasis this inferInstance inferInstance

/--
lemma `IsUltraUniformity.top` / 引理 `IsUltraUniformity.top`

English:
lemma IsUltraUniformity.top
  statement: @IsUltraUniformity X (⊤ : UniformSpace X)
  proof: by
  let : UniformSpace X := ⊤
  have := Filter.hasBasis_top (α := (X × X))
  rw [← top_uniformity] at this
  exact mk_of_hasBasis this inferInstance inferInstance

中文:
引理 是UltraUniformity.top
  结论: @是UltraUniformity X (⊤ : 一致空间 X)
  证明: by
  let : UniformSpace X := ⊤
  have := Filter.hasBasis_top (α := (X × X))
  rw [← top_uniformity] at this
  exact mk_of_hasBasis this inferInstance inferInstance

Depends on / 依赖: Filter, Filter.hasBasis_top, UniformSpace, hasBasis_top, mk_of_hasBasis, top_uniformity
-/
lemma IsUltraUniformity.top : @IsUltraUniformity X (⊤ : UniformSpace X) := by
  let : UniformSpace X := ⊤
  have := Filter.hasBasis_top (α := (X × X))
  rw [← top_uniformity] at this
  exact mk_of_hasBasis this inferInstance inferInstance
