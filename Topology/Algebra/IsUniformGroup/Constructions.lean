/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.Pi
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Constructions of new uniform groups from old ones
-/

public section

variable {G H hom : Type*} [Group G] [Group H]

section LatticeOps

@[to_additive]
/--
theorem `isUniformGroup_sInf` / 定理 `isUniformGroup_sInf`

English:
theorem isUniformGroup_sInf
  given: {us : Set (UniformSpace G)} (h : forall u in us, @IsUniformGroup G u _)
  proof: @IsUniformGroup.mk G (_) _
    uniformContinuous_sInf_rng.mpr fun u hu =>
      uniformContinuous_sInf_dom₂ hu hu (@IsUniformGroup.uniformContinuous_div G u _ (h u hu))

@[to_additive]

中文:
定理 isUniformGroup_sInf
  条件: {us : 集合 (一致空间 G)} (h : 对任意 u in us, @是一致群 G u _)
  证明: @IsUniformGroup.mk G (_) _
    uniformContinuous_sInf_rng.mpr fun u hu =>
      uniformContinuous_sInf_dom₂ hu hu (@IsUniformGroup.uniformContinuous_div G u _ (h u hu))

@[to_additive]

Depends on / 依赖: IsUniformGroup, IsUniformGroup.mk, IsUniformGroup.uniformContinuous_div, uniformContinuous_div, uniformContinuous_sInf_rng, uniformContinuous_sInf_rng.mpr
-/
theorem isUniformGroup_sInf {us : Set (UniformSpace G)} (h : forall u in us, @IsUniformGroup G u _) :
    @IsUniformGroup G (sInf us) _ :=
@IsUniformGroup.mk G (_) _
    uniformContinuous_sInf_rng.mpr fun u hu =>
      uniformContinuous_sInf_dom₂ hu hu (@IsUniformGroup.uniformContinuous_div G u _ (h u hu))

@[to_additive]
/--
theorem `isUniformGroup_iInf` / 定理 `isUniformGroup_iInf`

English:
theorem isUniformGroup_iInf
  statement: {ι : Sort*} {us' : ι -> UniformSpace G}
  proof: by
  rw [← sInf_range]
  exact isUniformGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

中文:
定理 isUniformGroup_iInf
  结论: {ι : 类型层*} {us' : ι -> 一致空间 G}
  证明: by
  rw [← sInf_range]
  exact isUniformGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]

Depends on / 依赖: Set.forall_mem_range.mpr, forall_mem_range, isUniformGroup_sInf, sInf_range
-/
theorem isUniformGroup_iInf {ι : Sort*} {us' : ι -> UniformSpace G}
    (h' : forall i, @IsUniformGroup G (us' i) _) : @IsUniformGroup G (⨅ i, us' i) _ := by
  rw [← sInf_range]
  exact isUniformGroup_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
/--
theorem `isUniformGroup_inf` / 定理 `isUniformGroup_inf`

English:
theorem isUniformGroup_inf
  statement: {u₁ u₂ : UniformSpace G} (h₁ : @IsUniformGroup G u₁ _)
  proof: by
  rw [inf_eq_iInf]
  refine isUniformGroup_iInf fun b => ?_
  cases b <;> assumption

中文:
定理 isUniformGroup_inf
  结论: {u₁ u₂ : 一致空间 G} (h₁ : @是一致群 G u₁ _)
  证明: by
  rw [inf_eq_iInf]
  refine isUniformGroup_iInf fun b => ?_
  cases b <;> assumption

Depends on / 依赖: inf_eq_iInf, isUniformGroup_iInf
-/
theorem isUniformGroup_inf {u₁ u₂ : UniformSpace G} (h₁ : @IsUniformGroup G u₁ _)
    (h₂ : @IsUniformGroup G u₂ _) : @IsUniformGroup G (u₁ ⊓ u₂) _ := by
  rw [inf_eq_iInf]
  refine isUniformGroup_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

section Comap

@[to_additive]
/--
lemma `IsUniformInducing.isUniformGroup` / 引理 `IsUniformInducing.isUniformGroup`

English:
lemma IsUniformInducing.isUniformGroup
  statement: [UniformSpace G] [UniformSpace H]
  proof: by
    simp_rw [hf.uniformContinuous_iff, Function.comp_def, map_div]
    exact uniformContinuous_div.comp (hf.uniformContinuous.prodMap hf.uniformContinuous)

@[to_additive]

中文:
引理 是UniformInducing.isUniformGroup
  结论: [一致空间 G] [一致空间 H]
  证明: by
    simp_rw [hf.uniformContinuous_iff, Function.comp_def, map_div]
    exact uniformContinuous_div.comp (hf.uniformContinuous.prodMap hf.uniformContinuous)

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, comp_def, hf.uniformContinuous, hf.uniformContinuous.prodMap, hf.uniformContinuous_iff, map_div, prodMap, simp_rw, uniformContinuous, uniformContinuous_div, uniformContinuous_div.comp, uniformContinuous_iff
-/
lemma IsUniformInducing.isUniformGroup [UniformSpace G] [UniformSpace H]
    [IsUniformGroup H] [FunLike hom G H] [MonoidHomClass hom G H]
    (f : hom) (hf : IsUniformInducing f) :
    IsUniformGroup G where
  uniformContinuous_div := by
    simp_rw [hf.uniformContinuous_iff, Function.comp_def, map_div]
    exact uniformContinuous_div.comp (hf.uniformContinuous.prodMap hf.uniformContinuous)

@[to_additive]
/--
theorem `IsUniformGroup.comap` / 定理 `IsUniformGroup.comap`

English:
theorem IsUniformGroup.comap
  statement: {u : UniformSpace H} [IsUniformGroup H]
  proof: letI : UniformSpace G := u.comap f; IsUniformInducing.isUniformGroup f ⟨rfl⟩

中文:
定理 是一致群.comap
  结论: {u : 一致空间 H} [是一致群 H]
  证明: letI : UniformSpace G := u.comap f; IsUniformInducing.isUniformGroup f ⟨rfl⟩
-/
protected theorem IsUniformGroup.comap {u : UniformSpace H} [IsUniformGroup H]
    [FunLike hom G H] [MonoidHomClass hom G H] (f : hom) :
    @IsUniformGroup G (u.comap f) _ :=
  letI : UniformSpace G := u.comap f; IsUniformInducing.isUniformGroup f ⟨rfl⟩

end Comap

section PiProd

@[to_additive]
/--
Instance `Prod.instIsUniformGroup` / 实例 `Prod.instIsUniformGroup`

English:
instance Prod.instIsUniformGroup
  signature: [UniformSpace G] [hG : IsUniformGroup G]
  body: by
  rw [instUniformSpaceProd]
  exact isUniformGroup_inf (.comap <| MonoidHom.fst G H) (.comap <| MonoidHom.snd G H)

@[to_additive]

中文:
实例 积类型.instIsUniformGroup
  签名: [一致空间 G] [hG : 是一致群 G]
  定义体: by
  rw [instUniformSpaceProd]
  exact isUniformGroup_inf (.comap <| MonoidHom.fst G H) (.comap <| MonoidHom.snd G H)

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.fst, MonoidHom.snd, instUniformSpaceProd, isUniformGroup_inf
-/
instance Prod.instIsUniformGroup [UniformSpace G] [hG : IsUniformGroup G]
    [UniformSpace H] [hH : IsUniformGroup H] :
    IsUniformGroup (G × H) := by
  rw [instUniformSpaceProd]
  exact isUniformGroup_inf (.comap <| MonoidHom.fst G H) (.comap <| MonoidHom.snd G H)

@[to_additive]
/--
Instance `Pi.instIsUniformGroup` / 实例 `Pi.instIsUniformGroup`

English:
instance Pi.instIsUniformGroup
  signature: {ι : Type*} {G : ι -> Type*} [forall i, UniformSpace (G i)]
  body: by
  rw [Pi.uniformSpace_eq]
  exact isUniformGroup_iInf fun i => .comap (Pi.evalMonoidHom G i)

中文:
实例 依赖函数类型.instIsUniformGroup
  签名: {ι : 类型} {G : ι -> 类型} [对任意 i, 一致空间 (G i)]
  定义体: by
  rw [Pi.uniformSpace_eq]
  exact isUniformGroup_iInf fun i => .comap (Pi.evalMonoidHom G i)

Depends on / 依赖: Pi.evalMonoidHom, Pi.uniformSpace_eq, evalMonoidHom, isUniformGroup_iInf, uniformSpace_eq
-/
instance Pi.instIsUniformGroup {ι : Type*} {G : ι -> Type*} [forall i, UniformSpace (G i)]
    [forall i, Group (G i)] [forall i, IsUniformGroup (G i)] : IsUniformGroup (forall i, G i) := by
  rw [Pi.uniformSpace_eq]
  exact isUniformGroup_iInf fun i => .comap (Pi.evalMonoidHom G i)

end PiProd

section DiscreteUniformity

/-- The discrete uniformity makes a group a `IsUniformGroup`. -/
@[to_additive /-- The discrete uniformity makes an additive group a `IsUniformAddGroup`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniformSpace
  signature: G] [DiscreteUniformity G] : IsUniformGroup G where
  body: DiscreteUniformity.uniformContinuous (G × G) fun p => p.1 / p.2

中文:
实例 [一致空间
  签名: G] [DiscreteUniformity G] : 是一致群 G where
  定义体: DiscreteUniformity.uniformContinuous (G × G) fun p => p.1 / p.2

Depends on / 依赖: DiscreteUniformity, DiscreteUniformity.uniformContinuous, uniformContinuous
-/
instance [UniformSpace G] [DiscreteUniformity G] : IsUniformGroup G where
  uniformContinuous_div := DiscreteUniformity.uniformContinuous (G × G) fun p => p.1 / p.2

end DiscreteUniformity
