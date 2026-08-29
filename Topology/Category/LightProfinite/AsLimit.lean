/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.LightProfinite.Basic
/-!
# Light profinite sets as limits of finite sets.

We show that any light profinite set is isomorphic to a sequential limit of finite sets.

The limit cone for `S : LightProfinite` is `S.asLimitCone`, the fact that it's a limit is
`S.asLimit`.

We also prove that the projection and transition maps in this limit are surjective.

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits CompHausLike

namespace LightProfinite

universe u

variable (S : LightProfinite.{u})

/--
Definition of `fintypeDiagram` / `fintypeDiagram` 的定义

English:
abbreviation fintypeDiagram
  signature: : Natᵒᵖ ⥤ FintypeCat
  body: S.toLightDiagram.diagram

中文:
缩写 fintypeDiagram
  签名: : 自然数ᵒᵖ ⥤ FintypeCat
  定义体: S.toLightDiagram.diagram

Depends on / 依赖: S.toLightDiagram.diagram, diagram, toLightDiagram
-/
abbrev fintypeDiagram : Natᵒᵖ ⥤ FintypeCat := S.toLightDiagram.diagram

/--
Definition of `diagram` / `diagram` 的定义

English:
abbreviation diagram
  signature: : Natᵒᵖ ⥤ LightProfinite
  body: S.fintypeDiagram ⋙ FintypeCat.toLightProfinite

中文:
缩写 diagram
  签名: : 自然数ᵒᵖ ⥤ LightProfinite
  定义体: S.fintypeDiagram ⋙ FintypeCat.toLightProfinite

Depends on / 依赖: FintypeCat, FintypeCat.toLightProfinite, S.fintypeDiagram, fintypeDiagram, toLightProfinite
-/
abbrev diagram : Natᵒᵖ ⥤ LightProfinite := S.fintypeDiagram ⋙ FintypeCat.toLightProfinite

/--
Definition of `asLimitConeAux` / `asLimitConeAux` 的定义

English:
definition asLimitConeAux
  signature: : Cone S.diagram
  body: let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc

中文:
定义 asLimitConeAux
  签名: : 锥 S.diagram
  定义体: let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc

Depends on / 依赖: IsLimit, S.diagram, S.toLightDiagram.cone, S.toLightDiagram.isLimit, diagram, isLimit, liftLimit, lightToProfinite, toLightDiagram
-/
def asLimitConeAux : Cone S.diagram :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftLimit hc

/--
Definition of `isoMapCone` / `isoMapCone` 的定义

English:
definition isoMapCone
  signature: : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone
  body: let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc

中文:
定义 isoMapCone
  签名: : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone
  定义体: let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc

Depends on / 依赖: IsLimit, S.diagram, S.toLightDiagram.cone, S.toLightDiagram.isLimit, diagram, isLimit, liftedLimitMapsToOriginal, lightToProfinite, toLightDiagram
-/
def isoMapCone : lightToProfinite.mapCone S.asLimitConeAux ≅ S.toLightDiagram.cone :=
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  liftedLimitMapsToOriginal hc

/--
Definition of `asLimitAux` / `asLimitAux` 的定义

English:
definition asLimitAux
  signature: : IsLimit S.asLimitConeAux
  body: let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

中文:
定义 asLimitAux
  签名: : 是极限 S.asLimitConeAux
  定义体: let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

Depends on / 依赖: IsLimit, S.asLimitConeAux, S.isoMapCone.symm, S.toLightDiagram.isLimit.ofIsoLimit, asLimitConeAux, isLimit, isLimitOfReflects, isoMapCone, lightToProfinite, lightToProfinite.mapCone, mapCone, ofIsoLimit, toLightDiagram
-/
def asLimitAux : IsLimit S.asLimitConeAux :=
  let hc : IsLimit (lightToProfinite.mapCone S.asLimitConeAux) :=
    S.toLightDiagram.isLimit.ofIsoLimit S.isoMapCone.symm
  isLimitOfReflects lightToProfinite hc

/--
Definition of `asLimitCone` / `asLimitCone` 的定义

English:
definition asLimitCone
  signature: : Cone S.diagram where
  body: S
  π := {
    app := fun n => (lightToProfiniteFullyFaithful.preimageIso <|
      (Cone.forget _).mapIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ => by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }

中文:
定义 asLimitCone
  签名: : 锥 S.diagram where
  定义体: S
  π := {
    app := fun n => (lightToProfiniteFullyFaithful.preimageIso <|
      (Cone.forget _).mapIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ => by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }
-/
def asLimitCone : Cone S.diagram where
  pt := S
  π := {
    app := fun n => (lightToProfiniteFullyFaithful.preimageIso <|
      (Cone.forget _).mapIso S.isoMapCone).inv ≫ S.asLimitConeAux.π.app n
    naturality := fun _ _ _ => by simp only [Category.assoc, S.asLimitConeAux.w]; rfl }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `asLimit` / `asLimit` 的定义

English:
definition asLimit
  signature: : IsLimit S.asLimitCone
  body: S.asLimitAux.ofIsoLimit
  Cone.ext (lightToProfiniteFullyFaithful.preimageIso <|
    (Cone.forget _).mapIso S.isoMapCone) (fun _ => by rw [← @Iso.inv_comp_eq]; rfl)

中文:
定义 asLimit
  签名: : 是极限 S.asLimitCone
  定义体: S.asLimitAux.ofIsoLimit
  Cone.ext (lightToProfiniteFullyFaithful.preimageIso <|
    (Cone.forget _).mapIso S.isoMapCone) (fun _ => by rw [← @Iso.inv_comp_eq]; rfl)

Depends on / 依赖: S.asLimitAux.ofIsoLimit, asLimitAux, ofIsoLimit
-/
def asLimit : IsLimit S.asLimitCone := S.asLimitAux.ofIsoLimit
  Cone.ext (lightToProfiniteFullyFaithful.preimageIso <|
    (Cone.forget _).mapIso S.isoMapCone) (fun _ => by rw [← @Iso.inv_comp_eq]; rfl)

/--
Definition of `lim` / `lim` 的定义

English:
definition lim
  signature: : Limits.LimitCone S.diagram
  body: ⟨S.asLimitCone, S.asLimit⟩

中文:
定义 lim
  签名: : Limits.极限锥 S.diagram
  定义体: ⟨S.asLimitCone, S.asLimit⟩

Depends on / 依赖: S.asLimit, S.asLimitCone, asLimit, asLimitCone
-/
def lim : Limits.LimitCone S.diagram := ⟨S.asLimitCone, S.asLimit⟩

/--
Definition of `proj` / `proj` 的定义

English:
abbreviation proj
  signature: (n : Nat)
  body: S.asLimitCone.π.app ⟨n⟩

中文:
缩写 proj
  签名: (n : 自然数)
  定义体: S.asLimitCone.π.app ⟨n⟩

Depends on / 依赖: S.asLimitCone, asLimitCone
-/
abbrev proj (n : Nat) : S ⟶ S.diagram.obj ⟨n⟩ := S.asLimitCone.π.app ⟨n⟩

/--
lemma `lightToProfinite_map_proj_eq` / 引理 `lightToProfinite_map_proj_eq`

English:
lemma lightToProfinite_map_proj_eq
  given: (n : Nat)
  statement: lightToProfinite.map (S.proj n) =
  proof: by
  simp only [toCompHausLike_map]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact liftedLimitMapsToOriginal_inv_map_π hc _

中文:
引理 lightToProfinite_map_proj_eq
  条件: (n : 自然数)
  结论: lightToProfinite.map (S.proj n) =
  证明: by
  simp only [toCompHausLike_map]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact liftedLimitMapsToOriginal_inv_map_π hc _

Depends on / 依赖: IsLimit, S.diagram, S.toLightDiagram.cone, S.toLightDiagram.isLimit, diagram, isLimit, lightToProfinite, toCompHausLike_map, toLightDiagram
-/
lemma lightToProfinite_map_proj_eq (n : Nat) : lightToProfinite.map (S.proj n) =
    (lightToProfinite.obj S).asLimitCone.π.app _ := by
  simp only [toCompHausLike_map]
  let c : Cone (S.diagram ⋙ lightToProfinite) := S.toLightDiagram.cone
  let hc : IsLimit c := S.toLightDiagram.isLimit
  exact liftedLimitMapsToOriginal_inv_map_π hc _

/--
lemma `proj_surjective` / 引理 `proj_surjective`

English:
lemma proj_surjective
  given: (n : Nat)
  statement: Function.Surjective (S.proj n)
  proof: by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _

中文:
引理 proj_surjective
  条件: (n : 自然数)
  结论: 函数.满射 (S.proj n)
  证明: by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _

Depends on / 依赖: DiscreteQuotient, DiscreteQuotient.proj_surjective, Function, Function.Surjective, S.proj, Surjective, lightToProfinite, lightToProfinite.map, lightToProfinite_map_proj_eq, proj_surjective
-/
lemma proj_surjective (n : Nat) : Function.Surjective (S.proj n) := by
  change Function.Surjective (lightToProfinite.map (S.proj n))
  rw [lightToProfinite_map_proj_eq]
  exact DiscreteQuotient.proj_surjective _

/--
Definition of `component` / `component` 的定义

English:
abbreviation component
  signature: (n : Nat)
  body: S.diagram.obj ⟨n⟩

中文:
缩写 component
  签名: (n : 自然数)
  定义体: S.diagram.obj ⟨n⟩

Depends on / 依赖: S.diagram.obj, diagram
-/
abbrev component (n : Nat) : LightProfinite := S.diagram.obj ⟨n⟩

/--
Definition of `transitionMap` / `transitionMap` 的定义

English:
abbreviation transitionMap
  signature: (n : Nat)
  body: S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

中文:
缩写 transitionMap
  签名: (n : 自然数)
  定义体: S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

Depends on / 依赖: Nat.le_succ, S.diagram.map, diagram, homOfLE, le_succ
-/
abbrev transitionMap (n : Nat) : S.component (n + 1) ⟶ S.component n :=
  S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩

/--
Definition of `transitionMapLE` / `transitionMapLE` 的定义

English:
abbreviation transitionMapLE
  signature: {n m : Nat} (h : n <= m)
  body: S.diagram.map ⟨homOfLE h⟩

中文:
缩写 transitionMapLE
  签名: {n m : 自然数} (h : n <= m)
  定义体: S.diagram.map ⟨homOfLE h⟩

Depends on / 依赖: S.diagram.map, diagram, homOfLE
-/
abbrev transitionMapLE {n m : Nat} (h : n <= m) : S.component m ⟶ S.component n :=
  S.diagram.map ⟨homOfLE h⟩

/--
lemma `proj_comp_transitionMap` / 引理 `proj_comp_transitionMap`

English:
lemma proj_comp_transitionMap
  given: (n : Nat)
  proof: S.asLimitCone.w (homOfLE (Nat.le_succ n)).op

中文:
引理 proj_comp_transitionMap
  条件: (n : 自然数)
  证明: S.asLimitCone.w (homOfLE (Nat.le_succ n)).op

Depends on / 依赖: Nat.le_succ, S.asLimitCone.w, asLimitCone, homOfLE, le_succ
-/
lemma proj_comp_transitionMap (n : Nat) :
    S.proj (n + 1) ≫ S.diagram.map ⟨homOfLE (Nat.le_succ _)⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE (Nat.le_succ n)).op

/--
lemma `proj_comp_transitionMap'` / 引理 `proj_comp_transitionMap'`

English:
lemma proj_comp_transitionMap'
  given: (n : Nat)
  statement: S.transitionMap n ∘ S.proj (n + 1) = S.proj n
  proof: by
  rw [← S.proj_comp_transitionMap n]
  rfl

中文:
引理 proj_comp_transitionMap'
  条件: (n : 自然数)
  结论: S.transitionMap n ∘ S.proj (n + 1) = S.proj n
  证明: by
  rw [← S.proj_comp_transitionMap n]
  rfl

Depends on / 依赖: S.proj_comp_transitionMap, proj_comp_transitionMap
-/
lemma proj_comp_transitionMap' (n : Nat) : S.transitionMap n ∘ S.proj (n + 1) = S.proj n := by
  rw [← S.proj_comp_transitionMap n]
  rfl

/--
lemma `proj_comp_transitionMapLE` / 引理 `proj_comp_transitionMapLE`

English:
lemma proj_comp_transitionMapLE
  given: {n m : Nat} (h : n <= m)
  proof: S.asLimitCone.w (homOfLE h).op

中文:
引理 proj_comp_transitionMapLE
  条件: {n m : 自然数} (h : n <= m)
  证明: S.asLimitCone.w (homOfLE h).op

Depends on / 依赖: S.asLimitCone.w, asLimitCone, homOfLE
-/
lemma proj_comp_transitionMapLE {n m : Nat} (h : n <= m) :
    S.proj m ≫ S.diagram.map ⟨homOfLE h⟩ = S.proj n :=
  S.asLimitCone.w (homOfLE h).op

/--
lemma `proj_comp_transitionMapLE'` / 引理 `proj_comp_transitionMapLE'`

English:
lemma proj_comp_transitionMapLE'
  given: {n m : Nat} (h : n <= m)
  proof: by
  rw [← S.proj_comp_transitionMapLE h]
  rfl

中文:
引理 proj_comp_transitionMapLE'
  条件: {n m : 自然数} (h : n <= m)
  证明: by
  rw [← S.proj_comp_transitionMapLE h]
  rfl

Depends on / 依赖: S.proj_comp_transitionMapLE, proj_comp_transitionMapLE
-/
lemma proj_comp_transitionMapLE' {n m : Nat} (h : n <= m) :
    S.transitionMapLE h ∘ S.proj m = S.proj n := by
  rw [← S.proj_comp_transitionMapLE h]
  rfl

/--
lemma `surjective_transitionMap` / 引理 `surjective_transitionMap`

English:
lemma surjective_transitionMap
  given: (n : Nat)
  statement: Function.Surjective (S.transitionMap n)
  proof: by
  apply Function.Surjective.of_comp (g := S.proj (n + 1))
  simpa only [proj_comp_transitionMap'] using S.proj_surjective n

中文:
引理 surjective_transitionMap
  条件: (n : 自然数)
  结论: 函数.满射 (S.transitionMap n)
  证明: by
  apply Function.Surjective.of_comp (g := S.proj (n + 1))
  simpa only [proj_comp_transitionMap'] using S.proj_surjective n

Depends on / 依赖: Function, Function.Surjective.of_comp, S.proj, S.proj_surjective, Surjective, of_comp, proj_comp_transitionMap, proj_surjective
-/
lemma surjective_transitionMap (n : Nat) : Function.Surjective (S.transitionMap n) := by
  apply Function.Surjective.of_comp (g := S.proj (n + 1))
  simpa only [proj_comp_transitionMap'] using S.proj_surjective n

/--
lemma `surjective_transitionMapLE` / 引理 `surjective_transitionMapLE`

English:
lemma surjective_transitionMapLE
  given: {n m : Nat} (h : n <= m)
  proof: by
  apply Function.Surjective.of_comp (g := S.proj m)
  simpa only [proj_comp_transitionMapLE'] using S.proj_surjective n

中文:
引理 surjective_transitionMapLE
  条件: {n m : 自然数} (h : n <= m)
  证明: by
  apply Function.Surjective.of_comp (g := S.proj m)
  simpa only [proj_comp_transitionMapLE'] using S.proj_surjective n

Depends on / 依赖: Function, Function.Surjective.of_comp, S.proj, S.proj_surjective, Surjective, of_comp, proj_comp_transitionMapLE, proj_surjective
-/
lemma surjective_transitionMapLE {n m : Nat} (h : n <= m) :
    Function.Surjective (S.transitionMapLE h) := by
  apply Function.Surjective.of_comp (g := S.proj m)
  simpa only [proj_comp_transitionMapLE'] using S.proj_surjective n

end LightProfinite
