/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# The topological space of `X`-continuous maps

Let `X i` be a family of topological spaces. Let `Z` and `T` be topological spaces.
In this file, we endow the type `ContinuousMapGeneratedBy X Z T` of
`X`-continuous maps `Z → T` with the coarsest topology which makes
the precomposition maps `ContinuousMapGeneratedBy X Z T → C(X i, T)`
continuous for any continuous map `X i → Z`, where `C(X i, T)`
is endowed with the compact-open topology.

If we assume that the spaces `X i` are locally compact and that the products
`X i × X j` are `X`-generated, we obtain that the curryfication of maps induces
a bijection between the type of `X`-continuous maps `Y × Z → T` and the type of
`X`-continuous maps `Z → ContinuousMapGeneratedBy X Y T` for all
topological spaces `Y`, `Z` and `T`.

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/
universe v v' v'' t u

@[expose] public section

variable {ι : Type t} {X : ι -> Type u} [forall i, TopologicalSpace (X i)]
  {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]
  {T : Type v''} [TopologicalSpace T]

namespace Topology.ContinuousMapGeneratedBy

/--
Definition of `precomp` / `precomp` 的定义

English:
definition precomp
  signature: {i : ι} (f : C(X i, Z))
  body: fun g => ⟨_, g.prop f⟩

@[simp]

中文:
定义 precomp
  签名: {i : ι} (f : C(X i, Z))
  定义体: fun g => ⟨_, g.prop f⟩

@[simp]

Depends on / 依赖: g.prop
-/
def precomp {i : ι} (f : C(X i, Z)) : ContinuousMapGeneratedBy X Z T -> C(X i, T) :=
  fun g => ⟨_, g.prop f⟩

@[simp]
/--
lemma `precomp_apply` / 引理 `precomp_apply`

English:
lemma precomp_apply
  given: {i : ι} (f : C(X i, Z)) (g : ContinuousMapGeneratedBy X Z T)
  proof: rfl

中文:
引理 precomp_apply
  条件: {i : ι} (f : C(X i, Z)) (g : 余ntinuousMapGeneratedBy X Z T)
  证明: rfl
-/
lemma precomp_apply {i : ι} (f : C(X i, Z)) (g : ContinuousMapGeneratedBy X Z T) :
    ⇑(precomp f g) = g ∘ f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (ContinuousMapGeneratedBy X Z T)
  body: ⨅ (i : ι) (f : C(X i, Z)), .induced (precomp f) inferInstance

中文:
实例 :
  签名: 拓扑空间 (余ntinuousMapGeneratedBy X Z T)
  定义体: ⨅ (i : ι) (f : C(X i, Z)), .induced (precomp f) inferInstance

Depends on / 依赖: induced, precomp
-/
instance : TopologicalSpace (ContinuousMapGeneratedBy X Z T) :=
  ⨅ (i : ι) (f : C(X i, Z)), .induced (precomp f) inferInstance

/--
lemma `continuous_iff` / 引理 `continuous_iff`

English:
lemma continuous_iff
  given: {A : Type*} [TopologicalSpace A] {φ : A -> ContinuousMapGeneratedBy X Z T}
  proof: by
  simp only [continuous_iInf_rng, continuous_induced_rng]

@[continuity, fun_prop]

中文:
引理 continuous_iff
  条件: {A : 类型} [拓扑空间 A] {φ : A -> 余ntinuousMapGeneratedBy X Z T}
  证明: by
  simp only [continuous_iInf_rng, continuous_induced_rng]

@[continuity, fun_prop]

Depends on / 依赖: continuous_iInf_rng, continuous_induced_rng
-/
lemma continuous_iff {A : Type*} [TopologicalSpace A] {φ : A -> ContinuousMapGeneratedBy X Z T} :
    Continuous φ ↔ forall (i : ι) (f : C(X i, Z)), Continuous (precomp f ∘ φ) := by
  simp only [continuous_iInf_rng, continuous_induced_rng]

@[continuity, fun_prop]
/--
lemma `continuous_precomp` / 引理 `continuous_precomp`

English:
lemma continuous_precomp
  given: {i : ι} (f : C(X i, Z))
  statement: Continuous (precomp (T := T) f)
  proof: by
  rw [continuous_iff_le_induced]
  exact (iInf_le _ i).trans (iInf_le _ _)

中文:
引理 continuous_precomp
  条件: {i : ι} (f : C(X i, Z))
  结论: 连续 (precomp (T := T) f)
  证明: by
  rw [continuous_iff_le_induced]
  exact (iInf_le _ i).trans (iInf_le _ _)

Depends on / 依赖: continuous_iff_le_induced, iInf_le
-/
lemma continuous_precomp {i : ι} (f : C(X i, Z)) : Continuous (precomp (T := T) f) := by
  rw [continuous_iff_le_induced]
  exact (iInf_le _ i).trans (iInf_le _ _)

/--
lemma `continuousGeneratedBy_iff_uncurry` / 引理 `continuousGeneratedBy_iff_uncurry`

English:
lemma continuousGeneratedBy_iff_uncurry
  statement: [forall i, LocallyCompactSpace (X i)]
  proof: by
  simp only [continuousGeneratedBy_def, continuous_iff]
  exact forall_congr' (fun i₁ => forall_congr' (fun f₁ =>
    forall_congr' (fun i₂ => forall_congr' (fun f₂ =>
      ⟨fun h => ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩,
        fun h => (ContinuousMap.curry ⟨_, h⟩).continuous⟩))))

中文:
引理 continuousGeneratedBy_iff_uncurry
  结论: [对任意 i, 局部紧空间 (X i)]
  证明: by
  simp only [continuousGeneratedBy_def, continuous_iff]
  exact forall_congr' (fun i₁ => forall_congr' (fun f₁ =>
    forall_congr' (fun i₂ => forall_congr' (fun f₂ =>
      ⟨fun h => ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩,
        fun h => (ContinuousMap.curry ⟨_, h⟩).continuous⟩))))

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_uncurry_of_continuous, ContinuousMap.curry, continuous, continuousGeneratedBy_def, continuous_iff, continuous_uncurry_of_continuous, forall_congr
-/
lemma continuousGeneratedBy_iff_uncurry [forall i, LocallyCompactSpace (X i)]
    (g : Z -> ContinuousMapGeneratedBy X Y T) :
    ContinuousGeneratedBy X g ↔
      forall ⦃i₁ : ι⦄ (f₁ : C(X i₁, Z)) ⦃i₂ : ι⦄ (f₂ : C(X i₂, Y)) ,
        Continuous (fun (x₁, x₂) => g (f₁ x₁) (f₂ x₂)) := by
  simp only [continuousGeneratedBy_def, continuous_iff]
  exact forall_congr' (fun i₁ => forall_congr' (fun f₁ =>
    forall_congr' (fun i₂ => forall_congr' (fun f₂ =>
      ⟨fun h => ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩,
        fun h => (ContinuousMap.curry ⟨_, h⟩).continuous⟩))))

/--
lemma `continuousGeneratedBy_dom_prod_iff` / 引理 `continuousGeneratedBy_dom_prod_iff`

English:
lemma continuousGeneratedBy_dom_prod_iff
  statement: [forall i j, IsGeneratedBy X (X i × X j)]
  proof: by
  refine ⟨fun h i₁ f₁ i₂ f₂ => ?_, fun h => ?_⟩
  · rw [IsGeneratedBy.continuous_iff X]
    intro j p
    let φ : X i₁ × X i₂ -> Y × Z := fun (x₁, x₂) => (f₂ x₂, f₁ x₁)
    replace h := h.comp (show Continuous φ by fun_prop).continuousGeneratedBy
    rw [continuousGeneratedBy_def] at h
    exact h p
  · rw [continuousGeneratedBy_def]
    intro i f
    exact (h i (ContinuousMap.snd.comp f) i (ContinuousMap.fst.comp f)).comp
      (Continuous.prodMk continuous_id continuous_id)

中文:
引理 continuousGeneratedBy_dom_prod_iff
  结论: [对任意 i j, 是GeneratedBy X (X i × X j)]
  证明: by
  refine ⟨fun h i₁ f₁ i₂ f₂ => ?_, fun h => ?_⟩
  · rw [IsGeneratedBy.continuous_iff X]
    intro j p
    let φ : X i₁ × X i₂ -> Y × Z := fun (x₁, x₂) => (f₂ x₂, f₁ x₁)
    replace h := h.comp (show Continuous φ by fun_prop).continuousGeneratedBy
    rw [continuousGeneratedBy_def] at h
    exact h p
  · rw [continuousGeneratedBy_def]
    intro i f
    exact (h i (ContinuousMap.snd.comp f) i (ContinuousMap.fst.comp f)).comp
      (Continuous.prodMk continuous_id continuous_id)

Depends on / 依赖: Continuous, Continuous.prodMk, ContinuousMap, ContinuousMap.fst.comp, ContinuousMap.snd.comp, IsGeneratedBy, IsGeneratedBy.continuous_iff, continuousGeneratedBy, continuousGeneratedBy_def, continuous_id, continuous_iff, fun_prop, h.comp, prodMk, replace
-/
lemma continuousGeneratedBy_dom_prod_iff [forall i j, IsGeneratedBy X (X i × X j)]
    (g : Y × Z -> T) :
    ContinuousGeneratedBy X g ↔
      forall (i₁ : ι) (f₁ : C(X i₁, Z)) (i₂ : ι) (f₂ : C(X i₂, Y)),
        Continuous (fun (x₁, x₂) => g ⟨f₂ x₂, f₁ x₁⟩) := by
  refine ⟨fun h i₁ f₁ i₂ f₂ => ?_, fun h => ?_⟩
  · rw [IsGeneratedBy.continuous_iff X]
    intro j p
    let φ : X i₁ × X i₂ -> Y × Z := fun (x₁, x₂) => (f₂ x₂, f₁ x₁)
    replace h := h.comp (show Continuous φ by fun_prop).continuousGeneratedBy
    rw [continuousGeneratedBy_def] at h
    exact h p
  · rw [continuousGeneratedBy_def]
    intro i f
    exact (h i (ContinuousMap.snd.comp f) i (ContinuousMap.fst.comp f)).comp
      (Continuous.prodMk continuous_id continuous_id)

variable [forall i, LocallyCompactSpace (X i)] [forall i j, IsGeneratedBy X (X i × X j)]

/--
Definition of `curryEquiv` / `curryEquiv` 的定义

English:
definition curryEquiv
  signature: :
  body: { toFun z := g.comp ⟨fun y => (y, z), (Continuous.prodMk_left z).continuousGeneratedBy⟩
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }
  invFun g :=
    { toFun x := g x.2 x.1
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }

@[simp]

中文:
定义 curryEquiv
  签名: :
  定义体: { toFun z := g.comp ⟨fun y => (y, z), (Continuous.prodMk_left z).continuousGeneratedBy⟩
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }
  invFun g :=
    { toFun x := g x.2 x.1
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }

@[simp]

Depends on / 依赖: Continuous, Continuous.prodMk_left, continuousGeneratedBy, continuousGeneratedBy_dom_prod_iff, continuousGeneratedBy_iff_uncurry, g.comp, g.prop, invFun, prodMk_left
-/
def curryEquiv :
  ContinuousMapGeneratedBy X (Y × Z) T ≃
    ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T) where
  toFun g :=
    { toFun z := g.comp ⟨fun y => (y, z), (Continuous.prodMk_left z).continuousGeneratedBy⟩
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }
  invFun g :=
    { toFun x := g x.2 x.1
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using! g.prop }

@[simp]
/--
lemma `curryEquiv_apply_apply` / 引理 `curryEquiv_apply_apply`

English:
lemma curryEquiv_apply_apply
  given: (g : ContinuousMapGeneratedBy X (Y × Z) T) (y : Y) (z : Z)
  proof: rfl

@[simp]

中文:
引理 curryEquiv_apply_apply
  条件: (g : 余ntinuousMapGeneratedBy X (Y × Z) T) (y : Y) (z : Z)
  证明: rfl

@[simp]
-/
lemma curryEquiv_apply_apply (g : ContinuousMapGeneratedBy X (Y × Z) T) (y : Y) (z : Z) :
    curryEquiv g z y = g (y, z) := rfl

@[simp]
/--
lemma `curryEquiv_symm_apply` / 引理 `curryEquiv_symm_apply`

English:
lemma curryEquiv_symm_apply
  statement: (g : ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T))
  proof: rfl

中文:
引理 curryEquiv_symm_apply
  结论: (g : 余ntinuousMapGeneratedBy X Z (余ntinuousMapGeneratedBy X Y T))
  证明: rfl
-/
lemma curryEquiv_symm_apply (g : ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T))
    (y : Y) (z : Z) :
    curryEquiv.symm g (y, z) = g z y := rfl

/--
Definition of `ev` / `ev` 的定义

English:
definition ev
  signature: : ContinuousMapGeneratedBy X (Y × ContinuousMapGeneratedBy X Y Z) Z
  body: curryEquiv.symm .id

@[simp]

中文:
定义 ev
  签名: : 余ntinuousMapGeneratedBy X (Y × 余ntinuousMapGeneratedBy X Y Z) Z
  定义体: curryEquiv.symm .id

@[simp]

Depends on / 依赖: curryEquiv, curryEquiv.symm
-/
def ev : ContinuousMapGeneratedBy X (Y × ContinuousMapGeneratedBy X Y Z) Z :=
  curryEquiv.symm .id

@[simp]
/--
lemma `ev_apply` / 引理 `ev_apply`

English:
lemma ev_apply
  given: (y : Y) (f : ContinuousMapGeneratedBy X Y Z)
  proof: rfl

中文:
引理 ev_apply
  条件: (y : Y) (f : 余ntinuousMapGeneratedBy X Y Z)
  证明: rfl
-/
lemma ev_apply (y : Y) (f : ContinuousMapGeneratedBy X Y Z) :
    ev (y, f) = f y := rfl

/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: (p : ContinuousMapGeneratedBy X Z T)
  body: curryEquiv (p.comp ev)

@[simp]

中文:
定义 postcomp
  签名: (p : 余ntinuousMapGeneratedBy X Z T)
  定义体: curryEquiv (p.comp ev)

@[simp]

Depends on / 依赖: curryEquiv, p.comp
-/
def postcomp (p : ContinuousMapGeneratedBy X Z T) :
    ContinuousMapGeneratedBy X (ContinuousMapGeneratedBy X Y Z)
      (ContinuousMapGeneratedBy X Y T) :=
  curryEquiv (p.comp ev)

@[simp]
/--
lemma `postcomp_apply` / 引理 `postcomp_apply`

English:
lemma postcomp_apply
  given: (p : ContinuousMapGeneratedBy X Z T) (g : ContinuousMapGeneratedBy X Y Z)
  proof: rfl

中文:
引理 postcomp_apply
  条件: (p : 余ntinuousMapGeneratedBy X Z T) (g : 余ntinuousMapGeneratedBy X Y Z)
  证明: rfl
-/
lemma postcomp_apply (p : ContinuousMapGeneratedBy X Z T) (g : ContinuousMapGeneratedBy X Y Z) :
    p.postcomp g = p.comp g := rfl

end Topology.ContinuousMapGeneratedBy
