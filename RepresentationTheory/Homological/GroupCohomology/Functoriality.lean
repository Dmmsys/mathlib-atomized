/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Functoriality of group cohomology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `H`-representation
`A`, a `k`-linear `G`-representation `B`, and a representation morphism `Res(f)(A) ⟶ B`, we get
a cochain map `inhomogeneousCochains A ⟶ inhomogeneousCochains B` and hence maps on
cohomology `Hⁿ(H, A) ⟶ Hⁿ(G, B)`.
We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupCohomology.cochainsMap f φ` is the map `inhomogeneousCochains A ⟶ inhomogeneousCochains B`
  induced by a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.map f φ n` is the map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` induced by a group
  homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.H1InfRes A S` is the short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` for
  a normal subgroup `S ≤ G` and a `G`-representation `A`.

-/

@[expose] public section

universe v u

namespace groupCohomology
open Rep CategoryTheory Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k H} {B : Rep k G} (f : G ->* H) (φ : res f A ⟶ B) (n : Nat)

section

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: {f₁ f₂ : G ->* H} (h : f₁ = f₂) {φ : res f₁ A ⟶ B} {T : Type*}
  proof: by
  subst h
  rfl

中文:
定理 congr
  结论: {f₁ f₂ : G ->* H} (h : f₁ = f₂) {φ : res f₁ A ⟶ B} {T : 类型}
  证明: by
  subst h
  rfl
-/
theorem congr {f₁ f₂ : G ->* H} (h : f₁ = f₂) {φ : res f₁ A ⟶ B} {T : Type*}
    (F : (f : G ->* H) -> (φ : res f A ⟶ B) -> T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the chain map sending `x : Hⁿ → A` to `(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
@[simps! -isSimp f f_hom]
/--
Definition of `cochainsMap` / `cochainsMap` 的定义

English:
definition cochainsMap
  signature: :
  body: ModuleCat.ofHom
    φ.hom.toLinearMap.compLeft (Fin i -> G) ∘ₗ LinearMap.funLeft k A (fun x : Fin i -> G => (f ∘ x))
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simpa [inhomogeneousCochains.d_hom_apply, Fin.comp_contractNth, CochainComplex.of.d]
      using! (hom_comm_apply φ _ _).symm

中文:
定义 cochainsMap
  签名: :
  定义体: ModuleCat.ofHom
    φ.hom.toLinearMap.compLeft (Fin i -> G) ∘ₗ LinearMap.funLeft k A (fun x : Fin i -> G => (f ∘ x))
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simpa [inhomogeneousCochains.d_hom_apply, Fin.comp_contractNth, CochainComplex.of.d]
      using! (hom_comm_apply φ _ _).symm

Depends on / 依赖: ModuleCat, ModuleCat.ofHom
-/
noncomputable def cochainsMap :
    inhomogeneousCochains A ⟶ inhomogeneousCochains B where
f i := ModuleCat.ofHom
    φ.hom.toLinearMap.compLeft (Fin i -> G) ∘ₗ LinearMap.funLeft k A (fun x : Fin i -> G => (f ∘ x))
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simpa [inhomogeneousCochains.d_hom_apply, Fin.comp_contractNth, CochainComplex.of.d]
      using! (hom_comm_apply φ _ _).symm

@[simp]
/--
lemma `cochainsMap_id` / 引理 `cochainsMap_id`

English:
lemma cochainsMap_id
  proof: by
  rfl

@[simp]

中文:
引理 cochainsMap_id
  证明: by
  rfl

@[simp]
-/
lemma cochainsMap_id :
    cochainsMap (MonoidHom.id _) (𝟙 A) = 𝟙 (inhomogeneousCochains A) := by
  rfl

@[simp]
/--
lemma `cochainsMap_id_f_hom_eq_compLeft` / 引理 `cochainsMap_id_f_hom_eq_compLeft`

English:
lemma cochainsMap_id_f_hom_eq_compLeft
  given: {A B : Rep k G} (f : A ⟶ B) (i : Nat)
  proof: rfl

@[reassoc]

中文:
引理 cochainsMap_id_f_hom_eq_compLeft
  条件: {A B : Rep k G} (f : A ⟶ B) (i : 自然数)
  证明: rfl

@[reassoc]
-/
lemma cochainsMap_id_f_hom_eq_compLeft {A B : Rep k G} (f : A ⟶ B) (i : Nat) :
    ((cochainsMap (MonoidHom.id G) f).f i).hom = f.hom.toLinearMap.compLeft _ := rfl

@[reassoc]
/--
lemma `cochainsMap_comp` / 引理 `cochainsMap_comp`

English:
lemma cochainsMap_comp
  statement: {G H K : Type u} [Group G] [Group H]
  proof: by
  rfl

@[reassoc]

中文:
引理 cochainsMap_comp
  结论: {G H K : 类型u} [群 G] [群 H]
  证明: by
  rfl

@[reassoc]
-/
lemma cochainsMap_comp {G H K : Type u} [Group G] [Group H]
    [Group K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) :
    cochainsMap (f.comp g) ((resFunctor g).map φ ≫ ψ) =
      cochainsMap f φ ≫ cochainsMap g ψ := by
  rfl

@[reassoc]
/--
lemma `cochainsMap_id_comp` / 引理 `cochainsMap_id_comp`

English:
lemma cochainsMap_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: by
  rfl

@[simp]

中文:
引理 cochainsMap_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: by
  rfl

@[simp]
-/
lemma cochainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    cochainsMap (MonoidHom.id G) (φ ≫ ψ) =
      cochainsMap (MonoidHom.id G) φ ≫ cochainsMap (MonoidHom.id G) ψ := by
  rfl

@[simp]
/--
lemma `cochainsMap_zero` / 引理 `cochainsMap_zero`

English:
lemma cochainsMap_zero
  statement: cochainsMap (A := A) (B := B) f 0 = 0
  proof: by rfl

中文:
引理 cochainsMap_zero
  结论: cochainsMap (A := A) (B := B) f 0 = 0
  证明: by rfl
-/
lemma cochainsMap_zero : cochainsMap (A := A) (B := B) f 0 = 0 := by rfl

/--
lemma `cochainsMap_f_map_mono` / 引理 `cochainsMap_f_map_mono`

English:
lemma cochainsMap_f_map_mono
  given: (hf : Function.Surjective f) [Mono φ] (i : Nat)
  proof: by
  simpa [ModuleCat.mono_iff_injective] using!
((Rep.mono_iff_injective φ).1 inferInstance).comp_left.comp
    LinearMap.funLeft_injective_of_surjective k A _ hf.comp_left

中文:
引理 cochainsMap_f_map_mono
  条件: (hf : 函数.满射 f) [单态射 φ] (i : 自然数)
  证明: by
  simpa [ModuleCat.mono_iff_injective] using!
((Rep.mono_iff_injective φ).1 inferInstance).comp_left.comp
    LinearMap.funLeft_injective_of_surjective k A _ hf.comp_left

Depends on / 依赖: LinearMap, LinearMap.funLeft_injective_of_surjective, ModuleCat, ModuleCat.mono_iff_injective, Rep.mono_iff_injective, comp_left, comp_left.comp, funLeft_injective_of_surjective, hf.comp_left, mono_iff_injective
-/
lemma cochainsMap_f_map_mono (hf : Function.Surjective f) [Mono φ] (i : Nat) :
    Mono ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using!
((Rep.mono_iff_injective φ).1 inferInstance).comp_left.comp
    LinearMap.funLeft_injective_of_surjective k A _ hf.comp_left

/--
Instance `cochainsMap_id_f_map_mono` / 实例 `cochainsMap_id_f_map_mono`

English:
instance cochainsMap_id_f_map_mono
  signature: {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : Nat)
  body: cochainsMap_f_map_mono (MonoidHom.id G) φ (fun x => ⟨x, rfl⟩) i

中文:
实例 cochainsMap_id_f_map_mono
  签名: {A B : Rep k G} (φ : A ⟶ B) [单态射 φ] (i : 自然数)
  定义体: cochainsMap_f_map_mono (MonoidHom.id G) φ (fun x => ⟨x, rfl⟩) i

Depends on / 依赖: MonoidHom, MonoidHom.id, cochainsMap_f_map_mono
-/
instance cochainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : Nat) :
    Mono ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_mono (MonoidHom.id G) φ (fun x => ⟨x, rfl⟩) i

/--
lemma `cochainsMap_f_map_epi` / 引理 `cochainsMap_f_map_epi`

English:
lemma cochainsMap_f_map_epi
  given: (hf : Function.Injective f) [Epi φ] (i : Nat)
  proof: by
  simpa [ModuleCat.epi_iff_surjective] using!
((Rep.epi_iff_surjective φ).1 inferInstance).comp_left.comp
    LinearMap.funLeft_surjective_of_injective k A _ hf.comp_left

中文:
引理 cochainsMap_f_map_epi
  条件: (hf : 函数.单射 f) [满态射 φ] (i : 自然数)
  证明: by
  simpa [ModuleCat.epi_iff_surjective] using!
((Rep.epi_iff_surjective φ).1 inferInstance).comp_left.comp
    LinearMap.funLeft_surjective_of_injective k A _ hf.comp_left

Depends on / 依赖: LinearMap, LinearMap.funLeft_surjective_of_injective, ModuleCat, ModuleCat.epi_iff_surjective, Rep.epi_iff_surjective, comp_left, comp_left.comp, epi_iff_surjective, funLeft_surjective_of_injective, hf.comp_left
-/
lemma cochainsMap_f_map_epi (hf : Function.Injective f) [Epi φ] (i : Nat) :
    Epi ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using!
((Rep.epi_iff_surjective φ).1 inferInstance).comp_left.comp
    LinearMap.funLeft_surjective_of_injective k A _ hf.comp_left

/--
Instance `cochainsMap_id_f_map_epi` / 实例 `cochainsMap_id_f_map_epi`

English:
instance cochainsMap_id_f_map_epi
  signature: {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : Nat)
  body: cochainsMap_f_map_epi (MonoidHom.id G) φ (fun _ _ h => h) i

中文:
实例 cochainsMap_id_f_map_epi
  签名: {A B : Rep k G} (φ : A ⟶ B) [满态射 φ] (i : 自然数)
  定义体: cochainsMap_f_map_epi (MonoidHom.id G) φ (fun _ _ h => h) i

Depends on / 依赖: MonoidHom, MonoidHom.id, cochainsMap_f_map_epi
-/
instance cochainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : Nat) :
    Epi ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_epi (MonoidHom.id G) φ (fun _ _ h => h) i

/--
Definition of `cocyclesMap` / `cocyclesMap` 的定义

English:
abbreviation cocyclesMap
  signature: (n : Nat)
  body: HomologicalComplex.cyclesMap (cochainsMap f φ) n

中文:
缩写 cocyclesMap
  签名: (n : 自然数)
  定义体: HomologicalComplex.cyclesMap (cochainsMap f φ) n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap, cochainsMap, cyclesMap
-/
noncomputable abbrev cocyclesMap (n : Nat) :
    groupCohomology.cocycles A n ⟶ groupCohomology.cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap f φ) n

/--
lemma `cochainsMap_congr` / 引理 `cochainsMap_congr`

English:
lemma cochainsMap_congr
  statement: {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
  proof: by
  subst hfg; congr; ext; simp [hφψ]

@[simp]

中文:
引理 cochainsMap_congr
  结论: {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
  证明: by
  subst hfg; congr; ext; simp [hφψ]

@[simp]
-/
lemma cochainsMap_congr {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
    (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) :
    cochainsMap f φ = cochainsMap g ψ := by
  subst hfg; congr; ext; simp [hφψ]

@[simp]
/--
lemma `cocyclesMap_id` / 引理 `cocyclesMap_id`

English:
lemma cocyclesMap_id
  statement: cocyclesMap (MonoidHom.id G) (𝟙 B) n = 𝟙 _
  proof: HomologicalComplex.cyclesMap_id _ _

@[reassoc]

中文:
引理 cocyclesMap_id
  结论: cocyclesMap (幺半群态射.id G) (𝟙 B) n = 𝟙 _
  证明: HomologicalComplex.cyclesMap_id _ _

@[reassoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap_id, cyclesMap_id
-/
lemma cocyclesMap_id : cocyclesMap (MonoidHom.id G) (𝟙 B) n = 𝟙 _ :=
  HomologicalComplex.cyclesMap_id _ _

@[reassoc]
/--
lemma `cocyclesMap_comp` / 引理 `cocyclesMap_comp`

English:
lemma cocyclesMap_comp
  statement: {G H K : Type u} [Group G] [Group H]
  proof: by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

@[reassoc]

中文:
引理 cocyclesMap_comp
  结论: {G H K : 类型u} [群 G] [群 H]
  证明: by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

@[reassoc]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap_comp, cochainsMap_comp, cocyclesMap, cyclesMap_comp
-/
lemma cocyclesMap_comp {G H K : Type u} [Group G] [Group H]
    [Group K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) (n : Nat) :
    cocyclesMap (f.comp g) ((resFunctor g).map φ ≫ ψ) n =
      cocyclesMap f φ n ≫ cocyclesMap g ψ n := by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

@[reassoc]
/--
theorem `cocyclesMap_id_comp` / 定理 `cocyclesMap_id_comp`

English:
theorem cocyclesMap_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat)
  proof: by
  simp [cocyclesMap, cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

中文:
定理 cocyclesMap_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : 自然数)
  证明: by
  simp [cocyclesMap, cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap_comp, cochainsMap_id_comp, cocyclesMap, cyclesMap_comp
-/
theorem cocyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat) :
    cocyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cocyclesMap (MonoidHom.id G) φ n ≫ cocyclesMap (MonoidHom.id G) ψ n := by
  simp [cocyclesMap, cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: (n : Nat)
  body: HomologicalComplex.homologyMap (cochainsMap f φ) n

中文:
缩写 map
  签名: (n : 自然数)
  定义体: HomologicalComplex.homologyMap (cochainsMap f φ) n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap, cochainsMap, homologyMap
-/
noncomputable abbrev map (n : Nat) :
    groupCohomology A n ⟶ groupCohomology B n :=
  HomologicalComplex.homologyMap (cochainsMap f φ) n

/--
lemma `map_congr` / 引理 `map_congr`

English:
lemma map_congr
  statement: {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
  proof: by
  subst hfg; congr; ext; simp [hφψ]

中文:
引理 map_congr
  结论: {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
  证明: by
  subst hfg; congr; ext; simp [hφψ]
-/
lemma map_congr {f g : G ->* H} {φ : res f A ⟶ B} {ψ : res g A ⟶ B} (hfg : f = g)
    (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) (n : Nat) :
    map f φ n = map g ψ n := by
  subst hfg; congr; ext; simp [hφψ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
theorem `π_map` / 定理 `π_map`

English:
theorem π_map
  given: (n : Nat)
  proof: by
  simp [map, cocyclesMap]

@[simp]

中文:
定理 π_map
  条件: (n : 自然数)
  证明: by
  simp [map, cocyclesMap]

@[simp]

Depends on / 依赖: cocyclesMap
-/
theorem π_map (n : Nat) :
    π A n ≫ map f φ n = cocyclesMap f φ n ≫ π B n := by
  simp [map, cocyclesMap]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (MonoidHom.id G) (𝟙 B) n = 𝟙 _
  proof: HomologicalComplex.homologyMap_id _ _

中文:
引理 map_id
  结论: map (幺半群态射.id G) (𝟙 B) n = 𝟙 _
  证明: HomologicalComplex.homologyMap_id _ _

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap_id, homologyMap_id
-/
lemma map_id : map (MonoidHom.id G) (𝟙 B) n = 𝟙 _ := HomologicalComplex.homologyMap_id _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: {G H K : Type u} [Group G] [Group H]
  proof: by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

中文:
引理 map_comp
  结论: {G H K : 类型u} [群 G] [群 H]
  证明: by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap_comp, cochainsMap_comp, homologyMap_comp
-/
lemma map_comp {G H K : Type u} [Group G] [Group H]
    [Group K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) (n : Nat) :
    map (f.comp g) ((resFunctor g).map φ ≫ ψ) n = map f φ n ≫ map g ψ n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `map_id_comp` / 定理 `map_id_comp`

English:
theorem map_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat)
  proof: by
  rw [map]; rw [cochainsMap_id_comp]; rw [HomologicalComplex.homologyMap_comp]

中文:
定理 map_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : 自然数)
  证明: by
  rw [map]; rw [cochainsMap_id_comp]; rw [HomologicalComplex.homologyMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap_comp, cochainsMap_id_comp, homologyMap_comp
-/
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map]; rw [cochainsMap_id_comp]; rw [HomologicalComplex.homologyMap_comp]

/-- The isomorphism between cohomology groups induced by a group isomorphism `e : G ≃* H` and a
isomorphism between representations (restricted by `e`). -/
@[simps]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V)
  body: groupCohomology.map e.symm (ofHom ⟨e', fun h => by simp [he]⟩) n
  inv := groupCohomology.map e (ofHom ⟨e'.symm, fun g => by
    rw [e'.toLinearMap_symm_comp_eq]; rw [← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupCohomology.map_comp]; rw [← groupCo

中文:
定义 mapIso
  签名: (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V)
  定义体: groupCohomology.map e.symm (ofHom ⟨e', fun h => by simp [he]⟩) n
  inv := groupCohomology.map e (ofHom ⟨e'.symm, fun g => by
    rw [e'.toLinearMap_symm_comp_eq]; rw [← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupCohomology.map_comp]; rw [← groupCo

Depends on / 依赖: e.symm, groupCohomology, groupCohomology.map
-/
noncomputable def mapIso (e : G ≃* H) (e' : B.V ≃ₗ[k] A.V)
    (he : forall g, e' ∘ₗ B.ρ g = A.ρ (e g) ∘ₗ e') (n : Nat) :
    groupCohomology B n ≅ groupCohomology A n where
  hom := groupCohomology.map e.symm (ofHom ⟨e', fun h => by simp [he]⟩) n
  inv := groupCohomology.map e (ofHom ⟨e'.symm, fun g => by
    rw [e'.toLinearMap_symm_comp_eq]; rw [← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupCohomology.map_comp]; rw [← groupCohomology.map_id]
    exact map_congr (by simp) (by simp [res_id]) n
  inv_hom_id := by
    rw [← groupCohomology.map_comp]; rw [← groupCohomology.map_id]
    exact groupCohomology.map_congr (by simp) e'.comp_symm n

/--
Definition of `cochainsMap₁` / `cochainsMap₁` 的定义

English:
abbreviation cochainsMap₁
  signature: :
  body: ModuleCat.ofHom φ.hom.toLinearMap.compLeft G ∘ₗ LinearMap.funLeft k A f

中文:
缩写 cochainsMap₁
  签名: :
  定义体: ModuleCat.ofHom φ.hom.toLinearMap.compLeft G ∘ₗ LinearMap.funLeft k A f

Depends on / 依赖: LinearMap, LinearMap.funLeft, ModuleCat, ModuleCat.ofHom, MonoidWithZeroHom, MonoidWithZeroHom.ofClass, Set.mem_range_self, Submonoid, Submonoid.nontrivial_iff_exists_ne_one, Units.ext_iff, Units.mk0, compLeft, exists_val_nontrivial, ext_iff, funLeft, hom.toLinearMap.compLeft, hv.exists_val_nontrivial, mem_range_self, mem_valueMonoid, nontrivial_iff_exists_ne_one
-/
noncomputable abbrev cochainsMap₁ :
    ModuleCat.of k (H -> A) ⟶ ModuleCat.of k (G -> B) :=
ModuleCat.ofHom φ.hom.toLinearMap.compLeft G ∘ₗ LinearMap.funLeft k A f

/--
Definition of `cochainsMap₂` / `cochainsMap₂` 的定义

English:
abbreviation cochainsMap₂
  signature: :
  body: ModuleCat.ofHom φ.hom.toLinearMap.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

中文:
缩写 cochainsMap₂
  签名: :
  定义体: ModuleCat.ofHom φ.hom.toLinearMap.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

Depends on / 依赖: LinearMap, LinearMap.funLeft, ModuleCat, ModuleCat.ofHom, MonoidWithZeroHom, MonoidWithZeroHom.ofClass, Prod.map, Set.mem_range_self, Subgroup, Subgroup.nontrivial_iff_exists_ne_one, Units.ext_iff, Units.mk0, compLeft, exists_val_nontrivial, ext_iff, funLeft, hom.toLinearMap.compLeft, hv.exists_val_nontrivial, mem_range_self, mem_valueGroup
-/
noncomputable abbrev cochainsMap₂ :
    ModuleCat.of k (H × H -> A) ⟶ ModuleCat.of k (G × G -> B) :=
ModuleCat.ofHom φ.hom.toLinearMap.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

/--
Definition of `cochainsMap₃` / `cochainsMap₃` 的定义

English:
abbreviation cochainsMap₃
  signature: :
  body: ModuleCat.ofHom
    φ.hom.toLinearMap.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
缩写 cochainsMap₃
  签名: :
  定义体: ModuleCat.ofHom
    φ.hom.toLinearMap.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: LinearMap, LinearMap.funLeft, ModuleCat, ModuleCat.ofHom, Prod.map, compLeft, funLeft, hom.toLinearMap.compLeft, toLinearMap
-/
noncomputable abbrev cochainsMap₃ :
    ModuleCat.of k (H × H × H -> A) ⟶ ModuleCat.of k (G × G × G -> B) :=
ModuleCat.ofHom
    φ.hom.toLinearMap.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cochainsMap_f_0_comp_cochainsIso₀` / 引理 `cochainsMap_f_0_comp_cochainsIso₀`

English:
lemma cochainsMap_f_0_comp_cochainsIso₀
  proof: by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 cochainsMap_f_0_comp_cochainsIso₀
  证明: by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: Unique, Unique.eq_default, cochainsMap_f, eq_default
-/
lemma cochainsMap_f_0_comp_cochainsIso₀ :
    (cochainsMap f φ).f 0 ≫ (cochainsIso₀ B).hom = (cochainsIso₀ A).hom ≫ φ.toModuleCatHom := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cochainsMap_f_1_comp_cochainsIso₁` / 引理 `cochainsMap_f_1_comp_cochainsIso₁`

English:
lemma cochainsMap_f_1_comp_cochainsIso₁
  proof: rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 cochainsMap_f_1_comp_cochainsIso₁
  证明: rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
-/
lemma cochainsMap_f_1_comp_cochainsIso₁ :
    (cochainsMap f φ).f 1 ≫ (cochainsIso₁ B).hom = (cochainsIso₁ A).hom ≫ cochainsMap₁ f φ := rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cochainsMap_f_2_comp_cochainsIso₂` / 引理 `cochainsMap_f_2_comp_cochainsIso₂`

English:
lemma cochainsMap_f_2_comp_cochainsIso₂
  proof: by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 cochainsMap_f_2_comp_cochainsIso₂
  证明: by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: fin_cases, rcongr
-/
lemma cochainsMap_f_2_comp_cochainsIso₂ :
    (cochainsMap f φ).f 2 ≫ (cochainsIso₂ B).hom = (cochainsIso₂ A).hom ≫ cochainsMap₂ f φ := by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cochainsMap_f_3_comp_cochainsIso₃` / 引理 `cochainsMap_f_3_comp_cochainsIso₃`

English:
lemma cochainsMap_f_3_comp_cochainsIso₃
  proof: by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

中文:
引理 cochainsMap_f_3_comp_cochainsIso₃
  证明: by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

Depends on / 依赖: fin_cases, rcongr
-/
lemma cochainsMap_f_3_comp_cochainsIso₃ :
    (cochainsMap f φ).f 3 ≫ (cochainsIso₃ B).hom = (cochainsIso₃ A).hom ≫ cochainsMap₃ f φ := by
  ext x g
  change φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

end

open ShortComplex

section H0

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `map_H0Iso_hom_f` / 定理 `map_H0Iso_hom_f`

English:
theorem map_H0Iso_hom_f
  proof: by
  simp [← cancel_epi (π _ _)]

中文:
定理 map_H0Iso_hom_f
  证明: by
  simp [← cancel_epi (π _ _)]

Depends on / 依赖: cancel_epi
-/
theorem map_H0Iso_hom_f :
    map f φ 0 ≫ (H0Iso B).hom ≫ (shortComplexH0 B).f =
      (H0Iso A).hom ≫ (shortComplexH0 A).f ≫ φ.toModuleCatHom := by
  simp [← cancel_epi (π _ _)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `map_id_comp_H0Iso_hom` / 定理 `map_id_comp_H0Iso_hom`

English:
theorem map_id_comp_H0Iso_hom
  given: {A B : Rep k G} (f : A ⟶ B)
  proof: by
  simp only [← cancel_mono (shortComplexH0 B).f, Category.assoc, map_H0Iso_hom_f]
  rfl

中文:
定理 map_id_comp_H0Iso_hom
  条件: {A B : Rep k G} (f : A ⟶ B)
  证明: by
  simp only [← cancel_mono (shortComplexH0 B).f, Category.assoc, map_H0Iso_hom_f]
  rfl

Depends on / 依赖: Category, Category.assoc, cancel_mono, map_H0Iso_hom_f, shortComplexH0
-/
theorem map_id_comp_H0Iso_hom {A B : Rep k G} (f : A ⟶ B) :
    map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom = (H0Iso A).hom ≫ (invariantsFunctor k G).map f := by
  simp only [← cancel_mono (shortComplexH0 B).f, Category.assoc, map_H0Iso_hom_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `mono_map_0_of_mono` / 实例 `mono_map_0_of_mono`

English:
instance mono_map_0_of_mono
  signature: {A B : Rep k G} (f : A ⟶ B) [Mono f]
  body: by
    simp only [← cancel_mono (H0Iso B).hom, Category.assoc, map_id_comp_H0Iso_hom] at hgh
    simp_all [cancel_mono]

中文:
实例 mono_map_0_of_mono
  签名: {A B : Rep k G} (f : A ⟶ B) [单态射 f]
  定义体: by
    simp only [← cancel_mono (H0Iso B).hom, Category.assoc, map_id_comp_H0Iso_hom] at hgh
    simp_all [cancel_mono]

Depends on / 依赖: Category, Category.assoc, cancel_mono, map_id_comp_H0Iso_hom
-/
instance mono_map_0_of_mono {A B : Rep k G} (f : A ⟶ B) [Mono f] :
    Mono (map (MonoidHom.id G) f 0) where
  right_cancellation g h hgh := by
    simp only [← cancel_mono (H0Iso B).hom, Category.assoc, map_id_comp_H0Iso_hom] at hgh
    simp_all [cancel_mono]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
theorem `cocyclesMap_cocyclesIso₀_hom_f` / 定理 `cocyclesMap_cocyclesIso₀_hom_f`

English:
theorem cocyclesMap_cocyclesIso₀_hom_f
  proof: by
  simp

中文:
定理 cocyclesMap_cocyclesIso₀_hom_f
  证明: by
  simp
-/
theorem cocyclesMap_cocyclesIso₀_hom_f :
    cocyclesMap f φ 0 ≫ (cocyclesIso₀ B).hom ≫ (shortComplexH0 B).f =
      (cocyclesIso₀ A).hom ≫ (shortComplexH0 A).f ≫ φ.toModuleCatHom := by
  simp

end H0
section H1

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex `A --d₀₁--> Fun(H, A) --d₁₂--> Fun(H × H, A)`
to `B --d₀₁--> Fun(G, B) --d₁₂--> Fun(G × G, B)`. -/
@[simps]
/--
Definition of `mapShortComplexH1` / `mapShortComplexH1` 的定义

English:
definition mapShortComplexH1
  signature: :
  body: φ.toModuleCatHom
  τ₂ := cochainsMap₁ f φ
  τ₃ := cochainsMap₂ f φ
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH1, d₀₁, cochainsMap₁] using (hom_comm_apply φ g x).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH1, d₁₂, cochainsMap₁, cochainsMap₂] using (hom_comm_a

中文:
定义 mapShortComplexH1
  签名: :
  定义体: φ.toModuleCatHom
  τ₂ := cochainsMap₁ f φ
  τ₃ := cochainsMap₂ f φ
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH1, d₀₁, cochainsMap₁] using (hom_comm_apply φ g x).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH1, d₁₂, cochainsMap₁, cochainsMap₂] using (hom_comm_a

Depends on / 依赖: toModuleCatHom
-/
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := φ.toModuleCatHom
  τ₂ := cochainsMap₁ f φ
  τ₃ := cochainsMap₂ f φ
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH1, d₀₁, cochainsMap₁] using (hom_comm_apply φ g x).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH1, d₁₂, cochainsMap₁, cochainsMap₂] using (hom_comm_apply φ _ _).symm

@[simp]
/--
theorem `mapShortComplexH1_zero` / 定理 `mapShortComplexH1_zero`

English:
theorem mapShortComplexH1_zero
  proof: by
  rfl

@[simp]

中文:
定理 mapShortComplexH1_zero
  证明: by
  rfl

@[simp]
-/
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  rfl

@[simp]
/--
theorem `mapShortComplexH1_id` / 定理 `mapShortComplexH1_id`

English:
theorem mapShortComplexH1_id
  proof: by
  rfl

@[reassoc]

中文:
定理 mapShortComplexH1_id
  证明: by
  rfl

@[reassoc]
-/
theorem mapShortComplexH1_id :
    mapShortComplexH1 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[reassoc]
/--
theorem `mapShortComplexH1_comp` / 定理 `mapShortComplexH1_comp`

English:
theorem mapShortComplexH1_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: rfl

@[reassoc]

中文:
定理 mapShortComplexH1_comp
  结论: {G H K : 类型u} [群 G] [群 H] [群 K]
  证明: rfl

@[reassoc]
-/
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) :
    mapShortComplexH1 (f.comp g) ((resFunctor g).map φ ≫ ψ) =
      mapShortComplexH1 f φ ≫ mapShortComplexH1 g ψ := rfl

@[reassoc]
/--
theorem `mapShortComplexH1_id_comp` / 定理 `mapShortComplexH1_id_comp`

English:
theorem mapShortComplexH1_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: rfl

中文:
定理 mapShortComplexH1_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: rfl
-/
theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ := rfl

/--
Definition of `mapCocycles₁` / `mapCocycles₁` 的定义

English:
abbreviation mapCocycles₁
  signature: :
  body: ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

中文:
缩写 mapCocycles₁
  签名: :
  定义体: ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap, cyclesMap, mapShortComplexH1, moduleCatLeftHomologyData, shortComplexH1
-/
noncomputable abbrev mapCocycles₁ :
    ModuleCat.of k (cocycles₁ A) ⟶ ModuleCat.of k (cocycles₁ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
lemma `mapCocycles₁_comp_i` / 引理 `mapCocycles₁_comp_i`

English:
lemma mapCocycles₁_comp_i
  proof: by
  simp

@[simp]

中文:
引理 mapCocycles₁_comp_i
  证明: by
  simp

@[simp]
-/
lemma mapCocycles₁_comp_i :
    mapCocycles₁ f φ ≫ (shortComplexH1 B).moduleCatLeftHomologyData.i =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ cochainsMap₁ f φ := by
  simp

@[simp]
/--
lemma `coe_mapCocycles₁` / 引理 `coe_mapCocycles₁`

English:
lemma coe_mapCocycles₁
  given: (x)
  proof: rfl

中文:
引理 coe_mapCocycles₁
  条件: (x)
  证明: rfl
-/
lemma coe_mapCocycles₁ (x) :
    ⇑(mapCocycles₁ f φ x) = cochainsMap₁ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cocyclesMap_comp_isoCocycles₁_hom` / 引理 `cocyclesMap_comp_isoCocycles₁_hom`

English:
lemma cocyclesMap_comp_isoCocycles₁_hom
  proof: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i]

中文:
引理 cocyclesMap_comp_isoCocycles₁_hom
  证明: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i]

Depends on / 依赖: cancel_mono, moduleCatLeftHomologyData, shortComplexH1
-/
lemma cocyclesMap_comp_isoCocycles₁_hom :
    cocyclesMap f φ 1 ≫ (isoCocycles₁ B).hom = (isoCocycles₁ A).hom ≫ mapCocycles₁.{u, u} f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mapCocycles₁_one` / 定理 `mapCocycles₁_one`

English:
theorem mapCocycles₁_one
  given: (φ : res 1 A ⟶ B)
  proof: by
  rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i]; rw [cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ => funext fun y => ?_)
  simp [mapShortComplexH1, shortComplexH1, Pi.zero_apply y]

中文:
定理 mapCocycles₁_one
  条件: (φ : res 1 A ⟶ B)
  证明: by
  rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i]; rw [cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ => funext fun y => ?_)
  simp [mapShortComplexH1, shortComplexH1, Pi.zero_apply y]

Depends on / 依赖: LinearMap, LinearMap.ext, ModuleCat, ModuleCat.hom_ext, Pi.zero_apply, cancel_mono, cyclesMap, hom_ext, mapShortComplexH1, moduleCatLeftHomologyData, shortComplexH1, zero_apply
-/
theorem mapCocycles₁_one (φ : res 1 A ⟶ B) :
    mapCocycles₁ 1 φ = 0 := by
  rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i]; rw [cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ => funext fun y => ?_)
  simp [mapShortComplexH1, shortComplexH1, Pi.zero_apply y]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `H1π_comp_map` / 引理 `H1π_comp_map`

English:
lemma H1π_comp_map
  proof: by
  simp [H1π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₁_hom_assoc]

@[simp]

中文:
引理 H1π_comp_map
  证明: by
  simp [H1π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₁_hom_assoc]

@[simp]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
lemma H1π_comp_map :
    H1π A ≫ map f φ 1 = mapCocycles₁ f φ ≫ H1π B := by
  simp [H1π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₁_hom_assoc]

@[simp]
/--
theorem `map₁_one` / 定理 `map₁_one`

English:
theorem map₁_one
  given: (φ : res 1 A ⟶ B)
  proof: by
  simp [← cancel_epi (H1π _)]

中文:
定理 map₁_one
  条件: (φ : res 1 A ⟶ B)
  证明: by
  simp [← cancel_epi (H1π _)]

Depends on / 依赖: cancel_epi
-/
theorem map₁_one (φ : res 1 A ⟶ B) :
    map 1 φ 1 = 0 := by
  simp [← cancel_epi (H1π _)]

section InfRes

variable (A : Rep k G) (S : Subgroup G) [S.Normal]

/-- The short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)`. -/
@[simps X₁ X₂ X₃ f g]
/--
Definition of `H1InfRes` / `H1InfRes` 的定义

English:
definition H1InfRes
  signature: :
  body: groupCohomology (A.quotientToInvariants S) 1
  X₂ := groupCohomology A 1
  X₃ := groupCohomology (res S.subtype A) 1
  f := map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) 1
  g := map S.subtype (𝟙 _) 1
  zero := by rw [← map_comp, Category.comp_id, congr (QuotientGroup.mk'_comp

中文:
定义 H1InfRes
  签名: :
  定义体: groupCohomology (A.quotientToInvariants S) 1
  X₂ := groupCohomology A 1
  X₃ := groupCohomology (res S.subtype A) 1
  f := map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) 1
  g := map S.subtype (𝟙 _) 1
  zero := by rw [← map_comp, Category.comp_id, congr (QuotientGroup.mk'_comp

Depends on / 依赖: A.quotientToInvariants, groupCohomology, quotientToInvariants
-/
noncomputable def H1InfRes :
    ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) 1
  X₂ := groupCohomology A 1
  X₃ := groupCohomology (res S.subtype A) 1
  f := map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) 1
  g := map S.subtype (𝟙 _) 1
  zero := by rw [← map_comp, Category.comp_id, congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ 1), map₁_one]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (H1InfRes A S).f
  body: by
  rw [ModuleCat.mono_iff_injective]; rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₁, H1InfRes_f, H1π_comp_map_apply (QuotientGroup.mk' S)]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
  refine (H1π_eq_zero

中文:
实例 :
  签名: 单态射 (H1InfRes A S).f
  定义体: by
  rw [ModuleCat.mono_iff_injective]; rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₁, H1InfRes_f, H1π_comp_map_apply (QuotientGroup.mk' S)]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
  refine (H1π_eq_zero

Depends on / 依赖: H1InfRes_f, H1_induction_on, ModuleCat, ModuleCat.mono_iff_injective, QuotientGroup, QuotientGroup.e, QuotientGroup.induction_on, QuotientGroup.mk, SetLike, SetLike.coe_eq_coe, Subtype, Subtype.ext, coe_eq_coe, congr_fun, induction_on, injective_iff_map_eq_zero, mono_iff_injective, sub_eq_zero
-/
instance : Mono (H1InfRes A S).f := by
  rw [ModuleCat.mono_iff_injective]; rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₁, H1InfRes_f, H1π_comp_map_apply (QuotientGroup.mk' S)]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
  refine (H1π_eq_zero_iff _).2 ⟨⟨y, fun s => ?_⟩, funext fun g => QuotientGroup.induction_on g
fun g => Subtype.ext by simpa [-SetLike.coe_eq_coe] using! congr_fun hy g⟩
  simpa [coe_mapCocycles₁ (x := x), sub_eq_zero, (QuotientGroup.eq_one_iff s.1).2 s.2] using!
    congr_fun hy s.1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `H1InfRes_exact` / 引理 `H1InfRes_exact`

English:
lemma H1InfRes_exact
  statement: (H1InfRes A S).Exact
  proof: by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₃, H1InfRes_g, H1InfRes_X₁, LinearMap.mem_ker,
    H1π_comp_map_apply S.subtype, H1InfRes_f]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨(y : A), hy⟩
  have

中文:
引理 H1InfRes_exact
  结论: (H1InfRes A S).正合
  证明: by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₃, H1InfRes_g, H1InfRes_X₁, LinearMap.mem_ker,
    H1π_comp_map_apply S.subtype, H1InfRes_f]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨(y : A), hy⟩
  have

Depends on / 依赖: H1InfRes_f, H1InfRes_g, H1_induction_on, LinearMap, LinearMap.mem_ker, Quotient, Quotient.liftOn, S.subtype, funext_iff, hy.symm, liftOn, mem_ker, moduleCat_exact_iff_ker_sub_range, subtype
-/
lemma H1InfRes_exact : (H1InfRes A S).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₃, H1InfRes_g, H1InfRes_X₁, LinearMap.mem_ker,
    H1π_comp_map_apply S.subtype, H1InfRes_f]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨(y : A), hy⟩
  have h1 := (mem_cocycles₁_iff x).1 x.2
  have h2 : forall s in S, x s = A.ρ s y - y :=
    fun s hs => funext_iff.1 hy.symm ⟨s, hs⟩
  refine ⟨H1π _ ⟨fun g => Quotient.liftOn' g (fun g => ⟨x.1 g - A.ρ g y + y, ?_⟩) ?_, ?_⟩, ?_⟩
  · intro s
    calc
      _ = x (s * g) - x s - A.ρ s (A.ρ g y) + (x s + y) := by
        simp [add_eq_of_eq_sub (h2 s s.2), sub_eq_of_eq_add (h1 s g)]
      _ = x (g * (g⁻¹ * s * g)) - A.ρ g (A.ρ (g⁻¹ * s * g) y - y) - A.ρ g y + y := by
        simp only [mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply, map_sub,
          Representation.self_inv_apply]
        abel
      _ = x g - A.ρ g y + y := by
        simp [eq_sub_of_add_eq' (h1 g (g⁻¹ * s * g)).symm,
          h2 (g⁻¹ * s * g) (Subgroup.Normal.conj_mem' ‹_› _ s.2 _)]
  · intro g h hgh
    have := congr(A.ρ g $(h2 (g⁻¹ * h) <| QuotientGroup.leftRel_apply.1 hgh))
    simp_all [← sub_eq_add_neg, sub_eq_sub_iff_sub_eq_sub]
  · rw [mem_cocycles₁_iff]
    intro g h
    induction g using QuotientGroup.induction_on with | @H g =>
    induction h using QuotientGroup.induction_on with | @H h =>
    apply Subtype.ext
    simp [← QuotientGroup.mk_mul, h1 g h, sub_add_eq_add_sub, add_assoc]
  · symm
    simp only [H1π_comp_map_apply, H1π_eq_iff (A := A)]
    use y
    ext g
    simp [coe_mapCocycles₁ (QuotientGroup.mk' S),
      cocycles₁.coe_mk (A := A.quotientToInvariants S), ← sub_sub]

end InfRes
end H1
section H2

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex
`Fun(H, A) --d₁₂--> Fun(H × H, A) --d₂₃--> Fun(H × H × H, A)` to
`Fun(G, B) --d₁₂--> Fun(G × G, B) --d₂₃--> Fun(G × G × G, B)`. -/
@[simps]
/--
Definition of `mapShortComplexH2` / `mapShortComplexH2` 的定义

English:
definition mapShortComplexH2
  signature: :
  body: cochainsMap₁ f φ
  τ₂ := cochainsMap₂ f φ
  τ₃ := cochainsMap₃ f φ
  comm₁₂ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]
  comm₂₃ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]

@[simp]

中文:
定义 mapShortComplexH2
  签名: :
  定义体: cochainsMap₁ f φ
  τ₂ := cochainsMap₂ f φ
  τ₃ := cochainsMap₃ f φ
  comm₁₂ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]
  comm₂₃ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]

@[simp]
-/
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := cochainsMap₁ f φ
  τ₂ := cochainsMap₂ f φ
  τ₃ := cochainsMap₃ f φ
  comm₁₂ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]
  comm₂₃ := by
    ext x
    funext g
    simp [shortComplexH2, ← hom_comm_apply φ]

@[simp]
/--
theorem `mapShortComplexH2_zero` / 定理 `mapShortComplexH2_zero`

English:
theorem mapShortComplexH2_zero
  proof: rfl

@[simp]

中文:
定理 mapShortComplexH2_zero
  证明: rfl

@[simp]
-/
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := rfl

@[simp]
/--
theorem `mapShortComplexH2_id` / 定理 `mapShortComplexH2_id`

English:
theorem mapShortComplexH2_id
  proof: by
  rfl

@[reassoc]

中文:
定理 mapShortComplexH2_id
  证明: by
  rfl

@[reassoc]
-/
theorem mapShortComplexH2_id :
    mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[reassoc]
/--
theorem `mapShortComplexH2_comp` / 定理 `mapShortComplexH2_comp`

English:
theorem mapShortComplexH2_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: rfl

@[reassoc]

中文:
定理 mapShortComplexH2_comp
  结论: {G H K : 类型u} [群 G] [群 H] [群 K]
  证明: rfl

@[reassoc]
-/
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H ->* K) (g : G ->* H)
    (φ : res f A ⟶ B) (ψ : res g B ⟶ C) :
    mapShortComplexH2 (f.comp g) ((resFunctor g).map φ ≫ ψ) =
      mapShortComplexH2 f φ ≫ mapShortComplexH2 g ψ := rfl

@[reassoc]
/--
theorem `mapShortComplexH2_id_comp` / 定理 `mapShortComplexH2_id_comp`

English:
theorem mapShortComplexH2_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: rfl

中文:
定理 mapShortComplexH2_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: rfl
-/
theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ := rfl

/--
Definition of `mapCocycles₂` / `mapCocycles₂` 的定义

English:
abbreviation mapCocycles₂
  signature: :
  body: ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

中文:
缩写 mapCocycles₂
  签名: :
  定义体: ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap, cyclesMap, mapShortComplexH2, moduleCatLeftHomologyData, shortComplexH2
-/
noncomputable abbrev mapCocycles₂ :
    ModuleCat.of k (cocycles₂ A) ⟶ ModuleCat.of k (cocycles₂ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
lemma `mapCocycles₂_comp_i` / 引理 `mapCocycles₂_comp_i`

English:
lemma mapCocycles₂_comp_i
  proof: by
  simp

@[simp]

中文:
引理 mapCocycles₂_comp_i
  证明: by
  simp

@[simp]
-/
lemma mapCocycles₂_comp_i :
    mapCocycles₂ f φ ≫ (shortComplexH2 B).moduleCatLeftHomologyData.i =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ cochainsMap₂ f φ := by
  simp

@[simp]
/--
lemma `coe_mapCocycles₂` / 引理 `coe_mapCocycles₂`

English:
lemma coe_mapCocycles₂
  given: (x)
  proof: rfl

中文:
引理 coe_mapCocycles₂
  条件: (x)
  证明: rfl
-/
lemma coe_mapCocycles₂ (x) :
    ⇑(mapCocycles₂ f φ x) = cochainsMap₂ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cocyclesMap_comp_isoCocycles₂_hom` / 引理 `cocyclesMap_comp_isoCocycles₂_hom`

English:
lemma cocyclesMap_comp_isoCocycles₂_hom
  proof: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    cochainsMap_f_2_comp_cochainsIso₂ f]

中文:
引理 cocyclesMap_comp_isoCocycles₂_hom
  证明: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    cochainsMap_f_2_comp_cochainsIso₂ f]

Depends on / 依赖: cancel_mono, mapShortComplexH2, moduleCatLeftHomologyData, shortComplexH2
-/
lemma cocyclesMap_comp_isoCocycles₂_hom :
    cocyclesMap f φ 2 ≫ (isoCocycles₂ B).hom = (isoCocycles₂ A).hom ≫ mapCocycles₂ f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    cochainsMap_f_2_comp_cochainsIso₂ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `H2π_comp_map` / 引理 `H2π_comp_map`

English:
lemma H2π_comp_map
  proof: by
  simp [H2π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₂_hom_assoc]

中文:
引理 H2π_comp_map
  证明: by
  simp [H2π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₂_hom_assoc]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
lemma H2π_comp_map :
    H2π A ≫ map f φ 2 = mapCocycles₂ f φ ≫ H2π B := by
  simp [H2π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoCocycles₂_hom_assoc]

end H2

variable (k G)

/-- The functor sending a representation to its complex of inhomogeneous cochains. -/
@[simps]
/--
Definition of `cochainsFunctor` / `cochainsFunctor` 的定义

English:
definition cochainsFunctor
  signature: : Rep k G ⥤ CochainComplex (ModuleCat k) Nat where
  body: inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

中文:
定义 cochainsFunctor
  签名: : Rep k G ⥤ 上链复形 (模范畴 k) 自然数 where
  定义体: inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

Depends on / 依赖: inhomogeneousCochains
-/
noncomputable def cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) Nat where
  obj A := inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cochainsFunctor k G).PreservesZeroMorphisms

中文:
实例 :
  签名: (cochainsFunctor k G).保持ZeroMorphisms
-/
instance : (cochainsFunctor k G).PreservesZeroMorphisms where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (cochainsFunctor k G).Additive

中文:
实例 :
  签名: (cochainsFunctor k G).加性
-/
instance : (cochainsFunctor k G).Additive where

set_option backward.isDefEq.respectTransparency false in
/-- The functor sending a `G`-representation `A` to `Hⁿ(G, A)`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: (n : Nat)
  body: groupCohomology A n
  map φ := map (MonoidHom.id _) φ n
  map_id _ := HomologicalComplex.homologyMap_id _ _
  map_comp _ _ := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

中文:
定义 functor
  签名: (n : 自然数)
  定义体: groupCohomology A n
  map φ := map (MonoidHom.id _) φ n
  map_id _ := HomologicalComplex.homologyMap_id _ _
  map_comp _ _ := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

Depends on / 依赖: groupCohomology
-/
noncomputable def functor (n : Nat) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map φ := map (MonoidHom.id _) φ n
  map_id _ := HomologicalComplex.homologyMap_id _ _
  map_comp _ _ := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance (n : Nat) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

variable {G}

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H`, this is a natural transformation between the functors
sending `A : Rep k H` to `Hⁿ(H, A)` and to `Hⁿ(G, Res(f)(A))`. -/
@[simps]
/--
Definition of `resNatTrans` / `resNatTrans` 的定义

English:
definition resNatTrans
  signature: (n : Nat)
  body: map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [functor_map, Functor.comp_map,
      ← cancel_epi (groupCohomology.π _ n), HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← cochainsMap_comp, res_ob

中文:
定义 res自然数Trans
  签名: (n : 自然数)
  定义体: map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [functor_map, Functor.comp_map,
      ← cancel_epi (groupCohomology.π _ n), HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← cochainsMap_comp, res_ob
-/
noncomputable def resNatTrans (n : Nat) :
    functor k H n ⟶ resFunctor f ⋙ functor k G n where
  app X := map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [functor_map, Functor.comp_map,
      ← cancel_epi (groupCohomology.π _ n), HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← cochainsMap_comp, res_obj_ρ, Category.comp_id]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a normal subgroup `S ≤ G`, this is a natural transformation between the functors
sending `A : Rep k G` to `Hⁿ(G ⧸ S, A^S)` and to `Hⁿ(G, A)`. -/
@[simps]
/--
Definition of `infNatTrans` / `infNatTrans` 的定义

English:
definition infNatTrans
  signature: (S : Subgroup G) [S.Normal] (n : Nat)
  body: map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupCohomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalCompl

中文:
定义 inf自然数Trans
  签名: (S : 子群 G) [S.正规] (n : 自然数)
  定义体: map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupCohomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalCompl

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, quotientToInvariants_lift
-/
noncomputable def infNatTrans (S : Subgroup G) [S.Normal] (n : Nat) :
    quotientToInvariantsFunctor k S ⋙ functor k (G ⧸ S) n ⟶ functor k G n where
  app A := map (QuotientGroup.mk' S) (ofHom <| A.ρ.quotientToInvariants_lift S) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupCohomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.cyclesMap_comp_assoc, ← cochainsMap_comp]
    congr 1

end groupCohomology
