/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Functoriality of group homology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `G`-representation
`A`, a `k`-linear `H`-representation `B`, and a representation morphism `A ⟶ Res(f)(B)`, we get
a chain map `inhomogeneousChains A ⟶ inhomogeneousChains B` and hence maps on homology
`Hₙ(G, A) ⟶ Hₙ(H, B)`.

We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupHomology.chainsMap f φ` is the map `inhomogeneousChains A ⟶ inhomogeneousChains B`
  induced by a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.
* `groupHomology.map f φ n` is the map `Hₙ(G, A) ⟶ Hₙ(H, B)` induced by a group homomorphism
  `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`.
* `groupHomology.coresNatTrans f n`: given a group homomorphism `f : G →* H`, this is a natural
  transformation of `n`th group homology functors which sends `A : Rep k H` to the "corestriction"
  map `Hₙ(G, Res(f)(A)) ⟶ Hₙ(H, A)` induced by `f` and the identity map on `Res(f)(A)`.
* `groupHomology.coinfNatTrans f n`: given a normal subgroup `S ≤ G`, this is a natural
  transformation of `n`th group homology functors which sends `A : Rep k G` to the "coinflation"
  map `Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`.
* `groupHomology.H1CoresCoinf A S` is the (exact) short complex
  `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)` for a normal subgroup `S ≤ G` and a `G`-representation
  `A`, defined using the corestriction and coinflation map in degree 1.

-/

@[expose] public section

universe v u

namespace groupHomology

open CategoryTheory Rep Finsupp Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k G} {B : Rep k H} (f : G ->* H) (φ : A ⟶ res f B) (n : Nat)

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  statement: {f₁ f₂ : G ->* H} (h : f₁ = f₂) {φ : A ⟶ res f₁ B} {T : Type*}
  proof: by
  subst h
  rfl

中文:
定理 congr
  结论: {f₁ f₂ : G ->* H} (h : f₁ = f₂) {φ : A ⟶ res f₁ B} {T : 类型}
  证明: by
  subst h
  rfl
-/
theorem congr {f₁ f₂ : G ->* H} (h : f₁ = f₂) {φ : A ⟶ res f₁ B} {T : Type*}
    (F : (f : G ->* H) -> (φ : A ⟶ res f B) -> T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the chain map sending `∑ aᵢ·gᵢ : Gⁿ →₀ A` to `∑ φ(aᵢ)·(f ∘ gᵢ) : Hⁿ →₀ B`. -/
@[simps! -isSimp f f_hom]
/--
Definition of `chainsMap` / `chainsMap` 的定义

English:
definition chainsMap
  signature: :
  body: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simp [Fin.comp_contractNth, map_add, inhomogeneousChains.d, Rep.hom_comm_apply φ]
    rfl

中文:
定义 chainsMap
  签名: :
  定义体: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simp [Fin.comp_contractNth, map_add, inhomogeneousChains.d, Rep.hom_comm_apply φ]
    rfl

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, hom.toLinearMap, linearMap, lmapDomain, mapRange, mapRange.linearMap, toLinearMap
-/
noncomputable def chainsMap :
    inhomogeneousChains A ⟶ inhomogeneousChains B where
f i := ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (f ∘ ·)
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simp [Fin.comp_contractNth, map_add, inhomogeneousChains.d, Rep.hom_comm_apply φ]
    rfl

/--
lemma `chainsMap_congr` / 引理 `chainsMap_congr`

English:
lemma chainsMap_congr
  statement: {f g : G ->* H} {φ : A ⟶ res f B} {ψ : A ⟶ res g B} (hfg : f = g)
  proof: by
  subst hfg; congr; ext; simp [hφψ]

@[reassoc (attr := simp)]

中文:
引理 chainsMap_congr
  结论: {f g : G ->* H} {φ : A ⟶ res f B} {ψ : A ⟶ res g B} (hfg : f = g)
  证明: by
  subst hfg; congr; ext; simp [hφψ]

@[reassoc (attr := simp)]
-/
lemma chainsMap_congr {f g : G ->* H} {φ : A ⟶ res f B} {ψ : A ⟶ res g B} (hfg : f = g)
    (hφψ : φ.hom.toLinearMap = ψ.hom.toLinearMap) :
    chainsMap f φ = chainsMap g ψ := by
  subst hfg; congr; ext; simp [hφψ]

@[reassoc (attr := simp)]
/--
lemma `lsingle_comp_chainsMap_f` / 引理 `lsingle_comp_chainsMap_f`

English:
lemma lsingle_comp_chainsMap_f
  given: (n : Nat) (x : Fin n -> G)
  proof: by
  ext
  simp [chainsMap_f]

中文:
引理 lsingle_comp_chainsMap_f
  条件: (n : 自然数) (x : Fin n -> G)
  证明: by
  ext
  simp [chainsMap_f]

Depends on / 依赖: chainsMap_f
-/
lemma lsingle_comp_chainsMap_f (n : Nat) (x : Fin n -> G) :
    ModuleCat.ofHom (lsingle x) ≫ (chainsMap f φ).f n =
      ModuleCat.ofHom (lsingle (f ∘ x) ∘ₗ φ.hom.toLinearMap) := by
  ext
  simp [chainsMap_f]

/--
lemma `chainsMap_f_single` / 引理 `chainsMap_f_single`

English:
lemma chainsMap_f_single
  given: (n : Nat) (x : Fin n -> G) (a : A)
  proof: by
  simp [chainsMap_f]

@[simp]

中文:
引理 chainsMap_f_single
  条件: (n : 自然数) (x : Fin n -> G) (a : A)
  证明: by
  simp [chainsMap_f]

@[simp]

Depends on / 依赖: chainsMap_f
-/
lemma chainsMap_f_single (n : Nat) (x : Fin n -> G) (a : A) :
    (chainsMap f φ).f n (single x a) = single (f ∘ x) (φ.hom a) := by
  simp [chainsMap_f]

@[simp]
/--
lemma `chainsMap_id` / 引理 `chainsMap_id`

English:
lemma chainsMap_id
  proof: HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext lhom_ext' fun _ =>
ModuleCat.hom_ext_iff.1 lsingle_comp_chainsMap_f (k := k) (MonoidHom.id G) ..

@[simp]

中文:
引理 chainsMap_id
  证明: HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext lhom_ext' fun _ =>
ModuleCat.hom_ext_iff.1 lsingle_comp_chainsMap_f (k := k) (MonoidHom.id G) ..

@[simp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.hom_ext, ModuleCat, ModuleCat.hom_ext, ModuleCat.hom_ext_iff, MonoidHom, MonoidHom.id, hom_ext, hom_ext_iff, lhom_ext, lsingle_comp_chainsMap_f
-/
lemma chainsMap_id :
    chainsMap (MonoidHom.id G) (𝟙 A) = 𝟙 (inhomogeneousChains A) :=
HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext lhom_ext' fun _ =>
ModuleCat.hom_ext_iff.1 lsingle_comp_chainsMap_f (k := k) (MonoidHom.id G) ..

@[simp]
/--
lemma `chainsMap_id_f_hom_eq_mapRange` / 引理 `chainsMap_id_f_hom_eq_mapRange`

English:
lemma chainsMap_id_f_hom_eq_mapRange
  given: {A B : Rep k G} (i : Nat) (φ : A ⟶ B)
  proof: by
  refine lhom_ext fun _ _ => ?_
  simp [chainsMap_f, MonoidHom.coe_id]

中文:
引理 chainsMap_id_f_hom_eq_mapRange
  条件: {A B : Rep k G} (i : 自然数) (φ : A ⟶ B)
  证明: by
  refine lhom_ext fun _ _ => ?_
  simp [chainsMap_f, MonoidHom.coe_id]

Depends on / 依赖: MonoidHom, MonoidHom.coe_id, chainsMap_f, coe_id, lhom_ext
-/
lemma chainsMap_id_f_hom_eq_mapRange {A B : Rep k G} (i : Nat) (φ : A ⟶ B) :
    ((chainsMap (MonoidHom.id G) φ).f i).hom = mapRange.linearMap φ.hom.toLinearMap := by
  refine lhom_ext fun _ _ => ?_
  simp [chainsMap_f, MonoidHom.coe_id]

/--
lemma `chainsMap_comp` / 引理 `chainsMap_comp`

English:
lemma chainsMap_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: by
  ext
  simp [chainsMap_f, Function.comp_assoc]

中文:
引理 chainsMap_comp
  结论: {G H K : 类型u} [Group G] [Group H] [Group K]
  证明: by
  ext
  simp [chainsMap_f, Function.comp_assoc]

Depends on / 依赖: Function, Function.comp_assoc, chainsMap_f, comp_assoc
-/
lemma chainsMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K}
    (f : G ->* H) (g : H ->* K) (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    chainsMap (g.comp f) (φ ≫ (resFunctor f).map ψ) = chainsMap f φ ≫ chainsMap g ψ := by
  ext
  simp [chainsMap_f, Function.comp_assoc]

/--
lemma `chainsMap_id_comp` / 引理 `chainsMap_id_comp`

English:
lemma chainsMap_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[simp]

中文:
引理 chainsMap_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[simp]

Depends on / 依赖: MonoidHom, MonoidHom.id, chainsMap_comp
-/
lemma chainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    chainsMap (MonoidHom.id G) (φ ≫ ψ) =
      chainsMap (MonoidHom.id G) φ ≫ chainsMap (MonoidHom.id G) ψ :=
  chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) _ _

@[simp]
/--
lemma `chainsMap_zero` / 引理 `chainsMap_zero`

English:
lemma chainsMap_zero
  statement: chainsMap f (0 : A ⟶ res f B) = 0
  proof: by
  ext; simp [chainsMap_f, LinearMap.zero_apply (M₂ := B)]

中文:
引理 chainsMap_zero
  结论: chainsMap f (0 : A ⟶ res f B) = 0
  证明: by
  ext; simp [chainsMap_f, LinearMap.zero_apply (M₂ := B)]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, chainsMap_f, zero_apply
-/
lemma chainsMap_zero : chainsMap f (0 : A ⟶ res f B) = 0 := by
  ext; simp [chainsMap_f, LinearMap.zero_apply (M₂ := B)]

/--
lemma `chainsMap_f_map_mono` / 引理 `chainsMap_f_map_mono`

English:
lemma chainsMap_f_map_mono
  given: (hf : Function.Injective f) [Mono φ] (i : Nat)
  proof: by
  simpa [ModuleCat.mono_iff_injective] using!
    (mapRange_injective φ.hom (map_zero _) <| (Rep.mono_iff_injective φ).1
    inferInstance).comp (mapDomain_injective hf.comp_left)

中文:
引理 chainsMap_f_map_mono
  条件: (hf : Function.Injective f) [Mono φ] (i : 自然数)
  证明: by
  simpa [ModuleCat.mono_iff_injective] using!
    (mapRange_injective φ.hom (map_zero _) <| (Rep.mono_iff_injective φ).1
    inferInstance).comp (mapDomain_injective hf.comp_left)

Depends on / 依赖: ModuleCat, ModuleCat.mono_iff_injective, Rep.mono_iff_injective, comp_left, hf.comp_left, mapDomain_injective, mapRange_injective, map_zero, mono_iff_injective
-/
lemma chainsMap_f_map_mono (hf : Function.Injective f) [Mono φ] (i : Nat) :
    Mono ((chainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using!
    (mapRange_injective φ.hom (map_zero _) <| (Rep.mono_iff_injective φ).1
    inferInstance).comp (mapDomain_injective hf.comp_left)

/--
Instance `chainsMap_id_f_map_mono` / 实例 `chainsMap_id_f_map_mono`

English:
instance chainsMap_id_f_map_mono
  signature: {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : Nat)
  body: chainsMap_f_map_mono (MonoidHom.id G) φ (fun _ _ h => h) _

中文:
实例 chainsMap_id_f_map_mono
  签名: {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : 自然数)
  定义体: chainsMap_f_map_mono (MonoidHom.id G) φ (fun _ _ h => h) _

Depends on / 依赖: MonoidHom, MonoidHom.id, chainsMap_f_map_mono
-/
instance chainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : Nat) :
    Mono ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_mono (MonoidHom.id G) φ (fun _ _ h => h) _

/--
lemma `chainsMap_f_map_epi` / 引理 `chainsMap_f_map_epi`

English:
lemma chainsMap_f_map_epi
  given: (hf : Function.Surjective f) [Epi φ] (i : Nat)
  proof: by
  simpa [ModuleCat.epi_iff_surjective] using!
    (mapRange_surjective φ.hom (map_zero _) ((Rep.epi_iff_surjective φ).1 inferInstance)).comp
    (mapDomain_surjective hf.comp_left)

中文:
引理 chainsMap_f_map_epi
  条件: (hf : Function.Surjective f) [Epi φ] (i : 自然数)
  证明: by
  simpa [ModuleCat.epi_iff_surjective] using!
    (mapRange_surjective φ.hom (map_zero _) ((Rep.epi_iff_surjective φ).1 inferInstance)).comp
    (mapDomain_surjective hf.comp_left)

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, Rep.epi_iff_surjective, comp_left, epi_iff_surjective, hf.comp_left, mapDomain_surjective, mapRange_surjective, map_zero
-/
lemma chainsMap_f_map_epi (hf : Function.Surjective f) [Epi φ] (i : Nat) :
    Epi ((chainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using!
    (mapRange_surjective φ.hom (map_zero _) ((Rep.epi_iff_surjective φ).1 inferInstance)).comp
    (mapDomain_surjective hf.comp_left)

/--
Instance `chainsMap_id_f_map_epi` / 实例 `chainsMap_id_f_map_epi`

English:
instance chainsMap_id_f_map_epi
  signature: {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : Nat)
  body: chainsMap_f_map_epi _ _ (fun x => ⟨x, rfl⟩) _

中文:
实例 chainsMap_id_f_map_epi
  签名: {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : 自然数)
  定义体: chainsMap_f_map_epi _ _ (fun x => ⟨x, rfl⟩) _

Depends on / 依赖: chainsMap_f_map_epi
-/
instance chainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : Nat) :
    Epi ((chainsMap (MonoidHom.id G) φ).f i) :=
  chainsMap_f_map_epi _ _ (fun x => ⟨x, rfl⟩) _

/--
Definition of `cyclesMap` / `cyclesMap` 的定义

English:
abbreviation cyclesMap
  signature: (n : Nat)
  body: HomologicalComplex.cyclesMap (chainsMap f φ) n

@[simp]

中文:
缩写 cyclesMap
  签名: (n : 自然数)
  定义体: HomologicalComplex.cyclesMap (chainsMap f φ) n

@[simp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap, chainsMap, cyclesMap
-/
noncomputable abbrev cyclesMap (n : Nat) :
    groupHomology.cycles A n ⟶ groupHomology.cycles B n :=
  HomologicalComplex.cyclesMap (chainsMap f φ) n

@[simp]
/--
lemma `cyclesMap_id` / 引理 `cyclesMap_id`

English:
lemma cyclesMap_id
  statement: cyclesMap (MonoidHom.id G) (𝟙 A) n = 𝟙 _
  proof: by
  simp [cyclesMap]

@[reassoc]

中文:
引理 cyclesMap_id
  结论: cyclesMap (MonoidHom.id G) (𝟙 A) n = 𝟙 _
  证明: by
  simp [cyclesMap]

@[reassoc]

Depends on / 依赖: cyclesMap
-/
lemma cyclesMap_id : cyclesMap (MonoidHom.id G) (𝟙 A) n = 𝟙 _ := by
  simp [cyclesMap]

@[reassoc]
/--
lemma `cyclesMap_comp` / 引理 `cyclesMap_comp`

English:
lemma cyclesMap_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: by
  simp [cyclesMap, ← HomologicalComplex.cyclesMap_comp, ← chainsMap_comp]

中文:
引理 cyclesMap_comp
  结论: {G H K : 类型u} [Group G] [Group H] [Group K]
  证明: by
  simp [cyclesMap, ← HomologicalComplex.cyclesMap_comp, ← chainsMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap_comp, chainsMap_comp, cyclesMap, cyclesMap_comp
-/
lemma cyclesMap_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G ->* H) (g : H ->* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) (n : Nat) :
    cyclesMap (g.comp f) (φ ≫ (resFunctor f).map ψ) n = cyclesMap f φ n ≫ cyclesMap g ψ n := by
  simp [cyclesMap, ← HomologicalComplex.cyclesMap_comp, ← chainsMap_comp]

/--
theorem `cyclesMap_id_comp` / 定理 `cyclesMap_id_comp`

English:
theorem cyclesMap_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat)
  proof: by
  simp [cyclesMap, chainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

中文:
定理 cyclesMap_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : 自然数)
  证明: by
  simp [cyclesMap, chainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.cyclesMap_comp, chainsMap_id_comp, cyclesMap, cyclesMap_comp
-/
theorem cyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat) :
    cyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cyclesMap (MonoidHom.id G) φ n ≫ cyclesMap (MonoidHom.id G) ψ n := by
  simp [cyclesMap, chainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: (n : Nat)
  body: HomologicalComplex.homologyMap (chainsMap f φ) n

中文:
缩写 map
  签名: (n : 自然数)
  定义体: HomologicalComplex.homologyMap (chainsMap f φ) n

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap, chainsMap, homologyMap
-/
noncomputable abbrev map (n : Nat) :
    groupHomology A n ⟶ groupHomology B n :=
  HomologicalComplex.homologyMap (chainsMap f φ) n

/--
lemma `map_congr` / 引理 `map_congr`

English:
lemma map_congr
  statement: {f g : G ->* H} {φ : A ⟶ res f B} {ψ : A ⟶ res g B} (hfg : f = g)
  proof: by
  subst hfg; congr; ext; simp [hφψ]

中文:
引理 map_congr
  结论: {f g : G ->* H} {φ : A ⟶ res f B} {ψ : A ⟶ res g B} (hfg : f = g)
  证明: by
  subst hfg; congr; ext; simp [hφψ]
-/
lemma map_congr {f g : G ->* H} {φ : A ⟶ res f B} {ψ : A ⟶ res g B} (hfg : f = g)
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
  simp [map, cyclesMap]

@[simp]

中文:
定理 π_map
  条件: (n : 自然数)
  证明: by
  simp [map, cyclesMap]

@[simp]

Depends on / 依赖: cyclesMap
-/
theorem π_map (n : Nat) :
    π A n ≫ map f φ n = cyclesMap f φ n ≫ π B n := by
  simp [map, cyclesMap]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map (MonoidHom.id G) (𝟙 A) n = 𝟙 _
  proof: by
  simp [map, groupHomology]

中文:
引理 map_id
  结论: map (MonoidHom.id G) (𝟙 A) n = 𝟙 _
  证明: by
  simp [map, groupHomology]

Depends on / 依赖: groupHomology
-/
lemma map_id : map (MonoidHom.id G) (𝟙 A) n = 𝟙 _ := by
  simp [map, groupHomology]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]

中文:
引理 map_comp
  结论: {G H K : 类型u} [Group G] [Group H] [Group K]
  证明: by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap_comp, chainsMap_comp, homologyMap_comp
-/
lemma map_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G ->* H) (g : H ->* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) (n : Nat) :
    map (g.comp f) (φ ≫ (resFunctor f).map ψ) n = map f φ n ≫ map g ψ n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_id_comp` / 定理 `map_id_comp`

English:
theorem map_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat)
  proof: by
  rw [map]; rw [chainsMap_id_comp]; rw [HomologicalComplex.homologyMap_comp]

中文:
定理 map_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : 自然数)
  证明: by
  rw [map]; rw [chainsMap_id_comp]; rw [HomologicalComplex.homologyMap_comp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyMap_comp, chainsMap_id_comp, homologyMap_comp
-/
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : Nat) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map]; rw [chainsMap_id_comp]; rw [HomologicalComplex.homologyMap_comp]

/-- The isomorphism between homology groups induced by a group isomorphism `e : G ≃* H` and a
isomorphism between representations (restricted by `e`). -/
@[simps]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (e : G ≃* H) (e' : A.V ≃ₗ[k] B.V)
  body: groupHomology.map (A := A) e (ofHom ⟨e', by simp [he]⟩) n
  inv := groupHomology.map (A := B) e.symm (ofHom ⟨e'.symm, fun h => by
    rw [LinearEquiv.toLinearMap_symm_comp_eq]; rw [← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupHomology.map_comp]; r

中文:
定义 mapIso
  签名: (e : G ≃* H) (e' : A.V ≃ₗ[k] B.V)
  定义体: groupHomology.map (A := A) e (ofHom ⟨e', by simp [he]⟩) n
  inv := groupHomology.map (A := B) e.symm (ofHom ⟨e'.symm, fun h => by
    rw [LinearEquiv.toLinearMap_symm_comp_eq]; rw [← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupHomology.map_comp]; r

Depends on / 依赖: groupHomology, groupHomology.map
-/
noncomputable def mapIso (e : G ≃* H) (e' : A.V ≃ₗ[k] B.V)
    (he : forall g, e' ∘ₗ A.ρ g = B.ρ (e g) ∘ₗ e') (n : Nat) :
    groupHomology A n ≅ groupHomology B n where
  hom := groupHomology.map (A := A) e (ofHom ⟨e', by simp [he]⟩) n
  inv := groupHomology.map (A := B) e.symm (ofHom ⟨e'.symm, fun h => by
    rw [LinearEquiv.toLinearMap_symm_comp_eq]; rw [← LinearMap.comp_assoc]
    simp [he, LinearMap.comp_assoc]⟩) n
  hom_inv_id := by
    rw [← groupHomology.map_comp]; rw [← groupHomology.map_id]
    exact groupHomology.map_congr e.coe_monoidHom_symm_comp_coe_monoidHom e'.symm_comp n
  inv_hom_id := by
    rw [← groupHomology.map_comp]; rw [← groupHomology.map_id]
    exact groupHomology.map_congr e.coe_monoidHom_comp_coe_monoidHom_symm e'.comp_symm n

/--
Definition of `chainsMap₁` / `chainsMap₁` 的定义

English:
abbreviation chainsMap₁
  signature: : ModuleCat.of k (G ->₀ A) ⟶ ModuleCat.of k (H ->₀ B)
  body: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k f

中文:
缩写 chainsMap₁
  签名: : ModuleCat.of k (G ->₀ A) ⟶ ModuleCat.of k (H ->₀ B)
  定义体: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k f

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, hom.toLinearMap, linearMap, lmapDomain, mapRange, mapRange.linearMap, toLinearMap
-/
noncomputable abbrev chainsMap₁ : ModuleCat.of k (G ->₀ A) ⟶ ModuleCat.of k (H ->₀ B) :=
ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k f

/--
Definition of `chainsMap₂` / `chainsMap₂` 的定义

English:
abbreviation chainsMap₂
  signature: : ModuleCat.of k (G × G ->₀ A) ⟶ ModuleCat.of k (H × H ->₀ B)
  body: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (Prod.map f f)

中文:
缩写 chainsMap₂
  签名: : ModuleCat.of k (G × G ->₀ A) ⟶ ModuleCat.of k (H × H ->₀ B)
  定义体: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (Prod.map f f)

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, Prod.map, hom.toLinearMap, linearMap, lmapDomain, mapRange, mapRange.linearMap, toLinearMap
-/
noncomputable abbrev chainsMap₂ : ModuleCat.of k (G × G ->₀ A) ⟶ ModuleCat.of k (H × H ->₀ B) :=
ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ lmapDomain A k (Prod.map f f)

/--
Definition of `chainsMap₃` / `chainsMap₃` 的定义

English:
abbreviation chainsMap₃
  signature: :
  body: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ
    lmapDomain A k (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
缩写 chainsMap₃
  签名: :
  定义体: ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ
    lmapDomain A k (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: ModuleCat, ModuleCat.ofHom, Prod.map, hom.toLinearMap, linearMap, lmapDomain, mapRange, mapRange.linearMap, toLinearMap
-/
noncomputable abbrev chainsMap₃ :
    ModuleCat.of k (G × G × G ->₀ A) ⟶ ModuleCat.of k (H × H × H ->₀ B) :=
ModuleCat.ofHom mapRange.linearMap φ.hom.toLinearMap ∘ₗ
    lmapDomain A k (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `chainsMap_f_0_comp_chainsIso₀` / 引理 `chainsMap_f_0_comp_chainsIso₀`

English:
lemma chainsMap_f_0_comp_chainsIso₀
  proof: by
  ext
  simp [chainsMap_f, Unique.eq_default (α := Fin 0 -> G), Unique.eq_default (α := Fin 0 -> H),
    chainsIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 chainsMap_f_0_comp_chainsIso₀
  证明: by
  ext
  simp [chainsMap_f, Unique.eq_default (α := Fin 0 -> G), Unique.eq_default (α := Fin 0 -> H),
    chainsIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: Unique, Unique.eq_default, chainsMap_f, eq_default
-/
lemma chainsMap_f_0_comp_chainsIso₀ :
    (chainsMap f φ).f 0 ≫ (chainsIso₀ B).hom = (chainsIso₀ A).hom ≫ φ.toModuleCatHom := by
  ext
  simp [chainsMap_f, Unique.eq_default (α := Fin 0 -> G), Unique.eq_default (α := Fin 0 -> H),
    chainsIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `chainsMap_f_1_comp_chainsIso₁` / 引理 `chainsMap_f_1_comp_chainsIso₁`

English:
lemma chainsMap_f_1_comp_chainsIso₁
  proof: by
  ext x
  simp [chainsMap_f, chainsIso₁]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 chainsMap_f_1_comp_chainsIso₁
  证明: by
  ext x
  simp [chainsMap_f, chainsIso₁]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: chainsMap_f
-/
lemma chainsMap_f_1_comp_chainsIso₁ :
    (chainsMap f φ).f 1 ≫ (chainsIso₁ B).hom = (chainsIso₁ A).hom ≫ chainsMap₁ f φ := by
  ext x
  simp [chainsMap_f, chainsIso₁]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `chainsMap_f_2_comp_chainsIso₂` / 引理 `chainsMap_f_2_comp_chainsIso₂`

English:
lemma chainsMap_f_2_comp_chainsIso₂
  proof: by
  ext
  simp [chainsMap_f, chainsIso₂]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
引理 chainsMap_f_2_comp_chainsIso₂
  证明: by
  ext
  simp [chainsMap_f, chainsIso₂]

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: chainsMap_f
-/
lemma chainsMap_f_2_comp_chainsIso₂ :
    (chainsMap f φ).f 2 ≫ (chainsIso₂ B).hom = (chainsIso₂ A).hom ≫ chainsMap₂ f φ := by
  ext
  simp [chainsMap_f, chainsIso₂]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `chainsMap_f_3_comp_chainsIso₃` / 引理 `chainsMap_f_3_comp_chainsIso₃`

English:
lemma chainsMap_f_3_comp_chainsIso₃
  proof: by
  ext
  simp [chainsMap_f, chainsIso₃, ← Fin.comp_tail]

中文:
引理 chainsMap_f_3_comp_chainsIso₃
  证明: by
  ext
  simp [chainsMap_f, chainsIso₃, ← Fin.comp_tail]

Depends on / 依赖: Fin.comp_tail, chainsMap_f, comp_tail
-/
lemma chainsMap_f_3_comp_chainsIso₃ :
    (chainsMap f φ).f 3 ≫ (chainsIso₃ B).hom = (chainsIso₃ A).hom ≫ chainsMap₃ f φ := by
  ext
  simp [chainsMap_f, chainsIso₃, ← Fin.comp_tail]

open ShortComplex

section H0

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `cyclesMap_comp_cyclesIso₀_hom` / 定理 `cyclesMap_comp_cyclesIso₀_hom`

English:
theorem cyclesMap_comp_cyclesIso₀_hom
  proof: by
  simp [cyclesIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定理 cyclesMap_comp_cyclesIso₀_hom
  证明: by
  simp [cyclesIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]
-/
theorem cyclesMap_comp_cyclesIso₀_hom :
    cyclesMap f φ 0 ≫ (cyclesIso₀ B).hom = (cyclesIso₀ A).hom ≫ φ.toModuleCatHom := by
  simp [cyclesIso₀]

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `cyclesIso₀_inv_comp_cyclesMap` / 定理 `cyclesIso₀_inv_comp_cyclesMap`

English:
theorem cyclesIso₀_inv_comp_cyclesMap
  proof: (CommSq.vert_inv ⟨cyclesMap_comp_cyclesIso₀_hom f φ⟩).w.symm

中文:
定理 cyclesIso₀_inv_comp_cyclesMap
  证明: (CommSq.vert_inv ⟨cyclesMap_comp_cyclesIso₀_hom f φ⟩).w.symm

Depends on / 依赖: CommSq, CommSq.vert_inv, vert_inv, w.symm
-/
theorem cyclesIso₀_inv_comp_cyclesMap :
    (cyclesIso₀ A).inv ≫ cyclesMap f φ 0 = φ.toModuleCatHom ≫ (cyclesIso₀ B).inv :=
  (CommSq.vert_inv ⟨cyclesMap_comp_cyclesIso₀_hom f φ⟩).w.symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `H0π_comp_map` / 定理 `H0π_comp_map`

English:
theorem H0π_comp_map
  proof: by
  simp [H0π]

中文:
定理 H0π_comp_map
  证明: by
  simp [H0π]
-/
theorem H0π_comp_map :
    H0π A ≫ map f φ 0 = φ.toModuleCatHom ≫ H0π B := by
  simp [H0π]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `map_id_comp_H0Iso_hom` / 定理 `map_id_comp_H0Iso_hom`

English:
theorem map_id_comp_H0Iso_hom
  given: {A B : Rep k G} (f : A ⟶ B)
  proof: by
  rw [← cancel_epi (H0π A)]
  ext
  simp

中文:
定理 map_id_comp_H0Iso_hom
  条件: {A B : Rep k G} (f : A ⟶ B)
  证明: by
  rw [← cancel_epi (H0π A)]
  ext
  simp

Depends on / 依赖: cancel_epi
-/
theorem map_id_comp_H0Iso_hom {A B : Rep k G} (f : A ⟶ B) :
    map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom =
      (H0Iso A).hom ≫ (coinvariantsFunctor k G).map f := by
  rw [← cancel_epi (H0π A)]
  ext
  simp

/--
Instance `epi_map_0_of_epi` / 实例 `epi_map_0_of_epi`

English:
instance epi_map_0_of_epi
  signature: {A B : Rep k G} (f : A ⟶ B) [Epi f]
  body: by
    simp only [← cancel_epi (H0π A)] at hgh
    simp_all [cancel_epi]

中文:
实例 epi_map_0_of_epi
  签名: {A B : Rep k G} (f : A ⟶ B) [Epi f]
  定义体: by
    simp only [← cancel_epi (H0π A)] at hgh
    simp_all [cancel_epi]

Depends on / 依赖: cancel_epi
-/
instance epi_map_0_of_epi {A B : Rep k G} (f : A ⟶ B) [Epi f] :
    Epi (map (MonoidHom.id G) f 0) where
  left_cancellation g h hgh := by
    simp only [← cancel_epi (H0π A)] at hgh
    simp_all [cancel_epi]

end H0

section H1

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex `(G × G →₀ A) --d₂₁--> (G →₀ A) --d₁₀--> A`
to `(H × H →₀ B) --d₂₁--> (H →₀ B) --d₁₀--> B`. -/
@[simps]
/--
Definition of `mapShortComplexH1` / `mapShortComplexH1` 的定义

English:
definition mapShortComplexH1
  signature: :
  body: chainsMap₂ f φ
  τ₂ := chainsMap₁ f φ
  τ₃ := φ.toModuleCatHom
  comm₁₂ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [d₂₁, map_add, map_sub, ← map_inv] using congr(single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [← map_inv, d

中文:
定义 mapShortComplexH1
  签名: :
  定义体: chainsMap₂ f φ
  τ₂ := chainsMap₁ f φ
  τ₃ := φ.toModuleCatHom
  comm₁₂ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [d₂₁, map_add, map_sub, ← map_inv] using congr(single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [← map_inv, d
-/
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := chainsMap₂ f φ
  τ₂ := chainsMap₁ f φ
  τ₃ := φ.toModuleCatHom
  comm₁₂ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [d₂₁, map_add, map_sub, ← map_inv] using congr(single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH1]
    ext : 3
    simpa [← map_inv, d₁₀] using (hom_comm_apply φ _ _).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mapShortComplexH1_zero` / 定理 `mapShortComplexH1_zero`

English:
theorem mapShortComplexH1_zero
  proof: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp }

@[simp]

中文:
定理 mapShortComplexH1_zero
  证明: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp }

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.hom_ext, all_goals, hom_ext, shortComplexH1
-/
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp }

@[simp]
/--
theorem `mapShortComplexH1_id` / 定理 `mapShortComplexH1_id`

English:
theorem mapShortComplexH1_id
  statement: mapShortComplexH1 (MonoidHom.id G) (𝟙 A) = 𝟙 _
  proof: by
  ext <;> simp [shortComplexH1]

中文:
定理 mapShortComplexH1_id
  结论: mapShortComplexH1 (MonoidHom.id G) (𝟙 A) = 𝟙 _
  证明: by
  ext <;> simp [shortComplexH1]

Depends on / 依赖: shortComplexH1
-/
theorem mapShortComplexH1_id : mapShortComplexH1 (MonoidHom.id G) (𝟙 A) = 𝟙 _ := by
  ext <;> simp [shortComplexH1]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mapShortComplexH1_comp` / 定理 `mapShortComplexH1_comp`

English:
theorem mapShortComplexH1_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp [Prod.map]}

中文:
定理 mapShortComplexH1_comp
  结论: {G H K : 类型u} [Group G] [Group H] [Group K]
  证明: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp [Prod.map]}

Depends on / 依赖: Prod.map, ShortComplex, ShortComplex.hom_ext, all_goals, hom_ext, shortComplexH1
-/
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G ->* H) (g : H ->* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapShortComplexH1 (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      (mapShortComplexH1 f φ) ≫ (mapShortComplexH1 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
  all_goals
  { simp only [shortComplexH1]
    ext
    simp [Prod.map]}

/--
theorem `mapShortComplexH1_id_comp` / 定理 `mapShortComplexH1_id_comp`

English:
theorem mapShortComplexH1_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: mapShortComplexH1_comp (MonoidHom.id G) (MonoidHom.id G) _ _

中文:
定理 mapShortComplexH1_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: mapShortComplexH1_comp (MonoidHom.id G) (MonoidHom.id G) _ _

Depends on / 依赖: MonoidHom, MonoidHom.id, mapShortComplexH1_comp
-/
theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ :=
  mapShortComplexH1_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/--
Definition of `mapCycles₁` / `mapCycles₁` 的定义

English:
abbreviation mapCycles₁
  signature: :
  body: ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

中文:
缩写 mapCycles₁
  签名: :
  定义体: ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

Depends on / 依赖: IsLocalRing, ShortComplex, ShortComplex.cyclesMap, cyclesMap, isLocalRing, mapShortComplexH1, moduleCatLeftHomologyData, shortComplexH1
-/
noncomputable abbrev mapCycles₁ :
    ModuleCat.of k (cycles₁ A) ⟶ ModuleCat.of k (cycles₁ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapCycles₁_hom` / 引理 `mapCycles₁_hom`

English:
lemma mapCycles₁_hom
  proof: rfl

中文:
引理 mapCycles₁_hom
  证明: rfl

Depends on / 依赖: mapShortComplexH1, shortComplexH1
-/
lemma mapCycles₁_hom :
    (mapCycles₁ f φ).hom = (chainsMap₁ f φ).hom.restrict (fun x _ => by
      have := congr($((mapShortComplexH1 f φ).comm₂₃) x); simp_all [cycles₁, shortComplexH1]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
lemma `mapCycles₁_comp` / 引理 `mapCycles₁_comp`

English:
lemma mapCycles₁_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: by
  rw [← cyclesMap'_comp]; rw [← mapShortComplexH1_comp]

@[reassoc, elementwise]

中文:
引理 mapCycles₁_comp
  结论: {G H K : 类型u} [Group G] [Group H] [Group K]
  证明: by
  rw [← cyclesMap'_comp]; rw [← mapShortComplexH1_comp]

@[reassoc, elementwise]

Depends on / 依赖: _comp, cyclesMap, mapShortComplexH1_comp
-/
lemma mapCycles₁_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G ->* H) (g : H ->* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapCycles₁ (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      mapCycles₁ f φ ≫ mapCycles₁ g ψ := by
  rw [← cyclesMap'_comp]; rw [← mapShortComplexH1_comp]

@[reassoc, elementwise]
/--
theorem `mapCycles₁_id_comp` / 定理 `mapCycles₁_id_comp`

English:
theorem mapCycles₁_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: mapCycles₁_comp (MonoidHom.id G) (MonoidHom.id G) _ _

中文:
定理 mapCycles₁_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: mapCycles₁_comp (MonoidHom.id G) (MonoidHom.id G) _ _

Depends on / 依赖: MonoidHom, MonoidHom.id
-/
theorem mapCycles₁_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapCycles₁ (MonoidHom.id G) (φ ≫ ψ) =
      mapCycles₁ (MonoidHom.id G) φ ≫ mapCycles₁ (MonoidHom.id G) ψ :=
  mapCycles₁_comp (MonoidHom.id G) (MonoidHom.id G) _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
lemma `mapCycles₁_comp_i` / 引理 `mapCycles₁_comp_i`

English:
lemma mapCycles₁_comp_i
  proof: by
  simp

@[simp]

中文:
引理 mapCycles₁_comp_i
  证明: by
  simp

@[simp]
-/
lemma mapCycles₁_comp_i :
    mapCycles₁ f φ ≫ (shortComplexH1 B).moduleCatLeftHomologyData.i =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ chainsMap₁ f φ := by
  simp

@[simp]
/--
lemma `coe_mapCycles₁` / 引理 `coe_mapCycles₁`

English:
lemma coe_mapCycles₁
  given: (x)
  proof: rfl

中文:
引理 coe_mapCycles₁
  条件: (x)
  证明: rfl
-/
lemma coe_mapCycles₁ (x) :
    (mapCycles₁ f φ x).1 = chainsMap₁ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cyclesMap_comp_isoCycles₁_hom` / 引理 `cyclesMap_comp_isoCycles₁_hom`

English:
lemma cyclesMap_comp_isoCycles₁_hom
  proof: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapShortComplexH1,
    chainsMap_f_1_comp_chainsIso₁ f]

中文:
引理 cyclesMap_comp_isoCycles₁_hom
  证明: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapShortComplexH1,
    chainsMap_f_1_comp_chainsIso₁ f]

Depends on / 依赖: cancel_mono, mapShortComplexH1, moduleCatLeftHomologyData, shortComplexH1
-/
lemma cyclesMap_comp_isoCycles₁_hom :
    cyclesMap f φ 1 ≫ (isoCycles₁ B).hom = (isoCycles₁ A).hom ≫ mapCycles₁ f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapShortComplexH1,
    chainsMap_f_1_comp_chainsIso₁ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `H1π_comp_map` / 引理 `H1π_comp_map`

English:
lemma H1π_comp_map
  proof: by
  simp [H1π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₁_hom_assoc]

@[simp]

中文:
引理 H1π_comp_map
  证明: by
  simp [H1π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₁_hom_assoc]

@[simp]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
lemma H1π_comp_map :
    H1π A ≫ map f φ 1 = mapCycles₁ f φ ≫ H1π B := by
  simp [H1π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₁_hom_assoc]

@[simp]
/--
lemma `map₁_one` / 引理 `map₁_one`

English:
lemma map₁_one
  given: (φ : A ⟶ res (1 : G ->* H) B)
  proof: by
  simp only [← cancel_epi (H1π A), H1π_comp_map, Limits.comp_zero]
  ext x
  rw [ModuleCat.hom_comp]
  refine (H1π_eq_zero_iff _).2 ?_
  simpa [coe_mapCycles₁ _ φ x, mapDomain, map_finsuppSum] using
    (boundaries₁ B).finsuppSum_mem k x.1 _ fun _ _ => single_one_mem_boundaries₁ (A := B) _

中文:
引理 map₁_one
  条件: (φ : A ⟶ res (1 : G ->* H) B)
  证明: by
  simp only [← cancel_epi (H1π A), H1π_comp_map, Limits.comp_zero]
  ext x
  rw [ModuleCat.hom_comp]
  refine (H1π_eq_zero_iff _).2 ?_
  simpa [coe_mapCycles₁ _ φ x, mapDomain, map_finsuppSum] using
    (boundaries₁ B).finsuppSum_mem k x.1 _ fun _ _ => single_one_mem_boundaries₁ (A := B) _

Depends on / 依赖: Limits, Limits.comp_zero, ModuleCat, ModuleCat.hom_comp, cancel_epi, comp_zero, finsuppSum_mem, hom_comp, mapDomain, map_finsuppSum
-/
lemma map₁_one (φ : A ⟶ res (1 : G ->* H) B) :
    map (1 : G ->* H) φ 1 = 0 := by
  simp only [← cancel_epi (H1π A), H1π_comp_map, Limits.comp_zero]
  ext x
  rw [ModuleCat.hom_comp]
  refine (H1π_eq_zero_iff _).2 ?_
  simpa [coe_mapCycles₁ _ φ x, mapDomain, map_finsuppSum] using
    (boundaries₁ B).finsuppSum_mem k x.1 _ fun _ _ => single_one_mem_boundaries₁ (A := B) _

section CoresCoinf

/-!
### Exactness of the corestriction-coinflation sequence in degree 1

Given a group homomorphism `f : G →* H`, the `n`th corestriction map is the map
`Hₙ(G, Res(f)(A)) ⟶ Hₙ(H, A)` induced by `f` and the identity map on `Res(f)(A)`. Similarly, given
a normal subgroup `S ≤ G`, we define the `n`th coinflation map `Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` as the
map induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`.

In particular, for `S ≤ G` normal and `A : Rep k G`, the corestriction map
`Hₙ(S, Res(ι)(A)) ⟶ Hₙ(G, A)` and the coinflation map `Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` form a short
complex, where `ι : S →* G` is the natural inclusion. In this section we define this short complex
for degree 1, `groupHomology.H1CoresCoinf A S`, and prove it is exact.

We do this first when `A` is `S`-trivial, and then extend to the general case.

-/

variable (A) (S : Subgroup G) [S.Normal]

section OfTrivial

variable [IsTrivial (A.ρ.comp S.subtype)]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `mapCycles₁_quotientGroupMk'_epi` / 实例 `mapCycles₁_quotientGroupMk'_epi`

English:
instance mapCycles₁_quotientGroupMk'_epi
  signature: :
  body: by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  have hs₁ : QuotientGroup.mk ∘ s = id := funext hs
refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext by
    simp [mapCycles₁_hom, ← mapDomain_comp, hs₁, res, Rep.hom_id (of _)]⟩
  simpa [mem_cyc

中文:
实例 mapCycles₁_quotientGroupMk'_epi
  签名: :
  定义体: by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  have hs₁ : QuotientGroup.mk ∘ s = id := funext hs
refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext by
    simp [mapCycles₁_hom, ← mapDomain_comp, hs₁, res, Rep.hom_id (of _)]⟩
  simpa [mem_cyc

Depends on / 依赖: Finsupp, Finsupp.sum_congr, ModuleCat, ModuleCat.epi_iff_surjective, QuotientGroup, QuotientGroup.induction_on, QuotientGroup.mk, QuotientGroup.mk_, QuotientGroup.mk_surjective, Rep.hom_id, Subtype, Subtype.ext, epi_iff_surjective, hom_id, induction_on, mapDomain, mapDomain_comp, mk_surjective, sum_congr, sum_mapDomain_index_inj
-/
instance mapCycles₁_quotientGroupMk'_epi :
    Epi (mapCycles₁ (QuotientGroup.mk' S) (resOfQuotientIso A S).inv) := by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  have hs₁ : QuotientGroup.mk ∘ s = id := funext hs
refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext by
    simp [mapCycles₁_hom, ← mapDomain_comp, hs₁, res, Rep.hom_id (of _)]⟩
  simpa [mem_cycles₁_iff, ← (mem_cycles₁_iff _).1 hx, sum_mapDomain_index_inj (f := s)
      (fun x y h => by rw [← hs x, ← hs y, h])]
    using Finsupp.sum_congr fun a b => QuotientGroup.induction_on a fun a => by
      simp [← QuotientGroup.mk_inv, apply_eq_of_coe_eq A.ρ S (s a)⁻¹ a⁻¹ (by simp [hs])]

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, this is the
short complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A)`. (This is a simplified expression for the
degree 1 corestriction-coinflation sequence when `A` is `S`-trivial.) -/
@[simps X₁ X₂ X₃ f g]
/--
Definition of `H1CoresCoinfOfTrivial` / `H1CoresCoinfOfTrivial` 的定义

English:
definition H1CoresCoinfOfTrivial
  signature: :
  body: H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (ofQuotient A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

中文:
定义 H1CoresCoinfOfTrivial
  签名: :
  定义体: H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (ofQuotient A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

Depends on / 依赖: S.subtype, subtype
-/
noncomputable def H1CoresCoinfOfTrivial :
    ShortComplex (ModuleCat k) where
  X₁ := H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (ofQuotient A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

/--
Instance `map₁_quotientGroupMk'_epi` / 实例 `map₁_quotientGroupMk'_epi`

English:
instance map₁_quotientGroupMk'_epi
  signature: :
  body: by
  convert! epi_of_epi (H1π A) _
  rw [H1π_comp_map]
  exact @epi_comp _ _ _ _ _ _ (mapCycles₁_quotientGroupMk'_epi A S) (H1π _) inferInstance

中文:
实例 map₁_quotientGroupMk'_epi
  签名: :
  定义体: by
  convert! epi_of_epi (H1π A) _
  rw [H1π_comp_map]
  exact @epi_comp _ _ _ _ _ _ (mapCycles₁_quotientGroupMk'_epi A S) (H1π _) inferInstance

Depends on / 依赖: Ideal.span, Ideal.span_insert, IsBezout, IsBezout.iff_span_pair_isPrincipal, ValuationRing, _epi, classical, convert, epi_comp, epi_of_epi, iff_span_pair_isPrincipal, le_total, span_insert, sup_eq_left, sup_eq_left.mpr, sup_eq_right, sup_eq_right.mpr
-/
instance map₁_quotientGroupMk'_epi :
    Epi (map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv 1) := by
  convert! epi_of_epi (H1π A) _
  rw [H1π_comp_map]
  exact @epi_comp _ _ _ _ _ _ (mapCycles₁_quotientGroupMk'_epi A S) (H1π _) inferInstance

/--
Instance `H1CoresCoinfOfTrivial_g_epi` / 实例 `H1CoresCoinfOfTrivial_g_epi`

English:
instance H1CoresCoinfOfTrivial_g_epi
  signature: :
  body: inferInstanceAs Epi (map _ _ 1)

中文:
实例 H1CoresCoinfOfTrivial_g_epi
  签名: :
  定义体: inferInstanceAs Epi (map _ _ 1)

Depends on / 依赖: Ideal.mem_span_pair.mp, Ideal.mem_span_singleton, Ideal.span, Ideal.subset_span, IsBezout, IsBezout.span_pair_isPrincipal, IsLocalRing, ValuationRing, iff_dvd_total, iff_dvd_total.mpr, mem_span_pair, mem_span_singleton, span_pair_isPrincipal, subset_span
-/
instance H1CoresCoinfOfTrivial_g_epi :
    Epi (H1CoresCoinfOfTrivial A S).g :=
inferInstanceAs Epi (map _ _ 1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `H1CoresCoinfOfTrivial_exact` / 定理 `H1CoresCoinfOfTrivial_exact`

English:
theorem H1CoresCoinfOfTrivial_exact
  proof: by
  classical
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx

中文:
定理 H1CoresCoinfOfTrivial_exact
  证明: by
  classical
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx

Depends on / 依赖: ShortComplex, ShortComplex.moduleCat_exact_iff_ker_sub_range, classical, moduleCat_exact_iff_ker_sub_range
-/
theorem H1CoresCoinfOfTrivial_exact :
    (H1CoresCoinfOfTrivial A S).Exact := by
  classical
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
/- Denote `C(i) : C(S, A) ⟶ C(G, A), C(π) : C(G, A) ⟶ C(G ⧸ S, A)` and let `x : Z₁(G, A)` map to
0 in `H₁(G ⧸ S, A)`. -/
  induction x using H1_induction_on with | @h x =>
  rcases x with ⟨x, hxc⟩
  simp_all only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₃, H1CoresCoinfOfTrivial_g,
    LinearMap.mem_ker, H1π_comp_map_apply (QuotientGroup.mk' S)]
/- Choose `y := ∑ y(σ, τ)·(σ, τ) ∈ C₂(G ⧸ S, A)` such that `C₁(π)(x) = d(y)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Let `s : G ⧸ S → G` be a section of the quotient map. -/
  choose! s hs using QuotientGroup.mk'_surjective S
  have hs₁ : QuotientGroup.mk (s := S) ∘ s = id := funext hs
/- Let `z := ∑ y(σ, τ)·(s(σ), s(τ))`. -/
  let z : G × G ->₀ A := lmapDomain _ k (Prod.map s s) y
/- We have that `C₂(π)(z) = y`. -/
  have hz : lmapDomain _ k (QuotientGroup.mk' S) ((d₂₁ A).hom z) =
      (d₂₁ (A.ofQuotient S)).hom y := by
    have := congr($((mapShortComplexH1 (QuotientGroup.mk' S)
      (resOfQuotientIso A S).inv).comm₁₂.symm) z)
    simp_all [shortComplexH1, z, ← mapDomain_comp, Prod.map_comp_map, Rep.hom_id (res _ _)]
  let v := x - (d₂₁ _).hom z
/- We have `C₁(s ∘ π)(v) = ∑ v(g)·s(π(g)) = 0`, since `C₁(π)(v) = dC₁(π)(z) - C₁(π)(dz) = 0` by
previous assumptions. -/
  have hv : mapDomain (s ∘ QuotientGroup.mk) v = 0 := by
    rw [mapDomain_comp]
    simp only [QuotientGroup.coe_mk', lmapDomain_apply, mapDomain_sub, v] at hz ⊢
    simp [hz, hy, coe_mapCycles₁ (QuotientGroup.mk' S), Rep.hom_id (of _)]
  let e : G -> G × G := fun (g : G) => (s (g : G ⧸ S), (s (g : G ⧸ S))⁻¹ * g)
  have he : e.Injective := fun x y hxy => by
    obtain ⟨(h₁ : s _ = s _), (h₂ : _ * _ = _ * _)⟩ := Prod.ext_iff.1 hxy
    exact (mul_right_inj _).1 (h₁ ▸ h₂)
/- Let `ve := ∑ v(g)·(s(π(g)), s(π(g))⁻¹g)`. -/
  let ve : G × G ->₀ A := mapDomain e v
  have hS : ((v + d₂₁ _ ve).support : Set G) subseteq S := by
  /- We have `d(ve) = ∑ ρ(s(π(g))⁻¹)(v(g))·s(π(g))⁻¹g - ∑ v(g)·g + ∑ v(g)·s(π(g))`.
    The second sum is `v`, so cancels: -/
    simp only [d₂₁, ve, ModuleCat.hom_ofHom, coe_lsum, sum_mapDomain_index_inj he, sum_single,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      lsingle_apply, sum_add, sum_sub, mul_inv_cancel_left, ← add_assoc, add_sub_cancel, e]
    intro w hw
    · obtain (hl | hr) := Finset.mem_union.1 (support_add hw)
    /- The first sum clearly has support in `S`: -/
      · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 (support_sum hl)
        apply support_single_subset at ht
        simp_all [← QuotientGroup.eq]
    /- The third sum is 0, by `hv`. -/
      · simp_all [mapDomain]
  /- Now `v + d(ve)` has support in `S` and agrees with `x` in `H₁(G, A)`: -/
use H1π _ ⟨comapDomain Subtype.val (v + d₂₁ _ ve)
    Set.injOn_of_injective Subtype.val_injective, ?_⟩
  · simp only [H1CoresCoinfOfTrivial_f, H1CoresCoinfOfTrivial_X₁, H1π_comp_map_apply]
    refine (H1π_eq_iff _ _).2 ?_
  /- Indeed, `v + d(ve) - x = d(ve - z) ∈ B₁(G, A)`, since `v := x - dz`. -/
    use ve - z
    have := mapDomain_comapDomain (α := S) Subtype.val Subtype.val_injective
      (v + d₂₁ A ve) (fun x hx => ⟨⟨x, hS hx⟩, rfl⟩)
    simp_all [mapCycles₁_hom, v, add_sub_assoc, sub_add_sub_cancel']
  /- And `v + d(ve) := x - dz + d(ve)` is a 1-cycle because `x` is. -/
  · have : v + d₂₁ _ ve in cycles₁ A := Submodule.add_mem _
      (Submodule.sub_mem _ hxc <| d₂₁_apply_mem_cycles₁ _) (d₂₁_apply_mem_cycles₁ _)
    rw [mem_cycles₁_iff] at this ⊢
    rwa [← sum_comapDomain, ← sum_comapDomain (g := fun _ a => a)] at this <;>
    exact ⟨Set.mapsTo_preimage _ _, Set.injOn_of_injective Subtype.val_injective,
      fun x hx => ⟨⟨x, hS hx⟩, hx, rfl⟩⟩

end OfTrivial

set_option backward.isDefEq.respectTransparency.types false in
/-- The short complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)`. The first map is the
"corestriction" map induced by the inclusion `ι : S →* G` and the identity on `Res(ι)(A)`, and the
second map is the "coinflation" map induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`. -/
@[simps X₁ X₂ X₃ f g]
/--
Definition of `H1CoresCoinf` / `H1CoresCoinf` 的定义

English:
definition H1CoresCoinf
  signature: :
  body: H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (quotientToCoinvariants A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ A S) 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

中文:
定义 H1CoresCoinf
  签名: :
  定义体: H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (quotientToCoinvariants A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ A S) 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

Depends on / 依赖: S.subtype, subtype
-/
noncomputable def H1CoresCoinf :
    ShortComplex (ModuleCat k) where
  X₁ := H1 (res S.subtype A)
  X₂ := H1 A
  X₃ := H1 (quotientToCoinvariants A S)
  f := map S.subtype (𝟙 _) 1
  g := map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ A S) 1
  zero := by rw [← map_comp, congr (QuotientGroup.mk'_comp_subtype S) (map (n := 1)), map₁_one]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top` / 定理 `comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top`

English:
theorem comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top
  proof: by
  rw [eq_top_iff]
  intro x _
  rcases mapRange_surjective _ (map_zero _) (chains₁ToCoinvariantsKer_surjective
    (res S.subtype A)) x with ⟨(X : G ->₀ S ->₀ A), hX⟩
  let Y : S ->₀ A := X.sum fun g f =>
    mapRange.linearMap (A.ρ g⁻¹) (lmapDomain _ k (fun s => MulAut.conjNormal g⁻¹ s) f) - f
 

中文:
定理 comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top
  证明: by
  rw [eq_top_iff]
  intro x _
  rcases mapRange_surjective _ (map_zero _) (chains₁ToCoinvariantsKer_surjective
    (res S.subtype A)) x with ⟨(X : G ->₀ S ->₀ A), hX⟩
  let Y : S ->₀ A := X.sum fun g f =>
    mapRange.linearMap (A.ρ g⁻¹) (lmapDomain _ k (fun s => MulAut.conjNormal g⁻¹ s) f) - f
 

Depends on / 依赖: MulAut, MulAut.conjNormal, S.subtype, X.sum, conjNormal, eq_top_iff, linearMap, lmapDomain, mapRange, mapRange.linearMap, mapRange_surjective, map_zero, moduleCat_pOpcycles_eq_iff, subtype
-/
theorem comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top :
    Submodule.comap ((mapShortComplexH1 (MonoidHom.id G) (coinvariantsShortComplex A S).f).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom (LinearMap.range ((mapShortComplexH1 S.subtype (𝟙 _)).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases mapRange_surjective _ (map_zero _) (chains₁ToCoinvariantsKer_surjective
    (res S.subtype A)) x with ⟨(X : G ->₀ S ->₀ A), hX⟩
  let Y : S ->₀ A := X.sum fun g f =>
    mapRange.linearMap (A.ρ g⁻¹) (lmapDomain _ k (fun s => MulAut.conjNormal g⁻¹ s) f) - f
  let Z : G × G ->₀ A := X.sum fun g f =>
    lmapDomain _ k (fun s => (g, g⁻¹ * s.1 * g)) f - lmapDomain _ k (fun s => (s.1, g)) f
  use Y
  apply (moduleCat_pOpcycles_eq_iff _ _ _).2 ⟨Z, ?_⟩
  change d₂₁ A Z = mapRange id rfl (lmapDomain _ k Subtype.val Y) -
    mapRange.linearMap (Submodule.subtype _) (mapDomain id x)
  simpa [map_finsuppSum, mapDomain, map_sub, ← hX, sum_single_index, curryLinearEquiv,
    curryEquiv, Finsupp.uncurry, d₂₁, Y, Z, sum_mapRange_index,
    chains₁ToCoinvariantsKer, d₁₀, single_sum, mul_assoc, sub_add_eq_add_sub,
    sum_sum_index, add_smul, sub_sub_sub_eq, lsingle, singleAddHom] using add_comm _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (H1CoresCoinf A S).g
  body: by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  induction x using H1_induction_on with | @h x =>

中文:
实例 :
  签名: Epi (H1CoresCoinf A S).g
  定义体: by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  induction x using H1_induction_on with | @h x =>

Depends on / 依赖: H1_induction_on, ModuleCat, ModuleCat.epi_iff_surjective, epi_iff_surjective
-/
instance : Epi (H1CoresCoinf A S).g := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  induction x using H1_induction_on with | @h x =>
/- Let `x : Z₁(G ⧸ S, A_S)`. We know `Z₁(G, A_S) ⟶ Z₁(G ⧸ S, A_S)` is surjective, so pick
`y : Z₁(G, A_S)` in the preimage of `x`. -/
  rcases (ModuleCat.epi_iff_surjective _).1
    (mapCycles₁_quotientGroupMk'_epi (A.toCoinvariants S) S) x with ⟨y, hy⟩
/- We know `C₁(G, A) ⟶ C₁(G, A_S)` is surjective, so pick `Y` in the preimage of `y`. -/
  rcases mapRange_surjective _ (map_zero _)
    (Coinvariants.mk_surjective (A.ρ.comp S.subtype)) y.1 with ⟨Y, hY⟩
/- Then `d(Y) ∈ I(S)A,` since `d(y) = 0`. -/
  have : d₁₀ _ Y in Coinvariants.ker (A.ρ.comp S.subtype) := by
    have h' := congr($((mapShortComplexH1 (B := toCoinvariants A S)
      (MonoidHom.id G) (toCoinvariantsMkQ A S)).comm₂₃) Y)
    simp_all [shortComplexH1, ← Coinvariants.mk_eq_zero]
  /- Thus we can pick a representation of `d(Y)` as a sum `∑ ρ(sᵢ⁻¹)(aᵢ) - aᵢ`, `sᵢ ∈ S, aᵢ ∈ A`,
and `Y - ∑ aᵢ·sᵢ` is a cycle. -/
  rcases chains₁ToCoinvariantsKer_surjective
    (res S.subtype A) ⟨d₁₀ A Y, this⟩ with ⟨(Z : S ->₀ A), hZ⟩
  have H : d₁₀ A (Y - mapDomain S.subtype Z) = 0 := by
    simpa [map_sub, sub_eq_zero, chains₁ToCoinvariantsKer, -LinearMap.sub_apply, d₁₀,
      sum_mapDomain_index_inj] using! Subtype.ext_iff.1 hZ.symm
  use H1π A ⟨Y - mapDomain S.subtype Z, H⟩
  simp only [H1CoresCoinf_X₃, H1CoresCoinf_X₂, H1CoresCoinf_g,
    Subgroup.coe_subtype, H1π_comp_map_apply]
/- Moreover, the image of `Y - ∑ aᵢ·sᵢ` in `Z₁(G ⧸ S, A_S)` is `x - ∑ aᵢ·1`, and hence differs from
`x` by a boundary, since `aᵢ·1 = d(aᵢ·(1, 1))`. -/
  refine (H1π_eq_iff _ _).2 ?_
  simpa [← hy, mapCycles₁_hom, map_sub, Rep.hom_id (res _ _), ← mapDomain_comp,
    ← mapDomain_mapRange, hY, Function.comp_def, (QuotientGroup.eq_one_iff <| Subtype.val _).2
    (Subtype.prop _)] using! Submodule.finsuppSum_mem _ _ _ _ fun _ _ => single_one_mem_boundaries₁ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `H1CoresCoinf_exact` / 定理 `H1CoresCoinf_exact`

English:
theorem H1CoresCoinf_exact
  proof: by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₃, LinearMap.mem_ker, H1CoresCoinf_g,
    H1π_comp_map_apply (QuotientGroup.mk' S)] at hx

中文:
定理 H1CoresCoinf_exact
  证明: by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₃, LinearMap.mem_ker, H1CoresCoinf_g,
    H1π_comp_map_apply (QuotientGroup.mk' S)] at hx

Depends on / 依赖: H1CoresCoinf_g, H1_induction_on, LinearMap, LinearMap.mem_ker, QuotientGroup, QuotientGroup.mk, ShortComplex, ShortComplex.moduleCat_exact_iff_ker_sub_range, mem_ker, moduleCat_exact_iff_ker_sub_range
-/
theorem H1CoresCoinf_exact :
    (H1CoresCoinf A S).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₃, LinearMap.mem_ker, H1CoresCoinf_g,
    H1π_comp_map_apply (QuotientGroup.mk' S)] at hx
/- Let `x : Z₁(G, A)` map to 0 in `H₁(G, ⧸ S, A_S)`. Pick `y : C₂(G ⧸ S, A_S)` such that `d(y)`
equals `Z₁(π, π)(x) : Z₁(G ⧸ S, A_S)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Then `Z₁(π, Id)(x) : Z₁(G, A_S)` maps to 0 in `H₁(G ⧸ S, A_S)`. We know
`H₁(S, A_S) ⟶ H₁(G, A_S) ⟶ H₁(G ⧸ S, A_S)` is exact by `H1CoresCoinfOfTrivial_exact`, since
`S` acts trivially on `A_S`. So we can choose `z : Z₁(S, A_S)` with the same homology class as
`Z₁(π, Id)(π)` in `H₁(G, A_S)`. -/
  rcases @(ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (H1CoresCoinfOfTrivial_exact (toCoinvariants A S) S)
    (H1π _ <| mapCycles₁ (MonoidHom.id G) (Rep.toCoinvariantsMkQ A S) x) (by
    simpa only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₃, H1CoresCoinfOfTrivial_g,
      Iso.refl_inv, LinearMap.mem_ker, H1π_comp_map_apply (QuotientGroup.mk' S),
      ← mapCycles₁_comp_apply (x := x)] using! hx) with ⟨z, hz⟩
  induction z using H1_induction_on with | @h z =>
  simp only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₁, H1CoresCoinfOfTrivial_f] at hz
  rw [H1π_comp_map_apply] at hz
/- Choose `w : C₂(G, A_S)` such that `d(w) = Z₁(i, Id)(z) - Z₁(Id, π)(x)`. -/
  rcases (H1π_eq_iff _ _).1 hz with ⟨w, hzw⟩
/- Choose `Z : C₁(S, A)` mapping to `z : C₁(S, A_S)`, and `W : C₂(G, A)` mapping to
`w : C₂(G, A_S)`. -/
  rcases mapRange_surjective (Coinvariants.mk _) (map_zero _)
    (Coinvariants.mk_surjective _) z.1 with ⟨Z, hZ⟩
  rcases mapRange_surjective (Coinvariants.mk _) (map_zero _)
    (Coinvariants.mk_surjective _) w with ⟨W, hW⟩
/- Let `b : C₁(G, A)` denote `x + d(W) - C₁(i, Id)(z)`. -/
  let b : G ->₀ A := (x.1 : G ->₀ A) + d₂₁ A W - lmapDomain _ k S.subtype Z
/- Then `b` has coefficients in `I(S)A := ⟨{ρ(s)(a) - a | s ∈ S, a ∈ A}⟩`, since
`C₁(G, I(S)(A)) ⟶ C₁(G, A) ⟶ C₁(G, A_S)` is exact, and `b` is in the kernel of the second map. -/
  have hb : forall g, b g in Coinvariants.ker (A.ρ.comp S.subtype) :=
fun g => (Coinvariants.mk_eq_iff _).1 by
      have := Finsupp.ext_iff.1 (congr($((mapShortComplexH1 (B := toCoinvariants A S)
        (MonoidHom.id G) (toCoinvariantsMkQ A S)).comm₁₂.symm) W)) g
      simp only [shortComplexH1, mapShortComplexH1_τ₂, ModuleCat.ofHom_comp, MonoidHom.coe_id,
        lmapDomain_id, ModuleCat.ofHom_id, res_obj_ρ, hom_ofHom, Category.id_comp,
        mapShortComplexH1_τ₁, Prod.map_id, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.coe_comp, Function.comp_apply, mapRange.linearMap_apply, mapRange_apply] at this
      simp only [← mapRange_apply (f := Coinvariants.mk <| A.ρ.comp S.subtype)
        (hf := map_zero _) (a := g), ← mapRange.linearMap_apply (R := k)]
      simp [← mapDomain_mapRange, hZ, this, hW, hzw, coe_mapCycles₁ S.subtype,
        coe_mapCycles₁ (MonoidHom.id G)]
/- Let `β` be `b` considered as an element of `C₁(G, I(S)(A))`, so that `C₁(Id, i)(β) = b`. -/
  let β : G ->₀ Coinvariants.ker (A.ρ.comp S.subtype) :=
    mapRange (Function.invFun <| (Coinvariants.ker (A.ρ.comp S.subtype)).subtype)
    (Function.leftInverse_invFun Subtype.val_injective (0 : Coinvariants.ker _)) b
have hβb : mapRange Subtype.val rfl β = b := Finsupp.ext fun g => Subtype.ext_iff.1
    Function.leftInverse_invFun Subtype.val_injective ⟨b g, hb g⟩
/- Then, since the image of `C₁(G, I(S)A)` in `C₁(G, A)⧸B₁(G, A)` is contained in the image of
`C₁(S, A)` by `comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top`, we can choose
`α : C₁(S, A)`, `δ : C₂(G, A)` such that `d(δ) = Z₁(i, Id)(α) - Z₁(Id, i)(β)`. -/
  rcases eq_top_iff.1 (comap_coinvariantsKer_pOpcycles_range_subtype_pOpcycles_eq_top A S)
    (by trivial : β in ⊤) with ⟨(α : S ->₀ A), hα⟩
  dsimp only [ModuleCat.hom_comp] at hα
  rcases (moduleCat_pOpcycles_eq_iff _ _ _).1 hα with ⟨(δ : G × G ->₀ A), hβ⟩
/- Then, by assumption, `d(W + δ) = C₁(i, Id)(α + Z) - x`. -/
  have hαZ : d₂₁ A (W + δ) = mapDomain Subtype.val (α + Z) - x := by
    simp_all [shortComplexH1, coinvariantsShortComplex_X₁,
      ← sub_add, ← sub_sub, sub_add_eq_add_sub, mapDomain_add, b]
/- So we claim that `α + Z` is an element of `Z₁(S, A)` which differs from `x` by a boundary in
`Z₁(G, A)`. -/
  use H1π _ ⟨α + Z, ?_⟩
/- Indeed, by `hαZ`, `d(W + δ)` is the desired boundary: -/
  · simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₁, H1CoresCoinf_f, H1π_comp_map_apply]
    refine (H1π_eq_iff _ _).2 ⟨W + δ, ?_⟩
    simp [hαZ, mapCycles₁_hom]
/- And `α + Z` is a cycle, since `d(W + δ) + x` is. -/
  · rw [mem_cycles₁_iff]
    have : x + d₂₁ A (W + δ) in cycles₁ A := Submodule.add_mem _ x.2 (d₂₁_apply_mem_cycles₁ _)
    rwa [eq_sub_iff_add_eq'.1 hαZ, mem_cycles₁_iff, sum_mapDomain_index_inj
      Subtype.val_injective, sum_mapDomain_index_inj Subtype.val_injective] at this

end CoresCoinf

end H1

section H2

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : A ⟶ Res(f)(B)`,
this is the induced map from the short complex
`(G × G × G →₀ A) --d₃₂--> (G × G →₀ A) --d₂₁--> (G →₀ A)` to
`(H × H × H →₀ B) --d₃₂--> (H × H →₀ B) --d₂₁--> (H →₀ B)`. -/
@[simps]
/--
Definition of `mapShortComplexH2` / `mapShortComplexH2` 的定义

English:
definition mapShortComplexH2
  signature: :
  body: chainsMap₃ f φ
  τ₂ := chainsMap₂ f φ
  τ₃ := chainsMap₁ f φ
  comm₁₂ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [d₃₂, map_add, map_sub, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [

中文:
定义 mapShortComplexH2
  签名: :
  定义体: chainsMap₃ f φ
  τ₂ := chainsMap₂ f φ
  τ₃ := chainsMap₁ f φ
  comm₁₂ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [d₃₂, map_add, map_sub, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [
-/
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := chainsMap₃ f φ
  τ₂ := chainsMap₂ f φ
  τ₃ := chainsMap₁ f φ
  comm₁₂ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [d₃₂, map_add, map_sub, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))
  comm₂₃ := by
    simp only [shortComplexH2]
    ext : 3
    simpa [d₂₁, map_add, map_sub, ← map_inv]
      using congr(Finsupp.single _ $((hom_comm_apply φ _ _).symm))

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mapShortComplexH2_zero` / 定理 `mapShortComplexH2_zero`

English:
theorem mapShortComplexH2_zero
  proof: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

@[simp]

中文:
定理 mapShortComplexH2_zero
  证明: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.hom_ext, all_goals, hom_ext, shortComplexH2
-/
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

@[simp]
/--
theorem `mapShortComplexH2_id` / 定理 `mapShortComplexH2_id`

English:
theorem mapShortComplexH2_id
  statement: mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _
  proof: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

中文:
定理 mapShortComplexH2_id
  结论: mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _
  证明: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

Depends on / 依赖: ShortComplex, ShortComplex.hom_ext, all_goals, hom_ext, shortComplexH2
-/
theorem mapShortComplexH2_id : mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp }

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mapShortComplexH2_comp` / 定理 `mapShortComplexH2_comp`

English:
theorem mapShortComplexH2_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp [Prod.map] }

中文:
定理 mapShortComplexH2_comp
  结论: {G H K : 类型u} [Group G] [Group H] [Group K]
  证明: by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp [Prod.map] }

Depends on / 依赖: Prod.map, ShortComplex, ShortComplex.hom_ext, all_goals, hom_ext, shortComplexH2
-/
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G ->* H) (g : H ->* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapShortComplexH2 (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      (mapShortComplexH2 f φ) ≫ (mapShortComplexH2 g ψ) := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  all_goals
  { simp only [shortComplexH2]
    ext
    simp [Prod.map] }

/--
theorem `mapShortComplexH2_id_comp` / 定理 `mapShortComplexH2_id_comp`

English:
theorem mapShortComplexH2_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: mapShortComplexH2_comp (MonoidHom.id G) (MonoidHom.id G) _ _

中文:
定理 mapShortComplexH2_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: mapShortComplexH2_comp (MonoidHom.id G) (MonoidHom.id G) _ _

Depends on / 依赖: MonoidHom, MonoidHom.id, ValuationRing, mapShortComplexH2_comp, of_field
-/
theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ :=
  mapShortComplexH2_comp (MonoidHom.id G) (MonoidHom.id G) _ _

/--
Definition of `mapCycles₂` / `mapCycles₂` 的定义

English:
abbreviation mapCycles₂
  signature: :
  body: ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

中文:
缩写 mapCycles₂
  签名: :
  定义体: ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

Depends on / 依赖: ShortComplex, ShortComplex.cyclesMap, cyclesMap, mapShortComplexH2, moduleCatLeftHomologyData, shortComplexH2
-/
noncomputable abbrev mapCycles₂ :
    ModuleCat.of k (cycles₂ A) ⟶ ModuleCat.of k (cycles₂ B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapCycles₂_hom` / 引理 `mapCycles₂_hom`

English:
lemma mapCycles₂_hom
  proof: rfl

中文:
引理 mapCycles₂_hom
  证明: rfl

Depends on / 依赖: mapShortComplexH2, shortComplexH2
-/
lemma mapCycles₂_hom :
    (mapCycles₂ f φ).hom = (chainsMap₂ f φ).hom.restrict (fun x _ => by
      have := congr($((mapShortComplexH2 f φ).comm₂₃) x); simp_all [cycles₂, shortComplexH2]) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
lemma `mapCycles₂_comp` / 引理 `mapCycles₂_comp`

English:
lemma mapCycles₂_comp
  statement: {G H K : Type u} [Group G] [Group H] [Group K]
  proof: by
  rw [← cyclesMap'_comp]; rw [← mapShortComplexH2_comp]

@[reassoc, elementwise]

中文:
引理 mapCycles₂_comp
  结论: {G H K : 类型u} [Group G] [Group H] [Group K]
  证明: by
  rw [← cyclesMap'_comp]; rw [← mapShortComplexH2_comp]

@[reassoc, elementwise]

Depends on / 依赖: _comp, cyclesMap, mapShortComplexH2_comp
-/
lemma mapCycles₂_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k G} {B : Rep k H} {C : Rep k K} (f : G ->* H) (g : H ->* K)
    (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    mapCycles₂ (g.comp f) (φ ≫ (resFunctor f).map ψ) =
      mapCycles₂ f φ ≫ mapCycles₂ g ψ := by
  rw [← cyclesMap'_comp]; rw [← mapShortComplexH2_comp]

@[reassoc, elementwise]
/--
theorem `mapCycles₂_id_comp` / 定理 `mapCycles₂_id_comp`

English:
theorem mapCycles₂_id_comp
  given: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  proof: mapCycles₂_comp (MonoidHom.id G) (MonoidHom.id G) _ _

中文:
定理 mapCycles₂_id_comp
  条件: {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)
  证明: mapCycles₂_comp (MonoidHom.id G) (MonoidHom.id G) _ _

Depends on / 依赖: MonoidHom, MonoidHom.id
-/
theorem mapCycles₂_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapCycles₂ (MonoidHom.id G) (φ ≫ ψ) =
      mapCycles₂ (MonoidHom.id G) φ ≫ mapCycles₂ (MonoidHom.id G) ψ :=
  mapCycles₂_comp (MonoidHom.id G) (MonoidHom.id G) _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc, elementwise]
/--
lemma `mapCycles₂_comp_i` / 引理 `mapCycles₂_comp_i`

English:
lemma mapCycles₂_comp_i
  proof: by
  simp

@[simp]

中文:
引理 mapCycles₂_comp_i
  证明: by
  simp

@[simp]
-/
lemma mapCycles₂_comp_i :
    mapCycles₂ f φ ≫ (shortComplexH2 B).moduleCatLeftHomologyData.i =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ chainsMap₂ f φ := by
  simp

@[simp]
/--
lemma `coe_mapCycles₂` / 引理 `coe_mapCycles₂`

English:
lemma coe_mapCycles₂
  given: (x)
  proof: rfl

中文:
引理 coe_mapCycles₂
  条件: (x)
  证明: rfl
-/
lemma coe_mapCycles₂ (x) :
    (mapCycles₂ f φ x).1 = chainsMap₂ f φ x := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `cyclesMap_comp_isoCycles₂_hom` / 引理 `cyclesMap_comp_isoCycles₂_hom`

English:
lemma cyclesMap_comp_isoCycles₂_hom
  proof: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    chainsMap_f_2_comp_chainsIso₂ f]

中文:
引理 cyclesMap_comp_isoCycles₂_hom
  证明: by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    chainsMap_f_2_comp_chainsIso₂ f]

Depends on / 依赖: cancel_mono, mapShortComplexH2, moduleCatLeftHomologyData, shortComplexH2
-/
lemma cyclesMap_comp_isoCycles₂_hom :
    cyclesMap f φ 2 ≫ (isoCycles₂ B).hom = (isoCycles₂ A).hom ≫ mapCycles₂ f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    chainsMap_f_2_comp_chainsIso₂ f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), elementwise (attr := simp)]
/--
lemma `H2π_comp_map` / 引理 `H2π_comp_map`

English:
lemma H2π_comp_map
  proof: by
  simp [H2π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₂_hom_assoc]

中文:
引理 H2π_comp_map
  证明: by
  simp [H2π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₂_hom_assoc]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
lemma H2π_comp_map :
    H2π A ≫ map f φ 2 = mapCycles₂ f φ ≫ H2π B := by
  simp [H2π, Iso.inv_comp_eq, ← cyclesMap_comp_isoCycles₂_hom_assoc]

end H2

variable (k G)

/-- The functor sending a representation to its complex of inhomogeneous chains. -/
@[simps]
/--
Definition of `chainsFunctor` / `chainsFunctor` 的定义

English:
definition chainsFunctor
  signature: :
  body: inhomogeneousChains A
  map f := chainsMap (MonoidHom.id _) f
  map_id _ := chainsMap_id
  map_comp φ ψ := chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

中文:
定义 chainsFunctor
  签名: :
  定义体: inhomogeneousChains A
  map f := chainsMap (MonoidHom.id _) f
  map_id _ := chainsMap_id
  map_comp φ ψ := chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

Depends on / 依赖: inhomogeneousChains
-/
noncomputable def chainsFunctor :
    Rep k G ⥤ ChainComplex (ModuleCat k) Nat where
  obj A := inhomogeneousChains A
  map f := chainsMap (MonoidHom.id _) f
  map_id _ := chainsMap_id
  map_comp φ ψ := chainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (chainsFunctor k G).PreservesZeroMorphisms
  body: chainsMap_zero (MonoidHom.id G)

中文:
实例 :
  签名: (chainsFunctor k G).PreservesZeroMorphisms
  定义体: chainsMap_zero (MonoidHom.id G)

Depends on / 依赖: MonoidHom, MonoidHom.id, chainsMap_zero
-/
instance : (chainsFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := chainsMap_zero (MonoidHom.id G)

set_option backward.isDefEq.respectTransparency false in
/-- The functor sending a `G`-representation `A` to `Hₙ(G, A)`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: (n : Nat)
  body: groupHomology A n
  map {A B} φ := map (MonoidHom.id _) φ n
  map_id A := by simp [map, groupHomology]
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

中文:
定义 functor
  签名: (n : 自然数)
  定义体: groupHomology A n
  map {A B} φ := map (MonoidHom.id _) φ n
  map_id A := by simp [map, groupHomology]
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

Depends on / 依赖: groupHomology
-/
noncomputable def functor (n : Nat) : Rep k G ⥤ ModuleCat k where
  obj A := groupHomology A n
  map {A B} φ := map (MonoidHom.id _) φ n
  map_id A := by simp [map, groupHomology]
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp, ← chainsMap_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
instance (n : Nat) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

variable {G}

set_option backward.isDefEq.respectTransparency false in
/-- Given a group homomorphism `f : G →* H` this sends `A : Rep k H` to the `n`th
"corestriction" map `Hₙ(G, Res(f)(A)) ⟶ Hₙ(H, A)` induced by `f` and the identity
map on `Res(f)(A)`. -/
@[simps]
/--
Definition of `coresNatTrans` / `coresNatTrans` 的定义

English:
definition coresNatTrans
  signature: (n : Nat)
  body: map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [← cancel_epi (groupHomology.π _ n), Functor.comp_map,
      functor_map, HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← chainsMap_comp, Category.i

中文:
定义 coresNatTrans
  签名: (n : 自然数)
  定义体: map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [← cancel_epi (groupHomology.π _ n), Functor.comp_map,
      functor_map, HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← chainsMap_comp, Category.i
-/
noncomputable def coresNatTrans (n : Nat) :
    resFunctor f ⋙ functor k G n ⟶ functor k H n where
  app X := map f (𝟙 _) n
  naturality {X Y} φ := by
    simp only [← cancel_epi (groupHomology.π _ n), Functor.comp_map,
      functor_map, HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← HomologicalComplex.cyclesMap_comp_assoc,
      ← chainsMap_comp, Category.id_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given a normal subgroup `S ≤ G`, this sends `A : Rep k G` to the `n`th "coinflation" map
`Hₙ(G, A) ⟶ Hₙ(G ⧸ S, A_S)` induced by the quotient maps `G →* G ⧸ S` and `A →ₗ A_S`. -/
@[simps]
/--
Definition of `coinfNatTrans` / `coinfNatTrans` 的定义

English:
definition coinfNatTrans
  signature: (S : Subgroup G) [S.Normal] (n : Nat)
  body: map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ _ _) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupHomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.cyclesMap_comp

中文:
定义 coinfNatTrans
  签名: (S : Subgroup G) [S.Normal] (n : 自然数)
  定义体: map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ _ _) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupHomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.cyclesMap_comp

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, Rep.toCoinvariantsMkQ, toCoinvariantsMkQ
-/
noncomputable def coinfNatTrans (S : Subgroup G) [S.Normal] (n : Nat) :
    functor k G n ⟶ quotientToCoinvariantsFunctor k S ⋙ functor k (G ⧸ S) n where
  app A := map (QuotientGroup.mk' S) (Rep.toCoinvariantsMkQ _ _) n
  naturality {X Y} φ := by
    simp only [Functor.comp_map, functor_map, ← cancel_epi (groupHomology.π _ n),
      HomologicalComplex.homologyπ_naturality_assoc, HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.cyclesMap_comp_assoc, ← chainsMap_comp]
    congr 1

end groupHomology
