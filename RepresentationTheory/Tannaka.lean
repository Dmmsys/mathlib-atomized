/-
Copyright (c) 2025 Yacine Benmeuraiem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yacine Benmeuraiem
-/
module

public import Mathlib.RepresentationTheory.FDRep

/-!
# Tannaka duality for finite groups

In this file we prove Tannaka duality for finite groups.

The theorem can be formulated as follows: for any integral domain `k`, a finite group `G` can be
recovered from `FDRep k G`, the monoidal category of finite-dimensional `k`-linear representations
of `G`, and the monoidal forgetful functor `forget : FDRep k G ⥤ FGModuleCat k`.

The main result is the isomorphism `equiv : G ≃* Aut (forget k G)`.

## Reference

<https://math.leidenuniv.nl/scripties/1bachCommelin.pdf>
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory ModuleCat Finset Pi

universe u

namespace TannakaDuality

namespace FiniteGroup

variable {k G : Type u} [CommRing k] [Group G]

section definitions

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (FDRep k G) (FGModuleCat k)).Monoidal
  body: inferInstanceAs (Action.forget _ _).Monoidal

中文:
实例 :
  签名: (forget₂ (FDRep k G) (FGModuleCat k)).幺半群
  定义体: inferInstanceAs (Action.forget _ _).Monoidal

Depends on / 依赖: Action, Action.forget, Monoidal, forget
-/
instance : (forget₂ (FDRep k G) (FGModuleCat k)).Monoidal :=
inferInstanceAs (Action.forget _ _).Monoidal

variable (k G) in
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  body: LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))

中文:
定义 forget
  定义体: LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))

Depends on / 依赖: FGModuleCat, LaxMonoidalFunctor, LaxMonoidalFunctor.of
-/
def forget := LaxMonoidalFunctor.of (forget₂ (FDRep k G) (FGModuleCat k))

/--
lemma `forget_obj` / 引理 `forget_obj`

English:
lemma forget_obj
  given: (X : FDRep k G)
  statement: (forget k G).obj X = X.V
  proof: rfl

中文:
引理 forget_obj
  条件: (X : FDRep k G)
  结论: (forget k G).obj X = X.V
  证明: rfl
-/
@[simp] lemma forget_obj (X : FDRep k G) : (forget k G).obj X = X.V := rfl

/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: (X Y : FDRep k G) (f : X ⟶ Y)
  statement: (forget k G).map f = f.hom
  proof: rfl

中文:
引理 forget_map
  条件: (X Y : FDRep k G) (f : X ⟶ Y)
  结论: (forget k G).map f = f.hom
  证明: rfl
-/
@[simp] lemma forget_map (X Y : FDRep k G) (f : X ⟶ Y) : (forget k G).map f = f.hom := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Definition of `equivHom g : Aut (forget k G)` by its components. -/
@[simps]
/--
Definition of `equivApp` / `equivApp` 的定义

English:
definition equivApp
  signature: (g : G) (X : FDRep k G)
  body: InducedCategory.homMk (ofHom (X.ρ g))
  inv := InducedCategory.homMk (ofHom (X.ρ g⁻¹))
  hom_inv_id := by
    ext x
    simp
  inv_hom_id := by
    ext x
    simp

中文:
定义 equivApp
  签名: (g : G) (X : FDRep k G)
  定义体: InducedCategory.homMk (ofHom (X.ρ g))
  inv := InducedCategory.homMk (ofHom (X.ρ g⁻¹))
  hom_inv_id := by
    ext x
    simp
  inv_hom_id := by
    ext x
    simp

Depends on / 依赖: InducedCategory, InducedCategory.homMk
-/
def equivApp (g : G) (X : FDRep k G) : X.V ≅ X.V where
  hom := InducedCategory.homMk (ofHom (X.ρ g))
  inv := InducedCategory.homMk (ofHom (X.ρ g⁻¹))
  hom_inv_id := by
    ext x
    simp
  inv_hom_id := by
    ext x
    simp

set_option backward.isDefEq.respectTransparency.types false in
variable (k G) in
/-- The group homomorphism `G →* Aut (forget k G)` shown to be an isomorphism. -/
@[simps]
/--
Definition of `equivHom` / `equivHom` 的定义

English:
definition equivHom
  signature: : G ->* Aut (forget k G) where
  body: LaxMonoidalFunctor.isoOfComponents (equivApp g) (fun f => (f.comm g).symm) rfl (by intros; rfl)
  map_one' := by ext; simp; rfl
  map_mul' _ _ := by ext; simp; rfl

中文:
定义 equivHom
  签名: : G ->* Aut (forget k G) where
  定义体: LaxMonoidalFunctor.isoOfComponents (equivApp g) (fun f => (f.comm g).symm) rfl (by intros; rfl)
  map_one' := by ext; simp; rfl
  map_mul' _ _ := by ext; simp; rfl

Depends on / 依赖: LaxMonoidalFunctor, LaxMonoidalFunctor.isoOfComponents, equivApp, f.comm, intros, isoOfComponents, map_mul, map_one
-/
def equivHom : G ->* Aut (forget k G) where
  toFun g :=
    LaxMonoidalFunctor.isoOfComponents (equivApp g) (fun f => (f.comm g).symm) rfl (by intros; rfl)
  map_one' := by ext; simp; rfl
  map_mul' _ _ := by ext; simp; rfl

/--
Definition of `rightRegular` / `rightRegular` 的定义

English:
definition rightRegular
  signature: : Representation k G (G -> k) where
  body: { toFun f t := f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]

中文:
定义 rightRegular
  签名: : Representation k G (G -> k) where
  定义体: { toFun f t := f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]

Depends on / 依赖: map_add, map_mul, map_one, map_smul, mul_assoc
-/
def rightRegular : Representation k G (G -> k) where
  toFun s :=
  { toFun f t := f (t * s)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]
/--
lemma `rightRegular_apply` / 引理 `rightRegular_apply`

English:
lemma rightRegular_apply
  given: (s t : G) (f : G -> k)
  statement: rightRegular s f t = f (t * s)
  proof: rfl

中文:
引理 rightRegular_apply
  条件: (s t : G) (f : G -> k)
  结论: rightRegular s f t = f (t * s)
  证明: rfl
-/
lemma rightRegular_apply (s t : G) (f : G -> k) : rightRegular s f t = f (t * s) := rfl

/--
Definition of `leftRegular` / `leftRegular` 的定义

English:
definition leftRegular
  signature: : Representation k G (G -> k) where
  body: { toFun f t := f (s⁻¹ * t)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]

中文:
定义 leftRegular
  签名: : Representation k G (G -> k) where
  定义体: { toFun f t := f (s⁻¹ * t)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]

Depends on / 依赖: map_add, map_mul, map_one, map_smul, mul_assoc
-/
def leftRegular : Representation k G (G -> k) where
  toFun s :=
  { toFun f t := f (s⁻¹ * t)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_assoc]

@[simp]
/--
lemma `leftRegular_apply` / 引理 `leftRegular_apply`

English:
lemma leftRegular_apply
  given: (s t : G) (f : G -> k)
  statement: leftRegular s f t = f (s⁻¹ * t)
  proof: rfl

中文:
引理 leftRegular_apply
  条件: (s t : G) (f : G -> k)
  结论: leftRegular s f t = f (s⁻¹ * t)
  证明: rfl
-/
lemma leftRegular_apply (s t : G) (f : G -> k) : leftRegular s f t = f (s⁻¹ * t) := rfl

/-- The right regular representation `rightRegular` on `G → k` as a `FDRep k G`. -/
@[simp]
/--
Definition of `rightFDRep` / `rightFDRep` 的定义

English:
definition rightFDRep
  signature: [Finite G]
  body: FDRep.of rightRegular

中文:
定义 rightFDRep
  签名: [有限 G]
  定义体: FDRep.of rightRegular

Depends on / 依赖: FDRep.of, rightRegular
-/
def rightFDRep [Finite G] : FDRep k G := FDRep.of rightRegular

end definitions

variable [Finite G]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `equivHom_injective` / 引理 `equivHom_injective`

English:
lemma equivHom_injective
  given: [Nontrivial k]
  statement: Function.Injective (equivHom k G)
  proof: by
  intro s t h
  classical
  apply_fun (fun x => (x.hom.hom.app rightFDRep).hom (single t 1) 1) at h
  simp_all [single_apply]

中文:
引理 equivHom_injective
  条件: [非平凡 k]
  结论: 函数.单射 (equivHom k G)
  证明: by
  intro s t h
  classical
  apply_fun (fun x => (x.hom.hom.app rightFDRep).hom (single t 1) 1) at h
  simp_all [single_apply]

Depends on / 依赖: apply_fun, classical, rightFDRep, single, single_apply, x.hom.hom.app
-/
lemma equivHom_injective [Nontrivial k] : Function.Injective (equivHom k G) := by
  intro s t h
  classical
  apply_fun (fun x => (x.hom.hom.app rightFDRep).hom (single t 1) 1) at h
  simp_all [single_apply]

/--
Definition of `mulRepHom` / `mulRepHom` 的定义

English:
definition mulRepHom
  signature: : rightFDRep (k := k) (G := G) otimes rightFDRep ⟶ rightFDRep where
  body: InducedCategory.homMk (ofHom (LinearMap.mul' k (G -> k)))
  comm := by
    intro
    ext u
    refine TensorProduct.induction_on u rfl (fun _ _ => rfl) (fun _ _ hx hy => ?_)
    simp only [map_add, hx, hy]

中文:
定义 mulRepHom
  签名: : rightFDRep (k := k) (G := G) otimes rightFDRep ⟶ rightFDRep where
  定义体: InducedCategory.homMk (ofHom (LinearMap.mul' k (G -> k)))
  comm := by
    intro
    ext u
    refine TensorProduct.induction_on u rfl (fun _ _ => rfl) (fun _ _ hx hy => ?_)
    simp only [map_add, hx, hy]

Depends on / 依赖: otimes, rightFDRep
-/
def mulRepHom : rightFDRep (k := k) (G := G) otimes rightFDRep ⟶ rightFDRep where
  hom := InducedCategory.homMk (ofHom (LinearMap.mul' k (G -> k)))
  comm := by
    intro
    ext u
    refine TensorProduct.induction_on u rfl (fun _ _ => rfl) (fun _ _ hx hy => ?_)
    simp only [map_add, hx, hy]

/--
lemma `map_mul_toRightFDRepComp` / 引理 `map_mul_toRightFDRepComp`

English:
lemma map_mul_toRightFDRepComp
  given: (η : Aut (forget k G)) (f g : G -> k)
  proof: (η.hom.hom.app rightFDRep).hom.hom
    α (f * g) = (α f) * (α g) := by
  have nat := η.hom.hom.naturality mulRepHom
  have tensor (X Y) : η.hom.hom.app (X otimes Y) = (η.hom.hom.app X otimesₘ η.hom.hom.app Y) :=
    η.hom.isMonoidal.tensor X Y
  rw [tensor] at nat
  exact ConcreteCategory.congr_hom 

中文:
引理 map_mul_toRightFDRepComp
  条件: (η : Aut (forget k G)) (f g : G -> k)
  证明: (η.hom.hom.app rightFDRep).hom.hom
    α (f * g) = (α f) * (α g) := by
  have nat := η.hom.hom.naturality mulRepHom
  have tensor (X Y) : η.hom.hom.app (X otimes Y) = (η.hom.hom.app X otimesₘ η.hom.hom.app Y) :=
    η.hom.isMonoidal.tensor X Y
  rw [tensor] at nat
  exact ConcreteCategory.congr_hom 

Depends on / 依赖: hom.hom, hom.hom.app, rightFDRep
-/
lemma map_mul_toRightFDRepComp (η : Aut (forget k G)) (f g : G -> k) :
    let α : (G -> k) ->ₗ[k] (G -> k) := (η.hom.hom.app rightFDRep).hom.hom
    α (f * g) = (α f) * (α g) := by
  have nat := η.hom.hom.naturality mulRepHom
  have tensor (X Y) : η.hom.hom.app (X otimes Y) = (η.hom.hom.app X otimesₘ η.hom.hom.app Y) :=
    η.hom.isMonoidal.tensor X Y
  rw [tensor] at nat
  exact ConcreteCategory.congr_hom ((CategoryTheory.forget _).congr_map nat) (f otimesₜ[k] g)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `algHomOfRightFDRepComp` / `algHomOfRightFDRepComp` 的定义

English:
definition algHomOfRightFDRepComp
  signature: (η : Aut (forget k G))
  body: by
  let α : (G -> k) ->ₗ[k] (G -> k) := (η.hom.hom.app rightFDRep).hom.hom
  let α_inv : (G -> k) ->ₗ[k] (G -> k) := (η.inv.hom.app rightFDRep).hom.hom
  refine AlgHom.ofLinearMap α ?_ (map_mul_toRightFDRepComp η)
  suffices α (α_inv 1) = (1 : G -> k) by
    have h := this
    rwa [← one_mul (α_inv

中文:
定义 algHomOfRightFDRepComp
  签名: (η : Aut (forget k G))
  定义体: by
  let α : (G -> k) ->ₗ[k] (G -> k) := (η.hom.hom.app rightFDRep).hom.hom
  let α_inv : (G -> k) ->ₗ[k] (G -> k) := (η.inv.hom.app rightFDRep).hom.hom
  refine AlgHom.ofLinearMap α ?_ (map_mul_toRightFDRepComp η)
  suffices α (α_inv 1) = (1 : G -> k) by
    have h := this
    rwa [← one_mul (α_inv

Depends on / 依赖: AlgHom, AlgHom.ofLinearMap, apply_fun, hom.hom, hom.hom.app, inv.hom.app, inv_hom_id, map_mul_toRightFDRepComp, mul_one, ofLinearMap, one_mul, rightFDRep, x.hom.app
-/
def algHomOfRightFDRepComp (η : Aut (forget k G)) : (G -> k) ->ₐ[k] (G -> k) := by
  let α : (G -> k) ->ₗ[k] (G -> k) := (η.hom.hom.app rightFDRep).hom.hom
  let α_inv : (G -> k) ->ₗ[k] (G -> k) := (η.inv.hom.app rightFDRep).hom.hom
  refine AlgHom.ofLinearMap α ?_ (map_mul_toRightFDRepComp η)
  suffices α (α_inv 1) = (1 : G -> k) by
    have h := this
    rwa [← one_mul (α_inv 1), map_mul_toRightFDRepComp, h, mul_one] at this
  have := η.inv_hom_id
  apply_fun (fun x => (x.hom.app rightFDRep).hom (1 : G -> k)) at this
  exact this

/-- For `v : X` and `G` a finite group, the `G`-equivariant linear map from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`. -/
@[simps]
/--
Definition of `sumSMulInv` / `sumSMulInv` 的定义

English:
definition sumSMulInv
  signature: [Fintype G] {X : FDRep k G} (v : X)
  body: ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' _ _ := by simp [add_smul, sum_add_distrib]
  map_smul' _ _ := by simp [smul_sum, smul_smul]

omit [Finite G] in

中文:
定义 sumSMulInv
  签名: [有限类型 G] {X : FDRep k G} (v : X)
  定义体: ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' _ _ := by simp [add_smul, sum_add_distrib]
  map_smul' _ _ := by simp [smul_sum, smul_smul]

omit [Finite G] in
-/
def sumSMulInv [Fintype G] {X : FDRep k G} (v : X) : (G -> k) ->ₗ[k] X where
  toFun f := ∑ s : G, (f s) • (X.ρ s⁻¹ v)
  map_add' _ _ := by simp [add_smul, sum_add_distrib]
  map_smul' _ _ := by simp [smul_sum, smul_smul]

omit [Finite G] in
/--
lemma `sumSMulInv_single_id` / 引理 `sumSMulInv_single_id`

English:
lemma sumSMulInv_single_id
  given: [Fintype G] [DecidableEq G] {X : FDRep k G} (v : X)
  proof: by
  simp

中文:
引理 sumSMulInv_single_id
  条件: [有限类型 G] [DecidableEq G] {X : FDRep k G} (v : X)
  证明: by
  simp
-/
lemma sumSMulInv_single_id [Fintype G] [DecidableEq G] {X : FDRep k G} (v : X) :
    ∑ s : G, (single 1 1 : G -> k) s • (X.ρ s⁻¹) v = v := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- For `v : X` and `G` a finite group, the representation morphism from the right
regular representation `rightFDRep` to `X` sending `single 1 1` to `v`. -/
@[simps]
/--
Definition of `ofRightFDRep` / `ofRightFDRep` 的定义

English:
definition ofRightFDRep
  signature: [Fintype G] (X : FDRep k G) (v : X)
  body: InducedCategory.homMk (ofHom (sumSMulInv v))
  comm t := by
    ext f
    let φ_term (X : FDRep k G) (f : G -> k) v s := (f s) • (X.ρ s⁻¹ v)
    have := sum_map univ (mulRightEmbedding t⁻¹) (φ_term X (rightRegular t f) v)
    simpa [φ_term] using! this

中文:
定义 ofRightFDRep
  签名: [有限类型 G] (X : FDRep k G) (v : X)
  定义体: InducedCategory.homMk (ofHom (sumSMulInv v))
  comm t := by
    ext f
    let φ_term (X : FDRep k G) (f : G -> k) v s := (f s) • (X.ρ s⁻¹ v)
    have := sum_map univ (mulRightEmbedding t⁻¹) (φ_term X (rightRegular t f) v)
    simpa [φ_term] using! this

Depends on / 依赖: InducedCategory, InducedCategory.homMk, sumSMulInv
-/
def ofRightFDRep [Fintype G] (X : FDRep k G) (v : X) : rightFDRep ⟶ X where
  hom := InducedCategory.homMk (ofHom (sumSMulInv v))
  comm t := by
    ext f
    let φ_term (X : FDRep k G) (f : G -> k) v s := (f s) • (X.ρ s⁻¹ v)
    have := sum_map univ (mulRightEmbedding t⁻¹) (φ_term X (rightRegular t f) v)
    simpa [φ_term] using! this

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toRightFDRepComp_injective` / 引理 `toRightFDRepComp_injective`

English:
lemma toRightFDRepComp_injective
  statement: {η₁ η₂ : Aut (forget k G)}
  proof: by
  have := Fintype.ofFinite G
  classical
  ext X v
  have h1 := η₁.hom.hom.naturality (ofRightFDRep X v)
  have h2 := η₂.hom.hom.naturality (ofRightFDRep X v)
  rw [h]; rw [← h2] at h1
  simpa using congr(($h1).hom (single 1 1))

中文:
引理 toRightFDRepComp_injective
  结论: {η₁ η₂ : Aut (forget k G)}
  证明: by
  have := Fintype.ofFinite G
  classical
  ext X v
  have h1 := η₁.hom.hom.naturality (ofRightFDRep X v)
  have h2 := η₂.hom.hom.naturality (ofRightFDRep X v)
  rw [h]; rw [← h2] at h1
  simpa using congr(($h1).hom (single 1 1))

Depends on / 依赖: Fintype, Fintype.ofFinite, classical, hom.hom.naturality, naturality, ofFinite, ofRightFDRep, single
-/
lemma toRightFDRepComp_injective {η₁ η₂ : Aut (forget k G)}
    (h : η₁.hom.hom.app rightFDRep = η₂.hom.hom.app rightFDRep) : η₁ = η₂ := by
  have := Fintype.ofFinite G
  classical
  ext X v
  have h1 := η₁.hom.hom.naturality (ofRightFDRep X v)
  have h2 := η₂.hom.hom.naturality (ofRightFDRep X v)
  rw [h]; rw [← h2] at h1
  simpa using congr(($h1).hom (single 1 1))

/--
Definition of `leftRegularFDRepHom` / `leftRegularFDRepHom` 的定义

English:
definition leftRegularFDRepHom
  signature: (s : G)
  body: InducedCategory.homMk (ofHom (leftRegular s))
  comm _ := by
    ext f
    funext _
    apply congrArg f
    exact mul_assoc ..

中文:
定义 leftRegularFDRepHom
  签名: (s : G)
  定义体: InducedCategory.homMk (ofHom (leftRegular s))
  comm _ := by
    ext f
    funext _
    apply congrArg f
    exact mul_assoc ..

Depends on / 依赖: InducedCategory, InducedCategory.homMk, leftRegular
-/
def leftRegularFDRepHom (s : G) : End (rightFDRep : FDRep k G) where
  hom := InducedCategory.homMk (ofHom (leftRegular s))
  comm _ := by
    ext f
    funext _
    apply congrArg f
    exact mul_assoc ..

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toRightFDRepComp_in_rightRegular` / 引理 `toRightFDRepComp_in_rightRegular`

English:
lemma toRightFDRepComp_in_rightRegular
  given: [IsDomain k] (η : Aut (forget k G))
  proof: by
  classical
  obtain ⟨s, hs⟩ := ((evalAlgHom _ _ 1).comp (algHomOfRightFDRepComp η)).eq_piEvalAlgHom
  refine ⟨s, (basisFun k G).ext fun u => ?_⟩
  simp only [rightFDRep, forget_obj]
  ext t
  have nat := η.hom.hom.naturality (leftRegularFDRepHom t⁻¹)
  calc
    _ = leftRegular t⁻¹ ((η.hom.hom.ap

中文:
引理 toRightFDRepComp_in_rightRegular
  条件: [是整环 k] (η : Aut (forget k G))
  证明: by
  classical
  obtain ⟨s, hs⟩ := ((evalAlgHom _ _ 1).comp (algHomOfRightFDRepComp η)).eq_piEvalAlgHom
  refine ⟨s, (basisFun k G).ext fun u => ?_⟩
  simp only [rightFDRep, forget_obj]
  ext t
  have nat := η.hom.hom.naturality (leftRegularFDRepHom t⁻¹)
  calc
    _ = leftRegular t⁻¹ ((η.hom.hom.ap

Depends on / 依赖: Fact.out, Fintype, Fintype.card_units, HasEnoughRootsOfUnity, HasEnoughRootsOfUnity.of_card_le, MulEquiv, MulEquiv.subgroupCongr, Nat.Prime.two_le, Nat.card_congr, NeZero, ZMod.rootsOfUnity_eq_top, algHomOfRightFDRepComp, basisFun, card_congr, card_units, classical, eq_piEvalAlgHom, evalAlgHom, forget_obj, hom.hom.app
-/
lemma toRightFDRepComp_in_rightRegular [IsDomain k] (η : Aut (forget k G)) :
    exists (s : G), (η.hom.hom.app rightFDRep).hom.hom = rightRegular s := by
  classical
  obtain ⟨s, hs⟩ := ((evalAlgHom _ _ 1).comp (algHomOfRightFDRepComp η)).eq_piEvalAlgHom
  refine ⟨s, (basisFun k G).ext fun u => ?_⟩
  simp only [rightFDRep, forget_obj]
  ext t
  have nat := η.hom.hom.naturality (leftRegularFDRepHom t⁻¹)
  calc
    _ = leftRegular t⁻¹ ((η.hom.hom.app rightFDRep).hom (single u 1)) 1 := by simp
    _ = (η.hom.hom.app rightFDRep).hom (leftRegular t⁻¹ (single u 1)) 1 :=
      congrFun congr(($nat.symm).hom (single u 1)) 1
    _ = evalAlgHom _ _ s (leftRegular t⁻¹ (single u 1)) :=
      congr($hs (leftRegular t⁻¹ (single u 1)))
    _ = _ := by by_cases u = t * s <;> simp_all

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `equivHom_surjective` / 引理 `equivHom_surjective`

English:
lemma equivHom_surjective
  given: [IsDomain k]
  statement: Function.Surjective (equivHom k G)
  proof: by
  intro η
  obtain ⟨s, h⟩ := toRightFDRepComp_in_rightRegular η
  exact ⟨s, toRightFDRepComp_injective (InducedCategory.hom_ext (hom_ext h.symm))⟩

中文:
引理 equivHom_surjective
  条件: [是整环 k]
  结论: 函数.满射 (equivHom k G)
  证明: by
  intro η
  obtain ⟨s, h⟩ := toRightFDRepComp_in_rightRegular η
  exact ⟨s, toRightFDRepComp_injective (InducedCategory.hom_ext (hom_ext h.symm))⟩

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, h.symm, hom_ext, toRightFDRepComp_in_rightRegular, toRightFDRepComp_injective
-/
lemma equivHom_surjective [IsDomain k] : Function.Surjective (equivHom k G) := by
  intro η
  obtain ⟨s, h⟩ := toRightFDRepComp_in_rightRegular η
  exact ⟨s, toRightFDRepComp_injective (InducedCategory.hom_ext (hom_ext h.symm))⟩

variable (k G) in
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: [IsDomain k]
  body: MulEquiv.ofBijective (equivHom k G) ⟨equivHom_injective, equivHom_surjective⟩

中文:
定义 equiv
  签名: [是整环 k]
  定义体: MulEquiv.ofBijective (equivHom k G) ⟨equivHom_injective, equivHom_surjective⟩

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, equivHom, equivHom_injective, equivHom_surjective, ofBijective
-/
def equiv [IsDomain k] : G ≃* Aut (forget k G) :=
  MulEquiv.ofBijective (equivHom k G) ⟨equivHom_injective, equivHom_surjective⟩

end FiniteGroup

end TannakaDuality

end
