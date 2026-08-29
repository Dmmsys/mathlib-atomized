/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Coinduced representations

Given a commutative ring `k`, a monoid homomorphism `φ : G →* H`, and a `k`-linear
`G`-representation `A`, this file introduces the coinduced representation $Coind_G^H(A)$ of `A` as
an `H`-representation.

By `coind φ A` we mean the submodule of functions `H → A` such that for all `g : G`, `h : H`,
`f (φ g * h) = ρ g (f h)`. We define a representation of `H` on this submodule by sending `h : H`
and `f : coind φ A` to the function `H → A` sending `h₁` to `f (h₁ * h)`.

Alternatively, we could define $Coind_G^H(A)$ as the morphisms $Hom(k[H], A)$ in the category
`Rep k G`, which we equip with the `H`-representation sending `h : H` and `f : k[H] ⟶ A` to the
representation morphism sending `r · h₁` to `r • f (h₁ * h)`. We include this definition as
`coind' φ A` and prove the two representations are isomorphic.

We also prove that the restriction functor `Rep k H ⥤ Rep k G` along `φ` is left adjoint to the
coinduction functor and hence that the coinduction functor preserves limits.

## Main definitions

* `Representation.coind φ ρ` : the coinduction of `ρ` along `φ` defined as the `k`-submodule of
  `G`-equivariant functions `H → A`, with `H`-action given by `(h • f) h₁ := f (h₁ * h)` for
  `f : H → A`, `h, h₁ : H`.
* `Representation.coind' φ A` : the coinduction of `A` along `φ` defined as the set of
  `G`-representation morphisms `k[H] ⟶ A`, with `H`-action given by
  `(h • f) (r • h₁) := r • f(h₁ * h)` for `f : k[H] ⟶ A`, `h, h₁ : H`, `r : k`.
* `Rep.resCoindAdjunction k φ`: given a monoid homomorphism `φ : G →* H`, this is the adjunction
  between the restriction functor `Rep k H ⥤ Rep k G` along `φ` and the coinduction functor
  along `φ`.

-/

@[expose] public section

universe t u' u v' v w' w

namespace Representation

variable {k G H : Type*} [Semiring k] [Monoid G] [Monoid H] (φ : G ->* H) {A B : Type*}
  [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B] (σ : Representation k G A)
  (ρ : Representation k G B)

/--
If `ρ : Representation k G A` and `φ : G →* H` then `coindV φ ρ` is the sub-`k`-module of
functions `H → A` underlying the coinduction of `ρ` along `φ`, i.e., the functions `f : H → A`
such that `f (φ g * h) = (ρ g) (f h)` for all `g : G` and `h : H`.
-/
@[simps]
/--
Definition of `coindV` / `coindV` 的定义

English:
definition coindV
  signature: : Submodule k (H -> A) where
  body: {f : H -> A | forall (g : G) (h : H), f (φ g * h) = σ g (f h) }
  add_mem' _ _ _ _ := by simp_all
  zero_mem' := by simp
  smul_mem' _ _ _ := by simp_all

@[simp]

中文:
定义 coindV
  签名: : 子模 k (H -> A) where
  定义体: {f : H -> A | forall (g : G) (h : H), f (φ g * h) = σ g (f h) }
  add_mem' _ _ _ _ := by simp_all
  zero_mem' := by simp
  smul_mem' _ _ _ := by simp_all

@[simp]
-/
def coindV : Submodule k (H -> A) where
  carrier := {f : H -> A | forall (g : G) (h : H), f (φ g * h) = σ g (f h) }
  add_mem' _ _ _ _ := by simp_all
  zero_mem' := by simp
  smul_mem' _ _ _ := by simp_all

@[simp]
/--
lemma `mem_coindV` / 引理 `mem_coindV`

English:
lemma mem_coindV
  given: (f : H -> A)
  statement: f in coindV φ σ ↔ forall (g : G) (h : H), f (φ g * h) = σ g (f h)
  proof: Iff.rfl

中文:
引理 mem_coindV
  条件: (f : H -> A)
  结论: f in coindV φ σ ↔ 对任意 (g : G) (h : H), f (φ g * h) = σ g (f h)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_coindV (f : H -> A) : f in coindV φ σ ↔ forall (g : G) (h : H), f (φ g * h) = σ g (f h) :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
If `ρ : Representation k G A` and `φ : G →* H` then `coind φ ρ` is the representation
coinduced by `ρ` along `φ`, defined as the following action of `H` on the submodule `coindV φ ρ`
of `G`-equivariant functions from `H` to `A`: we let `h : H` send the function `f : H → A`
to the function sending `h₁` to `f (h₁ * h)`.

See also `Rep.coind` and `Representation.coind'` for variants involving the category `Rep k G`.
-/
@[simps]
/--
Definition of `coind` / `coind` 的定义

English:
definition coind
  signature: : Representation k H (coindV φ ρ) where
  body: (LinearMap.funLeft _ _ (· * h)).restrict fun x hx g h₁ => by
    simpa [mul_assoc] using hx g (h₁ * h)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

中文:
定义 coind
  签名: : Representation k H (coindV φ ρ) where
  定义体: (LinearMap.funLeft _ _ (· * h)).restrict fun x hx g h₁ => by
    simpa [mul_assoc] using hx g (h₁ * h)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

Depends on / 依赖: LinearMap, LinearMap.funLeft, funLeft, map_mul, map_one, mul_assoc, restrict
-/
def coind : Representation k H (coindV φ ρ) where
  toFun h := (LinearMap.funLeft _ _ (· * h)).restrict fun x hx g h₁ => by
    simpa [mul_assoc] using hx g (h₁ * h)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

set_option backward.isDefEq.respectTransparency.types false in
variable {σ ρ} in
/--
Definition of `coindMap` / `coindMap` 的定义

English:
definition coindMap
  signature: (f : σ.IntertwiningMap ρ)
  body: (f.toLinearMap.compLeft H).restrict fun x h => by
    simp only [mem_coindV, LinearMap.compLeft_apply, Function.comp_apply,
      IntertwiningMap.toLinearMap_apply] at h ⊢
    intro g h0
    simpa [h] using LinearMap.ext_iff.1 (f.2 g) (x h0)
  isIntertwining' h := by ext; simp

中文:
定义 coindMap
  签名: (f : σ.整数ertwining映射 ρ)
  定义体: (f.toLinearMap.compLeft H).restrict fun x h => by
    simp only [mem_coindV, LinearMap.compLeft_apply, Function.comp_apply,
      IntertwiningMap.toLinearMap_apply] at h ⊢
    intro g h0
    simpa [h] using LinearMap.ext_iff.1 (f.2 g) (x h0)
  isIntertwining' h := by ext; simp

Depends on / 依赖: Function, Function.comp_apply, IntertwiningMap, IntertwiningMap.toLinearMap_apply, LinearMap, LinearMap.compLeft_apply, LinearMap.ext_iff, compLeft, compLeft_apply, comp_apply, ext_iff, f.toLinearMap.compLeft, isIntertwining, mem_coindV, restrict, toLinearMap, toLinearMap_apply
-/
def coindMap (f : σ.IntertwiningMap ρ) : (coind φ σ).IntertwiningMap (coind φ ρ) where
  __ : _ ->ₗ[k] _ := (f.toLinearMap.compLeft H).restrict fun x h => by
    simp only [mem_coindV, LinearMap.compLeft_apply, Function.comp_apply,
      IntertwiningMap.toLinearMap_apply] at h ⊢
    intro g h0
    simpa [h] using LinearMap.ext_iff.1 (f.2 g) (x h0)
  isIntertwining' h := by ext; simp

/--
lemma `coindMap_coe_apply` / 引理 `coindMap_coe_apply`

English:
lemma coindMap_coe_apply
  given: (f : σ.IntertwiningMap ρ) (x : coindV φ σ)
  proof: rfl

@[simp]

中文:
引理 coindMap_coe_apply
  条件: (f : σ.整数ertwining映射 ρ) (x : coindV φ σ)
  证明: rfl

@[simp]
-/
lemma coindMap_coe_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) :
    (coindMap φ f) x = (f.toLinearMap.compLeft H) x := rfl

@[simp]
/--
lemma `coindMap_coe_apply_apply` / 引理 `coindMap_coe_apply_apply`

English:
lemma coindMap_coe_apply_apply
  given: (f : σ.IntertwiningMap ρ) (x : coindV φ σ) (h : H)
  proof: rfl

中文:
引理 coindMap_coe_apply_apply
  条件: (f : σ.整数ertwining映射 ρ) (x : coindV φ σ) (h : H)
  证明: rfl
-/
lemma coindMap_coe_apply_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) (h : H) :
    ((coindMap φ f) x).1 h = f (x.1 h) := rfl

end Representation

namespace Rep

open CategoryTheory Finsupp

variable {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Monoid G] [Monoid H]
  (φ : G ->* H) (A : Rep k G)

section Coind

/--
Definition of `coind` / `coind` 的定义

English:
abbreviation coind
  signature: : Rep k H
  body: Rep.of (Representation.coind φ A.ρ)

中文:
缩写 coind
  签名: : Rep k H
  定义体: Rep.of (Representation.coind φ A.ρ)

Depends on / 依赖: Rep.of, Representation, Representation.coind
-/
noncomputable abbrev coind : Rep k H := Rep.of (Representation.coind φ A.ρ)

/--
Definition of `coindMap` / `coindMap` 的定义

English:
abbreviation coindMap
  signature: {A B : Rep k G} (f : A ⟶ B)
  body: ofHom Representation.coindMap φ f.hom

中文:
缩写 coindMap
  签名: {A B : Rep k G} (f : A ⟶ B)
  定义体: ofHom Representation.coindMap φ f.hom

Depends on / 依赖: I.mul_mem_right, Representation, Representation.coindMap, coindMap, f.hom, mul_mem_right
-/
noncomputable abbrev coindMap {A B : Rep k G} (f : A ⟶ B) : coind φ A ⟶ coind φ B :=
ofHom Representation.coindMap φ f.hom

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind φ A`, with action on maps given by postcomposition. -/
@[implicit_reducible, simps obj map]
/--
Definition of `coindFunctor` / `coindFunctor` 的定义

English:
definition coindFunctor
  signature: : Rep.{t} k G ⥤ Rep k H where
  body: coind φ A
  map f := coindMap φ f

中文:
定义 coindFunctor
  签名: : Rep.{t} k G ⥤ Rep k H where
  定义体: coind φ A
  map f := coindMap φ f
-/
noncomputable def coindFunctor : Rep.{t} k G ⥤ Rep k H where
  obj A := coind φ A
  map f := coindMap φ f

instance {G : Type v'} [Group G] (S : Subgroup G) :
    (coindFunctor k S.subtype).PreservesEpimorphisms where
  preserves {X Y} f := (epi_iff_surjective _).2 fun y => by
    let := QuotientGroup.rightRel S
    choose! s hs using (Rep.epi_iff_surjective f).1 ‹_›
    choose! i hi using Quotient.mk'_surjective (α := G)
    let γ (g : G) : S := ⟨g * (i (Quotient.mk' g))⁻¹,
      (QuotientGroup.rightRel_apply.1 (Quotient.eq'.1 (hi (Quotient.mk' g))))⟩
    have hmk (s : S) (g : G) : Quotient.mk' (s.1 * g) = Quotient.mk' g :=
      Quotient.eq'.2 (QuotientGroup.rightRel_apply.2 (by simp))
    have hγ (s : S) (g : G) : γ (s.1 * g) = s * γ g := by ext; simp [mul_assoc, γ, hmk]
    let x (g : G) : X := X.ρ (γ g) (s (y.1 (i (Quotient.mk' g))))
refine ⟨⟨x, fun _ _ => ?_⟩, Subtype.ext funext fun g => ?_⟩
    · simp [x, ← Module.End.mul_apply, ← map_mul, hmk, hγ]
    · simp only [coindFunctor_obj, coindFunctor_map, hom_ofHom,
        Representation.coindMap_coe_apply_apply, hom_comm_apply, x]
      simp_all [← y.2 (γ g), γ]

end Coind
section Coind'

set_option backward.isDefEq.respectTransparency.types false in
/--
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` along `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-equivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
-/
@[simps]
/--
Definition of `_root_.Representation.coind'` / `_root_.Representation.coind'` 的定义

English:
definition _root_.Representation.coind'
  signature: :
  body: { toFun f := (resFunctor φ).map ((leftRegularHomEquiv (leftRegular k H)).symm.toLinearMap
      (.single h 1)) ≫ f
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp [homEquiv]
  map_mul' _ _ := by
    ext
    simp [homEquiv, mul_assoc]

中文:
定义 _root_.Representation.coind'
  签名: :
  定义体: { toFun f := (resFunctor φ).map ((leftRegularHomEquiv (leftRegular k H)).symm.toLinearMap
      (.single h 1)) ≫ f
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp [homEquiv]
  map_mul' _ _ := by
    ext
    simp [homEquiv, mul_assoc]

Depends on / 依赖: homEquiv, leftRegular, leftRegularHomEquiv, map_add, map_mul, map_one, map_smul, mul_assoc, resFunctor, single, symm.toLinearMap, toLinearMap
-/
noncomputable def _root_.Representation.coind' :
    Representation k H (res φ (leftRegular k H) ⟶ A) where
  toFun h :=
  { toFun f := (resFunctor φ).map ((leftRegularHomEquiv (leftRegular k H)).symm.toLinearMap
      (.single h 1)) ≫ f
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext
    simp [homEquiv]
  map_mul' _ _ := by
    ext
    simp [homEquiv, mul_assoc]

/--
Definition of `coind'` / `coind'` 的定义

English:
abbreviation coind'
  signature: : Rep k H
  body: Rep.of (Representation.coind' φ A)

中文:
缩写 coind'
  签名: : Rep k H
  定义体: Rep.of (Representation.coind' φ A)

Depends on / 依赖: Rep.of, Representation, Representation.coind
-/
noncomputable abbrev coind' : Rep k H := Rep.of (Representation.coind' φ A)

variable {A} in
@[ext]
/--
lemma `coind'_ext` / 引理 `coind'_ext`

English:
lemma coind'_ext
  statement: {f g : coind' φ A} (hfg : forall h, f.hom.toLinearMap (.single h 1) =
  proof: Rep.hom_ext by ext1; dsimp; ext h; simpa using hfg h

中文:
引理 coind'_ext
  结论: {f g : coind' φ A} (hfg : 对任意 h, f.hom.toLinearMap (.single h 1) =
  证明: Rep.hom_ext by ext1; dsimp; ext h; simpa using hfg h
-/
lemma coind'_ext {f g : coind' φ A} (hfg : forall h, f.hom.toLinearMap (.single h 1) =
    g.hom.toLinearMap (.single h 1)) : f = g :=
Rep.hom_ext by ext1; dsimp; ext h; simpa using hfg h

/--
Definition of `coindMap'` / `coindMap'` 的定义

English:
definition coindMap'
  signature: {A B : Rep k G} (f : A ⟶ B)
  body: Rep.ofHom
  { __ := Linear.rightComp k _ f
    isIntertwining' h := by ext; simp }

中文:
定义 coindMap'
  签名: {A B : Rep k G} (f : A ⟶ B)
  定义体: Rep.ofHom
  { __ := Linear.rightComp k _ f
    isIntertwining' h := by ext; simp }

Depends on / 依赖: Rep.ofHom
-/
noncomputable def coindMap' {A B : Rep k G} (f : A ⟶ B) : coind' φ A ⟶ coind' φ B := Rep.ofHom
  { __ := Linear.rightComp k _ f
    isIntertwining' h := by ext; simp }

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind' φ A`, with action on maps given by postcomposition. -/
@[implicit_reducible, simps obj map]
/--
Definition of `coindFunctor'` / `coindFunctor'` 的定义

English:
definition coindFunctor'
  signature: : Rep k G ⥤ Rep k H where
  body: coind' φ A
  map f := coindMap' φ f

中文:
定义 coindFunctor'
  签名: : Rep k G ⥤ Rep k H where
  定义体: coind' φ A
  map f := coindMap' φ f
-/
noncomputable def coindFunctor' : Rep k G ⥤ Rep k H where
  obj A := coind' φ A
  map f := coindMap' φ f

end Coind'
noncomputable section CoindIso

/-- If `φ : G →* H` and `A : Rep k G` then the `k`-submodule of functions `f : H → A`
such that for all `g : G`, `h : H`, `f (φ g * h) = A.ρ g (f h)`, is `k`-linearly equivalent
to the `G`-representation morphisms `k[H] ⟶ A`. -/
@[simps]
/--
Definition of `coindVEquiv` / `coindVEquiv` 的定义

English:
definition coindVEquiv
  signature: :
  body: Rep.ofHom ⟨linearCombination _ f.1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g => by dsimp; ext; simp [f.2 g]⟩
map_add' _ _ := coind'_ext φ by simp [Rep.add_hom]
map_smul' _ _ := coind'_ext φ by simp [smul_hom]
  invFun f := ⟨fun h => f.hom.toLinearMap (.single h 1), fun g h => by
    simp only [res_obj_V, res_obj_ρ, Representation.IntertwiningMap.toLinearMap_apply]
    have := by simpa using (hom_comm_apply f g (.single h 1)).symm
    rw [← this]⟩
  left_inv x := by simp
  right_inv x := coind'_ext φ fun _ => by simp

中文:
定义 coindVEquiv
  签名: :
  定义体: Rep.ofHom ⟨linearCombination _ f.1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g => by dsimp; ext; simp [f.2 g]⟩
map_add' _ _ := coind'_ext φ by simp [Rep.add_hom]
map_smul' _ _ := coind'_ext φ by simp [smul_hom]
  invFun f := ⟨fun h => f.hom.toLinearMap (.single h 1), fun g h => by
    simp only [res_obj_V, res_obj_ρ, Representation.IntertwiningMap.toLinearMap_apply]
    have := by simpa using (hom_comm_apply f g (.single h 1)).symm
    rw [← this]⟩
  left_inv x := by simp
  right_inv x := coind'_ext φ fun _ => by simp

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, Rep.ofHom, coeffLinearEquiv, linearCombination, toLinearMap
-/
noncomputable def coindVEquiv :
    A.ρ.coindV φ ≃ₗ[k] (res φ (leftRegular k H) ⟶ A) where
  toFun f := Rep.ofHom ⟨linearCombination _ f.1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).toLinearMap,
    fun g => by dsimp; ext; simp [f.2 g]⟩
map_add' _ _ := coind'_ext φ by simp [Rep.add_hom]
map_smul' _ _ := coind'_ext φ by simp [smul_hom]
  invFun f := ⟨fun h => f.hom.toLinearMap (.single h 1), fun g h => by
    simp only [res_obj_V, res_obj_ρ, Representation.IntertwiningMap.toLinearMap_apply]
    have := by simpa using (hom_comm_apply f g (.single h 1)).symm
    rw [← this]⟩
  left_inv x := by simp
  right_inv x := coind'_ext φ fun _ => by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `coindIso` / `coindIso` 的定义

English:
definition coindIso
  signature: : coind φ A ≅ coind' φ A
  body: Rep.mkIso .mk (coindVEquiv φ A) fun h => by ext; simp [homEquiv]

中文:
定义 coindIso
  签名: : coind φ A ≅ coind' φ A
  定义体: Rep.mkIso .mk (coindVEquiv φ A) fun h => by ext; simp [homEquiv]

Depends on / 依赖: Rep.mkIso, coindVEquiv, homEquiv
-/
noncomputable def coindIso : coind φ A ≅ coind' φ A :=
Rep.mkIso .mk (coindVEquiv φ A) fun h => by ext; simp [homEquiv]

/-- Given a monoid homomorphism `φ : G →* H`, the coinduction functors `Rep k G ⥤ Rep k H` given by
`coindFunctor k φ` and `coindFunctor' k φ` are naturally isomorphic, with isomorphism on objects
given by `coindIso φ`. -/
@[simps!]
/--
Definition of `coindFunctorIso` / `coindFunctorIso` 的定义

English:
definition coindFunctorIso
  signature: : coindFunctor k φ ≅ coindFunctor' k φ
  body: NatIso.ofComponents (coindIso φ) fun _ => by
    ext
    exact coind'_ext _ fun _ => by simp [coindIso, coindMap']

中文:
定义 coindFunctorIso
  签名: : coindFunctor k φ ≅ coindFunctor' k φ
  定义体: NatIso.ofComponents (coindIso φ) fun _ => by
    ext
    exact coind'_ext _ fun _ => by simp [coindIso, coindMap']

Depends on / 依赖: NatIso, NatIso.ofComponents, _ext, coindIso, coindMap, ofComponents
-/
noncomputable def coindFunctorIso : coindFunctor k φ ≅ coindFunctor' k φ :=
  NatIso.ofComponents (coindIso φ) fun _ => by
    ext
    exact coind'_ext _ fun _ => by simp [coindIso, coindMap']

end CoindIso

noncomputable section Adjunction

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `resCoindToHom` / `resCoindToHom` 的定义

English:
definition resCoindToHom
  signature: (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A)
  body: Rep.ofHom ⟨(LinearMap.pi fun h => f.hom.toLinearMap ∘ₗ
    Rep.ρ B h).codRestrict _ fun _ _ _ => by simpa using hom_comm_apply f _ _, fun g => by
    dsimp; ext; simp⟩

@[simp]

中文:
定义 resCoindToHom
  签名: (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A)
  定义体: Rep.ofHom ⟨(LinearMap.pi fun h => f.hom.toLinearMap ∘ₗ
    Rep.ρ B h).codRestrict _ fun _ _ _ => by simpa using hom_comm_apply f _ _, fun g => by
    dsimp; ext; simp⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.pi, Rep.ofHom, codRestrict, f.hom.toLinearMap, hom_comm_apply, toLinearMap
-/
def resCoindToHom (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) : B ⟶ (coind φ A) :=
  Rep.ofHom ⟨(LinearMap.pi fun h => f.hom.toLinearMap ∘ₗ
    Rep.ρ B h).codRestrict _ fun _ _ _ => by simpa using hom_comm_apply f _ _, fun g => by
    dsimp; ext; simp⟩

@[simp]
/--
lemma `resCoindToHom_hom_apply_coe` / 引理 `resCoindToHom_hom_apply_coe`

English:
lemma resCoindToHom_hom_apply_coe
  statement: (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) (c : ↑B.V)
  proof: rfl

中文:
引理 resCoindToHom_hom_apply_coe
  结论: (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) (c : ↑B.V)
  证明: rfl

Depends on / 依赖: no_index, resCoindToHom
-/
lemma resCoindToHom_hom_apply_coe (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) (c : ↑B.V)
    (i : H) : (DFunLike.coe (F := no_index (_)) (resCoindToHom φ B A f).hom c).1 i =
    (Hom.hom f) ((B.ρ i) c) := rfl

-- this `no_index` is to prevent simp discrimination tree from acting weird, i.e before
-- adding it the discrimination tree looks like: _.1 (@DFunLike.coe
-- (@Representation.IntertwiningMap _ _ _.1 (@Rep.mk✝ ..).1 ..)) which is bad because `Rep.mk` is
-- private and should never be used.

/--
info: _.1 (@DFunLike.coe _ _.1 _ _ (@ConcreteCategory.hom (Rep _ _ _ _) _ _ _ _ _ _ _ (@resCoindToHom _ _ _ _ _ _ _ _ _ _)) _)
-/
#guard_msgs in
#discr_tree_simp_key resCoindToHom_hom_apply_coe

attribute [pp_with_univ] Rep coind

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a monoid homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-representation
`A`, there is a `k`-linear equivalence between the `G`-representation morphisms `res φ B ⟶ A` and
the `H`-representation morphisms `B ⟶ coind φ A`.

Note `Rep.resCoindHomEquiv.{t, u, v, w}` has the property that
even with all inputs explicitly given, the first universe cannot be synthesized.
-/
@[simps, pp_with_univ]
/--
Definition of `resCoindHomEquiv` / `resCoindHomEquiv` 的定义

English:
definition resCoindHomEquiv
  signature: (B : Rep.{max w t} k H) (A : Rep.{max w t} k G)
  body: resCoindToHom φ B A f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨LinearMap.proj 1 ∘ₗ (A.ρ.coindV φ).subtype ∘ₗ f.hom.toLinearMap,
    fun g => by
      ext x
      have := ((f.hom x).2 g 1).symm
      have := hom_comm_apply f (φ g) x
      simp_all⟩
  left_inv x := by ext; simp
  right_inv z := by ext; simp [resCoindToHom, hom_comm_apply z]

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `@[simps! counit_app_hom_hom unit_app_hom_hom]`,
but removing it seems to be harmless. -/

中文:
定义 resCoindHomEquiv
  签名: (B : Rep.{最大值 w t} k H) (A : Rep.{最大值 w t} k G)
  定义体: resCoindToHom φ B A f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨LinearMap.proj 1 ∘ₗ (A.ρ.coindV φ).subtype ∘ₗ f.hom.toLinearMap,
    fun g => by
      ext x
      have := ((f.hom x).2 g 1).symm
      have := hom_comm_apply f (φ g) x
      simp_all⟩
  left_inv x := by ext; simp
  right_inv z := by ext; simp [resCoindToHom, hom_comm_apply z]

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `@[simps! counit_app_hom_hom unit_app_hom_hom]`,
but removing it seems to be harmless. -/

Depends on / 依赖: resCoindToHom
-/
def resCoindHomEquiv (B : Rep.{max w t} k H) (A : Rep.{max w t} k G) :
    (res φ B ⟶ A) ≃ₗ[k] (B ⟶ coind φ A) where
  toFun f := resCoindToHom φ B A f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨LinearMap.proj 1 ∘ₗ (A.ρ.coindV φ).subtype ∘ₗ f.hom.toLinearMap,
    fun g => by
      ext x
      have := ((f.hom x).2 g 1).symm
      have := hom_comm_apply f (φ g) x
      simp_all⟩
  left_inv x := by ext; simp
  right_inv z := by ext; simp [resCoindToHom, hom_comm_apply z]

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `@[simps! counit_app_hom_hom unit_app_hom_hom]`,
but removing it seems to be harmless. -/
variable (k) in
/--
Definition of `resCoindAdjunction` / `resCoindAdjunction` 的定义

English:
abbreviation resCoindAdjunction
  signature: : resFunctor.{max w t} φ ⊣ coindFunctor k φ
  body: Adjunction.mkOfHomEquiv {
    homEquiv X Y := (resCoindHomEquiv φ X Y).toEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl }

中文:
缩写 resCoindAdjunction
  签名: : resFunctor.{最大值 w t} φ ⊣ coindFunctor k φ
  定义体: Adjunction.mkOfHomEquiv {
    homEquiv X Y := (resCoindHomEquiv φ X Y).toEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, intros, mkOfHomEquiv, resCoindHomEquiv, toEquiv
-/
noncomputable abbrev resCoindAdjunction : resFunctor.{max w t} φ ⊣ coindFunctor k φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := (resCoindHomEquiv φ X Y).toEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (coindFunctor.{max w t} k φ).IsRightAdjoint
  body: (resCoindAdjunction k φ).isRightAdjoint

中文:
实例 :
  签名: (coindFunctor.{最大值 w t} k φ).是右伴随
  定义体: (resCoindAdjunction k φ).isRightAdjoint

Depends on / 依赖: isRightAdjoint, resCoindAdjunction
-/
noncomputable instance : (coindFunctor.{max w t} k φ).IsRightAdjoint :=
  (resCoindAdjunction k φ).isRightAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (resFunctor.{max w t} (k := k) φ).IsLeftAdjoint
  body: (resCoindAdjunction k φ).isLeftAdjoint

中文:
实例 :
  签名: (resFunctor.{最大值 w t} (k := k) φ).是左伴随
  定义体: (resCoindAdjunction k φ).isLeftAdjoint

Depends on / 依赖: IsLeftAdjoint
-/
noncomputable instance : (resFunctor.{max w t} (k := k) φ).IsLeftAdjoint :=
  (resCoindAdjunction k φ).isLeftAdjoint

instance {G : Type w} [Group G] (S : Subgroup G) :
    (resFunctor.{max w t} (k := k) S.subtype).PreservesProjectiveObjects :=
  (resFunctor S.subtype).preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (resCoindAdjunction k S.subtype)

end Adjunction
end Rep
